// Testcase name : ai_core_base_test
// Description    : Base test for all of the ai core non-ral realted tests

`ifndef GUARD_AI_CORE_BASE_TEST_SV
`define GUARD_AI_CORE_BASE_TEST_SV
// AI_CORE base test class
class ai_core_base_test extends uvm_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(ai_core_base_test)

  /** Instance of the environment */
  ai_core_env env;
   /** Construct the report catcher extended class*/
  //ai_core_demoter demote_catcher = new();
  /** Instance of the environment configuration */
  ai_core_top_env_cfg m_env_cfg;


  uvm_sw_ipc m_uvm_sw_ipc_aicore;
  function void uvm_sw_ipc_gen_event(int event_idx);
    m_uvm_sw_ipc_aicore.uvm_sw_ipc_gen_event(event_idx);
  endfunction

  task uvm_sw_ipc_wait_event(int event_idx);
    m_uvm_sw_ipc_aicore.uvm_sw_ipc_wait_event(event_idx);
  endtask

  function void uvm_sw_ipc_push_data(input int fifo_idx, input bit [63:0] data);
    m_uvm_sw_ipc_aicore.uvm_sw_ipc_push_data(fifo_idx, data);
  endfunction

  function bit uvm_sw_ipc_pull_data(input int fifo_idx, output bit [63:0] data);
    return m_uvm_sw_ipc_aicore.uvm_sw_ipc_pull_data(fifo_idx, data);
  endfunction



  /** Customized configuration */
  cust_svt_axi_system_configuration cfg;
  cust_aicore_svt_apb_system_configuration apb_cfg;
  uvm_status_e status;
  ai_core_top_axi_simple_reset_sequence axi_reset_seq;
  apb_master_directed_sequence apb_dir_seq;
  bit [39:0] axi_write_addr;
  bit [31:0] axi_write_data;
  bit [63:0] ai_core_top_read_value;
  bit wait_for_response_for_read = 1;
  virtual ai_core_top_if tb_cfg_if;


  /** Class Constructor */
  function new(string name = "ai_core_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /**
   * Build Phase
   */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    /** Add uvm_report_cb callback */
  //  uvm_report_cb::add(null, demote_catcher);

    /** Factory override of the master transaction object */
    set_type_override_by_type(svt_axi_master_transaction::get_type(),
                              ai_core_top_cust_svt_axi_master_transaction::get_type());

    // Loading configuration
    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_LOW)
    /** Create the configuration object */
    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
    apb_cfg = cust_aicore_svt_apb_system_configuration::type_id::create("apb_cfg");

    /** Set configuration in environment */
    uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env.m_axi_system_env", "cfg", this.cfg);
    uvm_config_db#(cust_aicore_svt_apb_system_configuration)::set(this, "env.m_apb_system_env", "cfg", this.apb_cfg);
    /** Create the configuration object for AI Core environment */
    m_env_cfg = ai_core_top_env_cfg::type_id::create("m_env_cfg");


    /** Set configuration for AI Core environment */
    uvm_config_db#(ai_core_top_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);
    uvm_config_db#(ai_core_top_env_cfg)::set(null, "*", "AI_CORE_TOP_CFG", m_env_cfg);

    /** Create the environment */
    env = ai_core_env::type_id::create("env", this);

    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.m_axi_system_env.slave[0].sequencer.run_phase", "default_sequence", ai_core_top_axi_slave_mem_response_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.m_axi_system_env.slave[1].sequencer.run_phase", "default_sequence", ai_core_top_axi_slave_mem_response_sequence::type_id::get());
    uvm_top.set_timeout(500us, 1);
    axi_reset_seq = ai_core_top_axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    apb_dir_seq = apb_master_directed_sequence::type_id::create("apb_dir_seq");
    uvm_config_db#(virtual ai_core_top_if)::get(uvm_root::get(), "", "tb_cfg_if", tb_cfg_if);

    m_uvm_sw_ipc_aicore = uvm_sw_ipc::type_id::create("m_uvm_sw_ipc_aicore", this);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase


  // Start of simulation phase
  function void start_of_simulation_phase(uvm_phase phase);
    uvm_config_db#(ai_core_env)::set(null, "*", "AI_CORE_ENV", env);
    uvm_config_db#(aic_ls_env)::set(null,"*", "AIC_LS_ENV", env.m_ls_env);
  endfunction : start_of_simulation_phase

  virtual task post_reset_phase(uvm_phase phase);
    super.post_reset_phase(phase);
    `uvm_info(get_name(), "post_reset_phase() started.", UVM_LOW)
    phase.raise_objection(this);

    wait (tb_cfg_if.apb_rst == 0);
    repeat(3) @(posedge tb_cfg_if.ref_clk); // Make sure reset is synchronized
    `uvm_info(get_name(), "Out of reset", UVM_LOW)

    // first set the reset address:
    apb_dir_seq.cfg_addr        = 'h200; // TODO: Roswin to properly use regmod / apb adapter
    apb_dir_seq.cfg_data        = 'h14000000; //AICORE0_SPM
      // Start the sequence on the respective sequencer
    apb_dir_seq.start(env.m_apb_system_env.master.sequencer);


    // only after setting reset address the reset can be removed:
    apb_dir_seq.cfg_addr        = 'h0000; // pctl_ao_csr_reg_ppmu_reset_control
    apb_dir_seq.cfg_data        = 'h1;
     // Start the sequence on the respective sequencer
    apb_dir_seq.start(env.m_apb_system_env.master.sequencer);

     `uvm_info(get_name(), "post_reset_phase() ended.", UVM_LOW)
    phase.drop_objection(this);
  endtask

   //Configure phase
  virtual task configure_phase(uvm_phase phase);
   phase.raise_objection(this);
    #500ns; //Every write should wait till the aicore rst is lifted
    //Enable clock to cva6v
    env.m_ral.write_reg (INFRA_PERIPH_REGMOD, 'h1, "cva6_clk_en");
   phase.drop_objection(this);
  endtask : configure_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    uvm_top.print_topology();
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction : end_of_elaboration_phase

  //TODO change this once the normal test case sequences are present
  virtual task run_phase(uvm_phase phase);
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    if(m_env_cfg.uvm_sw_ipc_handle_end_of_test == 0) begin
      phase.raise_objection(this);
    end
     #100ns;
    if(m_env_cfg.uvm_sw_ipc_handle_end_of_test == 0) begin
      phase.drop_objection(this);
    end
    `uvm_info("run_phase", "Exiting...", UVM_LOW)
  endtask: run_phase

  //axi wr rd tasks
  virtual task axi_write_txn(input bit [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr, input [`AXI_LP_DATA_WIDTH-1:0] axi_write_data, input wait_for_response_for_write);
     axi_master_write_sequence                    axi_wr_seq;
     axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
     axi_wr_seq.randomize() with {
         cfg_addr        == axi_write_addr;
         sequence_length == 'd1;
         burst_size_enum_t == BURST_SIZE_64BIT;
         burst_type_enum_t == INCR;
         burst_lenght_enum_t == BURST_LENGTH_1;
         cfg_data[0] == axi_write_data;
         wait_for_response_for_write == local::wait_for_response_for_write;
       };
       // Start the sequence on the respective sequencer
       axi_wr_seq.start(env.m_axi_system_env.master[0].sequencer); //master 1 -> risv ai core
  endtask:axi_write_txn

  virtual task axi_read_txn(input [`AXI_LP_ADDR_WIDTH-1:0] axi_write_addr,input wait_for_response_for_read);
       axi_master_read_sequence                     axi_rd_seq;
       axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
          axi_rd_seq.randomize() with {
         cfg_addr        == axi_write_addr;
         sequence_length == 'd1;
         burst_size_enum_t == BURST_SIZE_64BIT;
         burst_type_enum_t == INCR;
         burst_lenght_enum_t == BURST_LENGTH_1;
         wait_for_response_for_read == local::wait_for_response_for_read;
       };
       axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer); //master 1 -> risv ai core
  endtask:axi_read_txn

endclass

`endif  // GUARD_AI_CORE_BASE_TEST_SV
