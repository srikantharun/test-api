`ifndef GUARD_AI_CORE_MVM_BASE_TEST_SV
`define GUARD_AI_CORE_MVM_BASE_TEST_SV
// AI CORE MVM base test class
class ai_core_mvm_base_test extends uvm_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(ai_core_mvm_base_test)
   // Declare p sequencer
  // `uvm_declare_p_sequencer(axi_virtual_sequencer)
  // AI Core MVM RAL Modl
  MVM_RAL mvm_regmodel;

  /** Construct the report catcher extended class*/
  ai_core_mvm_demoter catcher = new();

  /** Instance of the environment */
  ai_core_mvm_env env;

  /** Instance of the environment configuration */
  ai_core_mvm_env_cfg m_env_cfg;

  /** Load through configCreator and load_prop_val */
  /** Required to set to 1 if load vip configurations through configCreator gui */
  bit load_through_config_creator = 0;

  /** Customized configuration */
  cust_svt_axi_system_configuration cfg;

  /** Customized configCreator configuration handle */
  //cust_svt_axi_system_cc_configuration cc_cfg;
  uvm_status_e  status;
  // Semaphore
  semaphore key, key_for_lp_interface, key_for_ifdw, key_for_ifd0;
  bit [AXI_LT_DATA_WIDTH-1:0]    ral_write_data;
  bit [AXI_LT_DATA_WIDTH-1:0]    ral_read_data;
  bit [AXI_LT_DATA_WIDTH-1:0]    ral_read_prg_status;
  bit [AXI_LT_DATA_WIDTH-1:0]    ral_read_exe_status;
  bit [AXI_LT_ADDR_WIDTH-1:0]    axi_write_addr;
  bit [AXI_LT_DATA_WIDTH-1:0]    axi_write_data;
  bit [AXI_LT_ADDR_WIDTH-1:0]    axi_read_addr;
  bit [AXI_LT_DATA_WIDTH-1:0]    axi_read_data;
  bit [AXI_LT_ADDR_WIDTH-1:0]    wr_addr,rd_addr;
  bit [AXI_LT_DATA_WIDTH-1:0]    wr_data, rd_data;
  bit [ROW_OFF-1:0]              row_off;
  bit [COL_OFF-1:0]              col_off;
  bit [MATRIX_LEN-1:0]           col_len,row_len;
  bit [WT_SET-1:0]               weight_set;
  bit [LOOP_LEN-1:0]             loop_len;
  bit [LOOP_ITER-1:0]            loop_iter;
  int row_len_intr, col_len_intr, row_off_intr, col_off_intr, weight_set_intr,extra;
  int block_counter;
  rand bit [AXI_LT_DATA_WIDTH-1:0] 	 test_mode_data;
  rand int max_addr_size;
  int cmd_done_cnt;
  
  constraint imc_mode_data_cnst { test_mode_data inside {2,4,6,8}; }
  constraint addr_size_q { soft  max_addr_size >5 && max_addr_size <=256;}
   
   
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;
  axi_master_stream_base_sequence #(AXI_STREAM_IFDW_DATA_WIDTH)	axi_master_stream_ifdw_base_seq;
  axi_master_stream_base_sequence #(AXI_STREAM_IFD0_DATA_WIDTH)	axi_master_stream_ifd0_base_seq;
  axi_master_stream_base_sequence #(AXI_STREAM_IFD2_DATA_WIDTH)	axi_master_stream_ifd2_base_seq;
   
  axi_slave_mem_response_sequence  axi_slave_stream_iau_base_seq;

  // Zero sequence delay
  axi_master_zero_delay_sequence axi_master_stream_zero_delay_ifdw_base_seq;
  axi_master_zero_delay_sequence axi_master_stream_zero_delay_ifd0_base_seq;
  axi_master_zero_delay_sequence axi_master_stream_zero_delay_ifd2_base_seq; 
  axi_slave_mem_zero_delay_sequence axi_slave_stream_zero_delay_iau_base_seq;

  // UTILS Filter Inteface Handle
  virtual mvm_utils_filter_intf mvm_utils_vif;

  // Power Surge Check Interface
  virtual mvm_power_surge_check_intf mvm_power_surge_check_intf;

  // mvm user Inteface Handle
  virtual mvm_if mvm_if;

   mvm_prg_cmd_tb_data mvm_prg_cmd_tb_data_h;
   mvm_exe_instr_tb_data mvm_exe_instr_tb_data_h;
   mvm_exe_instr_tb_data_packet mvm_exe_instr_tb_data_packet_h;
   mvm_exe_cmd_tb_data mvm_exe_cmd_tb_data_h;
   mvm_exe_cmd_tb_data_packet mvm_exe_cmd_tb_data_packet_h;
   
  /** Class Constructor */
  function new(string name = "ai_core_mvm_base_test", uvm_component parent=null);
    super.new(name,parent);
    key = new (1);
    key_for_lp_interface = new(1);
    key_for_ifdw = new(1);
    key_for_ifd0 = new(1);
    uvm_top.set_timeout(200us,1);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_HIGH)
    super.build_phase(phase);

    mvm_prg_cmd_tb_data_h= mvm_prg_cmd_tb_data::type_id::create("mvm_prg_cmd_tb_data_h");
    mvm_exe_instr_tb_data_h = mvm_exe_instr_tb_data::type_id::create("mvm_exe_instr_tb_data_h");
    mvm_exe_instr_tb_data_packet_h = mvm_exe_instr_tb_data_packet::type_id::create("mvm_exe_instr_tb_data_packet_h");
    mvm_exe_cmd_tb_data_h= mvm_exe_cmd_tb_data::type_id::create("mvm_exe_cmd_tb_data_h");
    mvm_exe_cmd_tb_data_packet_h= mvm_exe_cmd_tb_data_packet::type_id::create("mvm_exe_cmd_tb_data_packet_h");
     
    /** Add uvm_report_cb callback */
    uvm_report_cb::add(null, catcher);

    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_HIGH)

    /** Create the configuration object */
    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");

    /** Set configuration in environment */
    uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

    /** Create the configuration object for AI Core LS environment */
    m_env_cfg = ai_core_mvm_env_cfg::type_id::create("m_env_cfg");
    /** Set configuration for AI Core MVM environment */
    uvm_config_db#(ai_core_mvm_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);

    /** Create the environment */
    env = ai_core_mvm_env::type_id::create("env", this);

    /** Apply the default sequence to the System ENV virtual sequencer
     * A virtual sequence is applied by default which generates unconstrained random
     * master transactions on all masters.  Extended tests can disable this behavior in
     * one of two ways:
     *   1) If using UVM 1.0 then this virtual sequence can be overriden with the
     *      axi_null_virtual_sequence.
     *   2) If using UVM 1.1 then his virtual sequence can be overriden by configuring
     *      the default sequence of the main phase as 'null'.
     *
     * Note that this sequence is configured using the uvm_object_wrapper with the
     * uvm_config_db. So extended tests must also configure the default_sequence using
     * the uvm_object_wrapper rather than using a sequence instance.
     */
    //uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.sequencer.main_phase", "default_sequence", axi_master_random_discrete_virtual_sequence::type_id::get());

    // Set the sequence length to generate 2 transactions
    //uvm_config_db#(int unsigned)::set(this, "env.axi_system_env.sequencer.axi_master_random_discrete_virtual_sequence", "sequence_length", 2);

    /** Apply the default reset sequence */
      uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());
    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    // random selection of slave response normal or zero delay sequence
    randcase
      1: begin uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_zero_delay_sequence::type_id::get()); end
      1: begin uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get()); end
    endcase
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
    axi_master_stream_ifdw_base_seq	= axi_master_stream_base_sequence#(AXI_STREAM_IFDW_DATA_WIDTH)::type_id::create("axi_master_stream_ifdw_base_seq");
    axi_master_stream_ifd0_base_seq	= axi_master_stream_base_sequence#(AXI_STREAM_IFD0_DATA_WIDTH)::type_id::create("axi_master_stream_ifd0_base_seq");
    axi_master_stream_ifd2_base_seq     = axi_master_stream_base_sequence #(AXI_STREAM_IFD2_DATA_WIDTH)::type_id::create("axi_master_stream_ifd2_base_seq");

    axi_slave_stream_iau_base_seq	= axi_slave_mem_response_sequence::type_id::create("axi_slave_stream_iau_base_seq");

    axi_master_stream_zero_delay_ifdw_base_seq	= axi_master_zero_delay_sequence::type_id::create("axi_master_stream_zero_delay_ifdw_base_seq");
    axi_master_stream_zero_delay_ifd0_base_seq	= axi_master_zero_delay_sequence::type_id::create("axi_master_stream_zero_delay_ifd0_base_seq");
    axi_master_stream_zero_delay_ifd2_base_seq	= axi_master_zero_delay_sequence::type_id::create("axi_master_stream_zero_delay_ifd2_base_seq");

    axi_slave_stream_zero_delay_iau_base_seq	= axi_slave_mem_zero_delay_sequence::type_id::create("axi_slave_stream_zero_delay_iau_base_seq");

    /* Receieve UVM UTILS Filter Interface handle*/
    uvm_config_db#(virtual mvm_utils_filter_intf)::get(
        uvm_root::get(), "uvm_test_top", "mvm_utils_filter_intf", mvm_utils_vif);

    /* Receieve Power Surge Check Interface handle*/
    uvm_config_db#(virtual mvm_power_surge_check_intf)::get(
        uvm_root::get(), "uvm_test_top", "mvm_power_surge_check_intf", mvm_power_surge_check_intf);

    // Recieve mvm user interface handle
    uvm_config_db#(virtual mvm_if)::get(
        uvm_root::get(), "uvm_test_top", "mvm_if", mvm_if);

    if ($value$plusargs ("ROW_LEN=%d", row_len))
    `uvm_info("MVM",$sformatf("value of ROW_LEN is %d",row_len ), UVM_LOW)
    else row_len=2;
    
    if ($value$plusargs ("ROW_OFF=%d", row_off))
    `uvm_info("MVM",$sformatf("value of ROW_OFF is %d",row_off ), UVM_LOW)
    else row_off=0;
    
    if ($value$plusargs ("COL_LEN=%d", col_len))
    `uvm_info("MVM",$sformatf("value of COL_LEN is %d",col_len ), UVM_LOW)
    else col_len=2;
    
    if ($value$plusargs ("COL_OFF=%d", col_off))
    `uvm_info("MVM",$sformatf("value of COL_OFF is %d",col_off ), UVM_LOW)
    else col_off=0;
    
    if ($value$plusargs ("WEIGHT_SET=%d", weight_set))
    `uvm_info("MVM",$sformatf("value of weight_set is %d",weight_set), UVM_LOW)
    else weight_set=0;
    
    if ($value$plusargs ("LOOP_LEN=%d", loop_len))
    `uvm_info("MVM",$sformatf("value of LOOP_LEN is %d",loop_len ), UVM_LOW)
    else loop_len=1;
    
    if ($value$plusargs ("LOOP_ITER=%d", loop_iter))
    `uvm_info("MVM",$sformatf("value of loop_iter is %d",loop_iter), UVM_LOW)
    else loop_iter=3;

    col_off_intr = {5'b0,col_off};
    row_off_intr = {4'b0,row_off};
    row_len_intr = {4'b0,row_len};
    col_len_intr = {5'b0,col_len};
    weight_set_intr = {6'b0,weight_set};
    
    `uvm_info("MVM",$sformatf("value of row_off is %0d ,row_len is %0d, col_len is %0d, col_off is %0d, loop_len is %0d loop_iter is %0d",row_off, row_len, col_len, col_off, loop_len, loop_iter), UVM_LOW)

    `uvm_info("build_phase", "Exiting...", UVM_HIGH)
  endfunction: build_phase

  // Start of simulation phase
  function void start_of_simulation_phase (uvm_phase phase);
    // set cfg axi mst agent in config db to be retrieved by non uvm components like report catcher
    uvm_config_db#(svt_axi_master_agent)::set(null,"*", "CFG_AXI_MST_AGENT", env.axi_system_env.master[0]);
  endfunction: start_of_simulation_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_HIGH)
    uvm_top.print_topology();
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_HIGH)
  endfunction: end_of_elaboration_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_HIGH)
    mvm_regmodel = env.mvm_regmodel;
  endfunction : connect_phase

  virtual task run_phase(uvm_phase phase);
    bit util_limit_enable;
    bit [6:0] util_limit_value;
    bit power_smooth_dummy_ops;

    ral_read_data   = 64'h000_0000; 
 
    `uvm_info("base_test:run_phase", "Entered...", UVM_HIGH)

    //Receive UTIL LIMIT EN and UTIL LIMIT VALUE from cmd line args
    //---------------------------------------------------------------
    if($test$plusargs("UTIL_LIMIT_EN")) begin
       util_limit_enable = 1;
       if($value$plusargs("UTIL_LIMIT_VALUE=%d",util_limit_value)) begin
         `uvm_info(this.get_name(),$psprintf("UTIL_LIMIT_VALUE = %d",util_limit_value),UVM_HIGH)
       end else begin
         util_limit_value = $urandom_range(64,1);
         `uvm_info(this.get_name(),$psprintf("UTIL_LIMIT_VALUE = %d",util_limit_value),UVM_HIGH)
       end
    end else begin
       util_limit_enable = $urandom_range(1,0);
       util_limit_value = $urandom_range(64,1);
    end
    //Drive Util Limit Value
    mvm_utils_vif.mvm_util_limit_enable_i = 0;
    mvm_utils_vif.mvm_util_limit_value_i = util_limit_value;
    mvm_utils_vif.mvm_util_average_nominator_i = $urandom_range(255,0);
    @(posedge mvm_utils_vif.clk);
    mvm_utils_vif.mvm_util_limit_enable_i = util_limit_enable;
    @(posedge mvm_utils_vif.clk);

    // SET POWER SMOOTH DUMMY OPS
    //---------------------------------------------------------------
    if ($test$plusargs("POWER_SMOOTH")) begin
       power_smooth_dummy_ops = 1;
    end else begin
       power_smooth_dummy_ops = $urandom_range(1,0);
    end
    `uvm_info(this.get_name(),$psprintf("POWER_SMOOTH_DUMMY_OPS = %d",power_smooth_dummy_ops),UVM_HIGH)
    //Write to CSR
    mvm_regmodel.m_mvmexe_regmod.dp_ctrl.power_smooth_dummy_ops.set(power_smooth_dummy_ops);
    mvm_regmodel.m_mvmexe_regmod.dp_ctrl.update(status);
    mvm_power_surge_check_intf.power_smooth_dummy_ops = power_smooth_dummy_ops;

    `uvm_info("base_test:run_phase", "Exiting...", UVM_HIGH)
  endtask

  /**
   * Calculate the pass or fail status for the test in the final phase method of the
   * test. If a UVM_FATAL, UVM_ERROR, or a UVM_WARNING message has been generated the
   * test will fail.
   */
  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...",UVM_HIGH)

    super.final_phase(phase);

    svr = uvm_report_server::get_server();

    if (svr.get_severity_count(UVM_FATAL) +
        svr.get_severity_count(UVM_ERROR) +
        svr.get_severity_count(UVM_WARNING) > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

     svr.set_max_quit_count(50);
    `uvm_info("final_phase", "Exiting...", UVM_NONE)
  endfunction: final_phase

  virtual task configure_prg_reg;
    int delay;
    fork
      begin
        void'(std::randomize(delay) with { delay inside {[0:300]};});
        #(delay * 10ns);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
      end
    join_none
  endtask

  virtual task configure_exe_reg;
    int delay;
    fork
      begin
        void'(std::randomize(delay) with { delay inside {[0:300]};});
        #(delay * 10ns);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);
      end
    join_none
  endtask

  virtual task wait_for_prg_status;
   do begin
       ral_read_data   = 64'h000_0000;
       mvm_regmodel.m_mvmprg_regmod.cmdblk_status.read(status, ral_read_data);
     end while(|ral_read_data[1:0]); // IDLE state == 0   
  endtask
   
  virtual task wait_for_exe_status;
     do begin
       ral_read_data   = 64'h000_0000;
       mvm_regmodel.m_mvmexe_regmod.cmdblk_status.read(status, ral_read_data);
     end while(|ral_read_data[1:0]); // IDLE state == 0            
  endtask //
   
  virtual task check_irq_status;
    ral_read_data   = 64'h000_0000;
    mvm_regmodel.m_mvmexe_regmod.irq_status.read(status,ral_read_data);
    if(ral_read_data != 0)
    `uvm_error(get_type_name, $sformatf("Any of the irq getting asserted and irq read data value is %0d", ral_read_data))
  endtask
 
   virtual task unsigned_exe_prg_enable;
          
     mvm_regmodel.m_mvmexe_regmod.dp_ctrl.write(status, 0);
     mvm_regmodel.m_mvmprg_regmod.dp_ctrl.write(status, 0);
   
    endtask // unsigned_mult_enable
   
    
endclass:ai_core_mvm_base_test

`endif // GUARD_AI_CORE_MVM_BASE_TEST_SV
