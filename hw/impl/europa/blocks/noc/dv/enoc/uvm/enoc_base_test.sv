// *** (C) Copyright Axelera AI 2021                                                      *** //
// *** All Rights Reserved                                                                *** //
// *** Axelera AI Confidential                                                            *** //
// *** Owner : srinivas.prakash@axelera.ai                                                *** //
// ****************************************************************************************** //
// Description: This Class is used to declare all the user-defined sequences, interfaces  *** // 
// and misc components, it also has generic tasks related to NOC specific features like   *** //
// power fences, firewalls, IRQ etc                                                       *** //
// ****************************************************************************************** //

`ifndef GUARD_ENOC_BASE_TEST_SV
`define GUARD_ENOC_BASE_TEST_SV
class enoc_base_test extends uvm_test;
  /** UVM Component Utility macro */
  `uvm_component_utils(enoc_base_test)

  // Queues to get INIT & TARG from +arg //
  bit [`AXI_LP_ADDR_WIDTH-1:0]    rand_addr_q[$], get_init_q[$];
  bit [`AXI_HP_DATA_WIDTH-1:0]    axi_write_data;
  // Configuring firewall registers addresses //
  bit [`AXI_LP_ADDR_WIDTH-1:0]    disable_firewall_registers_Q [$];
  bit [`AXI_LP_ADDR_WIDTH-1:0]    disable_hide_en_firewall_registers_Q[$];
  int                             num_rand_addr;
  bit                             connectivity [enoc_inits_e][enoc_all_targs_e] = '{default: 0};    
  /** Construct the report catcher extended class*/
  //warning_catcher catcher = new();

  /** User defined interface */
  virtual enoc_tb_intf  tb_intf;

  /** Instance of the environment */
  enoc_env env;

  /** Instance of the environment configuration */
  enoc_env_cfg m_env_cfg;

  //Axi reset sequece
  axi_simple_reset_sequence           axi_reset_seq;
  axi_master_write_sequence           axi_wr_seq;
  axi_master_read_sequence            axi_rd_seq;
  axi_master_write_random_sequence    axi_rand_wr_seq;
  axi_master_read_random_sequence     axi_rand_rd_seq;
  axi_master_sequence                 axi_mst_seq;

  /** Class Constructor */
  function new(string name = "enoc_base_test", uvm_component parent=null);
    super.new(name,parent);
    //UVM_TIMEOUT
    uvm_top.set_timeout(3ms,1);
    //Get the number of random addrs
    if($test$plusargs("NUM_RAND_ADDR"))
      $value$plusargs("NUM_RAND_ADDR=%0d",num_rand_addr);
            
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    /** Add uvm_report_cb callback */
    //uvm_report_cb::add(null, catcher);
    /** Get the user defined interface to access & control pwr_domain_fences and other misc signals **/
    uvm_config_db#(virtual enoc_tb_intf)::get(uvm_root::get(), "", "tb_intf", tb_intf);
    /** Factory override of the master transaction object */
    //set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_LOW)

    /** Create the configuration object */
    m_env_cfg = enoc_env_cfg::type_id::create("m_env_cfg");
    /** Set configuration */
    uvm_config_db#(enoc_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);
    /** Create the environment */
    env = enoc_env::type_id::create("env", this);

    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());
    
    //Setting Apb slave memory sequence as base sequence for apb slaves
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.apb_system_env*.slave*.sequencer.run_phase", "default_sequence", svt_apb_slave_memory_sequence::type_id::get());

    axi_reset_seq         = axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    axi_wr_seq            = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq            = axi_master_read_sequence::type_id::create("axi_rd_seq");
    axi_rand_wr_seq       = axi_master_write_random_sequence::type_id::create("axi_rand_wr_seq");
    axi_rand_rd_seq       = axi_master_read_random_sequence::type_id::create("axi_rand_rd_seq");
    axi_mst_seq           = axi_master_sequence::type_id::create("axi_mst_seq");
    
    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase
  // End of elaboration phase //
  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    uvm_top.print_topology();
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction: end_of_elaboration_phase
  // Connect phase //
  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    //regmodel = env.regmodel;
  endfunction : connect_phase
  // Run phase //
  virtual task run_phase(uvm_phase phase);
    `uvm_info ("enoc_base_test", "Objection raised", UVM_HIGH)
    //raise_objection
    phase.raise_objection(this);
    //Initializations methods
    initialize_conn_matrix();
    get_init_from_ext_args();
    #400ns;
    // Initializing power fences & open before reset
    open_pwr_fence();
    // Apply reset
    axi_reset_seq.start(env.sequencer);
    // Initializing power fences & close after reset
    close_pwr_fence();
    #400ns;
    // Initializing power fences & open after reset
    fork
      open_pwr_fence();
    // Apply reset
      axi_reset_seq.start(env.sequencer);
    join
    @(posedge tb_intf.enoc_rst_n);
    close_pwr_fence();
    // Opening power fences
    @(posedge tb_intf.enoc_clk);
    open_pwr_fence();
    #400ns;
    //disable_firewalls_all(1);
    #400ns;
    //drop_objection
    phase.drop_objection(this);
    `uvm_info ("enoc_base_test", "Objection dropped", UVM_HIGH)
  
  endtask : run_phase

  // *****************************************************************************************
  // Task to close the power domain fences
  // *****************************************************************************************
  task close_pwr_fence();
   `uvm_info ("POWER_FENCE", "Closing power fences for all targets", UVM_LOW)
   @(posedge tb_intf.enoc_clk);
   tb_intf.i_aic_0_pwr_idle_req         = 1;
   tb_intf.i_aic_1_pwr_idle_req         = 1;
   tb_intf.i_aic_2_pwr_idle_req         = 1;
   tb_intf.i_aic_3_pwr_idle_req         = 1;
   tb_intf.i_aic_4_pwr_idle_req         = 1;
   tb_intf.i_aic_5_pwr_idle_req         = 1;
   tb_intf.i_aic_6_pwr_idle_req         = 1;
   tb_intf.i_aic_7_pwr_idle_req         = 1;
   tb_intf.i_apu_pwr_idle_req           = 1;
   tb_intf.i_dcd_mcu_pwr_idle_req       = 1;
   tb_intf.i_dcd_pwr_idle_req           = 1;
   tb_intf.i_l2_0_pwr_idle_req          = 1;
   tb_intf.i_l2_1_pwr_idle_req          = 1;
   tb_intf.i_l2_2_pwr_idle_req          = 1;
   tb_intf.i_l2_3_pwr_idle_req          = 1;
   tb_intf.i_l2_4_pwr_idle_req          = 1;
   tb_intf.i_l2_5_pwr_idle_req          = 1;
   tb_intf.i_l2_6_pwr_idle_req          = 1;
   tb_intf.i_l2_7_pwr_idle_req          = 1;
   tb_intf.i_lpddr_graph_0_pwr_idle_vec_req = 2'b11;
   tb_intf.i_lpddr_graph_1_pwr_idle_vec_req = 2'b11;
   tb_intf.i_lpddr_graph_2_pwr_idle_vec_req = 2'b11;
   tb_intf.i_lpddr_graph_3_pwr_idle_vec_req = 2'b11;
   tb_intf.i_lpddr_ppp_0_pwr_idle_vec_req   = 2'b11;
   tb_intf.i_lpddr_ppp_1_pwr_idle_vec_req   = 2'b11;
   tb_intf.i_lpddr_ppp_2_pwr_idle_vec_req   = 2'b11;
   tb_intf.i_lpddr_ppp_3_pwr_idle_vec_req   = 2'b11;
   tb_intf.i_pcie_init_mt_pwr_idle_req      = 1;
   tb_intf.i_pcie_targ_mt_pwr_idle_req      = 1;
   tb_intf.i_pcie_targ_cfg_pwr_idle_req     = 1;
   tb_intf.i_pcie_targ_cfg_dbi_pwr_idle_req = 1;
   tb_intf.i_pve_0_pwr_idle_req         = 1;
   tb_intf.i_pve_1_pwr_idle_req         = 1;
   tb_intf.i_soc_mgmt_pwr_idle_req      = 1;
   tb_intf.i_soc_periph_pwr_idle_req    = 1;
   tb_intf.i_sys_spm_pwr_idle_req       = 1;
  endtask : close_pwr_fence

  // *****************************************************************************************
  // Task to open the power domain fences
  // *****************************************************************************************
  task open_pwr_fence();
   `uvm_info ("POWER_FENCE", "Opening power fences for all targets", UVM_LOW)
   @(posedge tb_intf.enoc_clk);
   tb_intf.i_aic_0_pwr_idle_req               = 0;
   tb_intf.i_aic_1_pwr_idle_req               = 0;
   tb_intf.i_aic_2_pwr_idle_req               = 0;
   tb_intf.i_aic_3_pwr_idle_req               = 0;
   tb_intf.i_aic_4_pwr_idle_req               = 0;
   tb_intf.i_aic_5_pwr_idle_req               = 0;
   tb_intf.i_aic_6_pwr_idle_req               = 0;
   tb_intf.i_aic_7_pwr_idle_req               = 0;
   tb_intf.i_apu_pwr_idle_req                 = 0;
   tb_intf.i_dcd_mcu_pwr_idle_req             = 0;
   tb_intf.i_dcd_pwr_idle_req                 = 0;
   tb_intf.i_l2_0_pwr_idle_req                = 0;
   tb_intf.i_l2_1_pwr_idle_req                = 0;
   tb_intf.i_l2_2_pwr_idle_req                = 0;
   tb_intf.i_l2_3_pwr_idle_req                = 0;
   tb_intf.i_l2_4_pwr_idle_req                = 0;
   tb_intf.i_l2_5_pwr_idle_req                = 0;
   tb_intf.i_l2_6_pwr_idle_req                = 0;
   tb_intf.i_l2_7_pwr_idle_req                = 0;
   tb_intf.i_lpddr_graph_0_pwr_idle_vec_req   = 2'b00;
   tb_intf.i_lpddr_graph_1_pwr_idle_vec_req   = 2'b00;
   tb_intf.i_lpddr_graph_2_pwr_idle_vec_req   = 2'b00;
   tb_intf.i_lpddr_graph_3_pwr_idle_vec_req   = 2'b00;
   tb_intf.i_lpddr_ppp_0_pwr_idle_vec_req     = 2'b00;
   tb_intf.i_lpddr_ppp_1_pwr_idle_vec_req     = 2'b00;
   tb_intf.i_lpddr_ppp_2_pwr_idle_vec_req     = 2'b00;
   tb_intf.i_lpddr_ppp_3_pwr_idle_vec_req     = 2'b00;
   tb_intf.i_pcie_init_mt_pwr_idle_req        = 0;
   tb_intf.i_pcie_targ_mt_pwr_idle_req        = 0;
   tb_intf.i_pcie_targ_cfg_pwr_idle_req       = 0;
   tb_intf.i_pcie_targ_cfg_dbi_pwr_idle_req   = 0;
   tb_intf.i_pve_0_pwr_idle_req               = 0;
   tb_intf.i_pve_1_pwr_idle_req               = 0;
   tb_intf.i_soc_mgmt_pwr_idle_req            = 0;
   tb_intf.i_soc_periph_pwr_idle_req          = 0;
   tb_intf.i_sys_spm_pwr_idle_req             = 0;
  endtask : open_pwr_fence

  // *****************************************************************************************
  // Task to open the power domain fences
  // *****************************************************************************************
  task wait_pwr_fence_idle_0();
   `uvm_info ("POWER_FENCE", "Waiting for power fences to goto IDLE=0", UVM_LOW)
   @(posedge tb_intf.enoc_clk);
      wait(tb_intf.o_aic_0_pwr_idle_ack             == 0 &&
           tb_intf.o_aic_1_pwr_idle_ack             == 0 &&
           tb_intf.o_aic_2_pwr_idle_ack             == 0 &&
           tb_intf.o_aic_3_pwr_idle_ack             == 0 &&
           tb_intf.o_aic_4_pwr_idle_ack             == 0 &&
           tb_intf.o_aic_5_pwr_idle_ack             == 0 &&
           tb_intf.o_aic_6_pwr_idle_ack             == 0 &&
           tb_intf.o_aic_7_pwr_idle_ack             == 0 &&
           tb_intf.o_apu_pwr_idle_ack               == 0 &&
           tb_intf.o_dcd_mcu_pwr_idle_ack           == 0 &&
           tb_intf.o_dcd_pwr_idle_ack               == 0 &&
           tb_intf.o_l2_0_pwr_idle_ack              == 0 &&
           tb_intf.o_l2_1_pwr_idle_ack              == 0 &&
           tb_intf.o_l2_2_pwr_idle_ack              == 0 &&
           tb_intf.o_l2_3_pwr_idle_ack              == 0 &&
           tb_intf.o_l2_4_pwr_idle_ack              == 0 &&
           tb_intf.o_l2_5_pwr_idle_ack              == 0 &&
           tb_intf.o_l2_6_pwr_idle_ack              == 0 &&
           tb_intf.o_l2_7_pwr_idle_ack              == 0 &&
           tb_intf.o_lpddr_graph_0_pwr_idle_vec_ack == 2'b00 &&
           tb_intf.o_lpddr_graph_1_pwr_idle_vec_ack == 2'b00 &&
           tb_intf.o_lpddr_graph_2_pwr_idle_vec_ack == 2'b00 &&
           tb_intf.o_lpddr_graph_3_pwr_idle_vec_ack == 2'b00 &&
           tb_intf.o_lpddr_ppp_0_pwr_idle_vec_ack   == 2'b00 &&
           tb_intf.o_lpddr_ppp_1_pwr_idle_vec_ack   == 2'b00 &&
           tb_intf.o_lpddr_ppp_2_pwr_idle_vec_ack   == 2'b00 &&
           tb_intf.o_lpddr_ppp_3_pwr_idle_vec_ack   == 2'b00 &&
           tb_intf.o_pcie_init_mt_pwr_idle_ack      == 0 &&
           tb_intf.o_pcie_targ_mt_pwr_idle_ack      == 0 &&
           tb_intf.o_pcie_targ_cfg_pwr_idle_ack     == 0 &&
           tb_intf.o_pcie_targ_cfg_dbi_pwr_idle_ack == 0 &&
           tb_intf.o_pve_0_pwr_idle_ack             == 0 &&
           tb_intf.o_pve_1_pwr_idle_ack             == 0 &&
           tb_intf.o_soc_mgmt_pwr_idle_ack          == 0 &&
           tb_intf.o_soc_periph_pwr_idle_ack        == 0 &&
           tb_intf.o_sys_spm_pwr_idle_ack           == 0);
  endtask : wait_pwr_fence_idle_0

  // *****************************************************************************************
  // Task to open the power domain fences
  // *****************************************************************************************
  task wait_pwr_fence_idle_1();
   `uvm_info ("POWER_FENCE", "Waiting for power fences to goto IDLE=1", UVM_LOW)
   @(posedge tb_intf.enoc_clk);
      wait(tb_intf.o_aic_0_pwr_idle_ack             == 1);
      wait(tb_intf.o_aic_1_pwr_idle_ack             == 1);
      wait(tb_intf.o_aic_2_pwr_idle_ack             == 1);
      wait(tb_intf.o_aic_3_pwr_idle_ack             == 1);
      wait(tb_intf.o_aic_4_pwr_idle_ack             == 1);
      wait(tb_intf.o_aic_5_pwr_idle_ack             == 1);
      wait(tb_intf.o_aic_6_pwr_idle_ack             == 1);
      wait(tb_intf.o_aic_7_pwr_idle_ack             == 1);
      wait(tb_intf.o_apu_pwr_idle_ack               == 1);
      wait(tb_intf.o_dcd_mcu_pwr_idle_ack           == 1);
      wait(tb_intf.o_dcd_pwr_idle_ack               == 1);
      wait(tb_intf.o_l2_0_pwr_idle_ack              == 1);
      wait(tb_intf.o_l2_1_pwr_idle_ack              == 1);
      wait(tb_intf.o_l2_2_pwr_idle_ack              == 1);
      wait(tb_intf.o_l2_3_pwr_idle_ack              == 1);
      wait(tb_intf.o_l2_4_pwr_idle_ack              == 1);
      wait(tb_intf.o_l2_5_pwr_idle_ack              == 1);
      wait(tb_intf.o_l2_6_pwr_idle_ack              == 1);
      wait(tb_intf.o_l2_7_pwr_idle_ack              == 1);
      wait(tb_intf.o_lpddr_graph_0_pwr_idle_vec_ack == 2'b11);
      wait(tb_intf.o_lpddr_graph_1_pwr_idle_vec_ack == 2'b11);
      wait(tb_intf.o_lpddr_graph_2_pwr_idle_vec_ack == 2'b11);
      wait(tb_intf.o_lpddr_graph_3_pwr_idle_vec_ack == 2'b11);
      wait(tb_intf.o_lpddr_ppp_0_pwr_idle_vec_ack   == 2'b11);
      wait(tb_intf.o_lpddr_ppp_1_pwr_idle_vec_ack   == 2'b11);
      wait(tb_intf.o_lpddr_ppp_2_pwr_idle_vec_ack   == 2'b11);
      wait(tb_intf.o_lpddr_ppp_3_pwr_idle_vec_ack   == 2'b11);
      wait(tb_intf.o_pcie_init_mt_pwr_idle_ack      == 1);
      wait(tb_intf.o_pcie_targ_mt_pwr_idle_ack      == 1);
      wait(tb_intf.o_pcie_targ_cfg_pwr_idle_ack     == 1);
      wait(tb_intf.o_pcie_targ_cfg_dbi_pwr_idle_ack == 1);
      wait(tb_intf.o_pve_0_pwr_idle_ack             == 1);
      wait(tb_intf.o_pve_1_pwr_idle_ack             == 1);
      wait(tb_intf.o_soc_mgmt_pwr_idle_ack          == 1);
      wait(tb_intf.o_soc_periph_pwr_idle_ack        == 1);
      wait(tb_intf.o_sys_spm_pwr_idle_ack           == 1);
  endtask : wait_pwr_fence_idle_1
  
  // *****************************************************************************************
  // Task to lower the power domain fences initially once after reset
  // *****************************************************************************************
  task init_open_pwr_fence();
   `uvm_info ("POWER_FENCE", "Initialization of power fences", UVM_LOW)
   close_pwr_fence();
   @(posedge tb_intf.enoc_clk);
   wait(tb_intf.enoc_rst_n == 1);
   #1500ns;
   //wait_pwr_fence_idle_0();
   `uvm_info ("POWER_FENCE", "Opening the power fences after initial reset", UVM_LOW)
   open_pwr_fence(); 
  endtask : init_open_pwr_fence

  // *****************************************************************************************
  // Task to generate randomized addrs of europa memory map based on +ARG
  // *****************************************************************************************
  task gen_axi_addrs(input bit is_rsvd); //{
    bit [`AXI_LP_ADDR_WIDTH-1:0] targ_addr;
  
    if (!is_rsvd) begin //{
        // Individual Targets
        if ($test$plusargs("APU_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`APU_TARG_SA : `APU_TARG_EA]};//#1537,#1569,#2211
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SOC_MGMT_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SOC_MGMT_TARG_SA : `SOC_MGMT_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SOC_PERIPH_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SOC_PERIPH_TARG_SA : `SOC_PERIPH_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("PCIE_TARG_CFG_DBI")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`PCIE_DBI_TARG_SA : `PCIE_DBI_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("NOC_INT_TARG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`NOC_INT_TARG_SA : `NOC_INT_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // AIC SYSCFG Targets
        if ($test$plusargs("AIC_0_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_AICORE_0_AO_CSR_TARG_SA : `SYS_CFG_AICORE_0_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_1_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_AICORE_1_AO_CSR_TARG_SA : `SYS_CFG_AICORE_1_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_2_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_AICORE_2_AO_CSR_TARG_SA : `SYS_CFG_AICORE_2_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_3_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_AICORE_3_AO_CSR_TARG_SA : `SYS_CFG_AICORE_3_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_4_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_AICORE_4_AO_CSR_TARG_SA : `SYS_CFG_AICORE_4_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_5_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_AICORE_5_AO_CSR_TARG_SA : `SYS_CFG_AICORE_5_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_6_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_AICORE_6_AO_CSR_TARG_SA : `SYS_CFG_AICORE_6_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_7_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_AICORE_7_AO_CSR_TARG_SA : `SYS_CFG_AICORE_7_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // L2 SYSCFG Targets
        if ($test$plusargs("L2_0_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_L2_MODULE_0_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_0_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_1_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_L2_MODULE_1_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_1_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_2_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_L2_MODULE_2_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_2_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_3_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_L2_MODULE_3_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_3_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_4_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_L2_MODULE_4_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_4_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_5_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_L2_MODULE_5_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_5_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_6_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_L2_MODULE_6_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_6_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_7_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_L2_MODULE_7_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_7_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // LPDDR GRAPH SYSCFG Targets
        if ($test$plusargs("LPDDR_GRAPH_0_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_0_GRAPH_0_AO_CSR_TARG_SA : `SYS_CFG_DDR_0_GRAPH_0_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_GRAPH_1_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_1_GRAPH_1_AO_CSR_TARG_SA : `SYS_CFG_DDR_1_GRAPH_1_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_GRAPH_2_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_2_GRAPH_2_AO_CSR_TARG_SA : `SYS_CFG_DDR_2_GRAPH_2_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_GRAPH_3_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_3_GRAPH_3_AO_CSR_TARG_SA : `SYS_CFG_DDR_3_GRAPH_3_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // LPDDR PPP SYSCFG Targets
        if ($test$plusargs("LPDDR_PPP_0_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_4_PPP_0_AO_CSR_TARG_SA : `SYS_CFG_DDR_4_PPP_0_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_PPP_1_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_5_PPP_1_AO_CSR_TARG_SA : `SYS_CFG_DDR_5_PPP_1_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_PPP_2_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_6_PPP_2_AO_CSR_TARG_SA : `SYS_CFG_DDR_6_PPP_2_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_PPP_3_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_7_PPP_3_AO_CSR_TARG_SA : `SYS_CFG_DDR_7_PPP_3_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // Other SYSCFG Targets
        if ($test$plusargs("PVE_0_SYSCFG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_PVE_0_AO_CSR_TARG_SA : `SYS_CFG_PVE_0_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("PVE_1_SYSCFG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_PVE_1_AO_CSR_TARG_SA : `SYS_CFG_PVE_1_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("PCIE_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_PCIE_AO_CSR_TARG_SA : `SYS_CFG_PCIE_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("DCD_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DECODER_AO_CSR_TARG_SA : `SYS_CFG_DECODER_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("APU_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_APU_AO_CSR_TARG_SA : `SYS_CFG_APU_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SOC_MGMT_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_SOC_MGMT_AO_CSR_TARG_SA : `SYS_CFG_SOC_MGMT_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SOC_PERIPH_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_SOC_PERIPH_AO_CSR_TARG_SA : `SYS_CFG_SOC_PERIPH_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SYS_SPM_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_SYS_SPM_AO_CSR_TARG_SA : `SYS_CFG_SYS_SPM_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("DDR_WEST_PLL_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_DDR_WEST_PLL_AO_CSR_TARG_SA : `SYS_CFG_DDR_WEST_PLL_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SDMA_0_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_SDMA_0_AO_CSR_TARG_SA : `SYS_CFG_SDMA_0_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SDMA_1_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_SDMA_1_AO_CSR_TARG_SA : `SYS_CFG_SDMA_1_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("CLK_GEN_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_SOC_MGMT_CLOCK_GEN_TARG_SA : `SYS_CFG_SOC_MGMT_CLOCK_GEN_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("RST_GEN_TARG_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_SOC_MGMT_RESET_GEN_TARG_SA : `SYS_CFG_SOC_MGMT_RESET_GEN_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("NOC_SYSCFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_CFG_SOC_MGMT_NOC_AO_CSR_TARG_SA : `SYS_CFG_SOC_MGMT_NOC_AO_CSR_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // LT Targets
        if ($test$plusargs("SDMA_0_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SDMA_0_TARG_SA : `SDMA_0_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SDMA_1_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SDMA_1_TARG_SA : `SDMA_1_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("SYS_SPM_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`SYS_SPM_TARG_SA : `SYS_SPM_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // HT Targets
        if ($test$plusargs("L2_0_TARG_HT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`L2_MODULE_0_TARG_SA : `L2_MODULE_0_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_1_TARG_HT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`L2_MODULE_1_TARG_SA : `L2_MODULE_1_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_2_TARG_HT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`L2_MODULE_2_TARG_SA : `L2_MODULE_2_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_3_TARG_HT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`L2_MODULE_3_TARG_SA : `L2_MODULE_3_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_4_TARG_HT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`L2_MODULE_4_TARG_SA : `L2_MODULE_4_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_5_TARG_HT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`L2_MODULE_5_TARG_SA : `L2_MODULE_5_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_6_TARG_HT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`L2_MODULE_6_TARG_SA : `L2_MODULE_6_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("L2_7_TARG_HT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`L2_MODULE_7_TARG_SA : `L2_MODULE_7_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // AIC LT Targets
        if ($test$plusargs("AIC_0_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`AICORE_0_TARG_SA : `AICORE_0_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_1_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`AICORE_1_TARG_SA : `AICORE_1_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_2_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`AICORE_2_TARG_SA : `AICORE_2_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_3_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`AICORE_3_TARG_SA : `AICORE_3_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_4_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`AICORE_4_TARG_SA : `AICORE_4_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_5_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`AICORE_5_TARG_SA : `AICORE_5_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_6_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`AICORE_6_TARG_SA : `AICORE_6_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("AIC_7_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`AICORE_7_TARG_SA : `AICORE_7_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // PVE LT Targets
        if ($test$plusargs("PVE_0_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`PVE_0_TARG_SA : `PVE_0_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("PVE_1_TARG_LT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`PVE_1_TARG_SA : `PVE_1_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        if ($test$plusargs("DCD_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DCD_CFG_TARG_SA : `DCD_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // LPDDR GRAPH HT Targets 
        if ($test$plusargs("LPDDR_GRAPH_0_TARG_HT") || 
            $test$plusargs("LPDDR_GRAPH_1_TARG_HT") ||
            $test$plusargs("LPDDR_GRAPH_2_TARG_HT") ||
            $test$plusargs("LPDDR_GRAPH_3_TARG_HT") ) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_0_GRAPH_TARG_SA : `DDR_0_GRAPH_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        
        // LPDDR PPP MT Targets 
        if ($test$plusargs("LPDDR_PPP_0_TARG_MT") ||
            $test$plusargs("LPDDR_PPP_1_TARG_MT") ||
            $test$plusargs("LPDDR_PPP_2_TARG_MT") ||
            $test$plusargs("LPDDR_PPP_3_TARG_MT") ) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_1_PPP_TARG_SA : `DDR_1_PPP_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        
        // LPDDR GRAPH TARG CFG 
        if ($test$plusargs("LPDDR_GRAPH_0_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_0_CTRL_GRAPH_0_CFG_TARG_SA : `DDR_0_CTRL_GRAPH_0_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_GRAPH_1_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_1_CTRL_GRAPH_1_CFG_TARG_SA : `DDR_1_CTRL_GRAPH_1_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_GRAPH_2_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_2_CTRL_GRAPH_2_CFG_TARG_SA : `DDR_2_CTRL_GRAPH_2_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_GRAPH_3_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_3_CTRL_GRAPH_3_CFG_TARG_SA : `DDR_3_CTRL_GRAPH_3_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // LPDDR PPP TARG CFG 
        if ($test$plusargs("LPDDR_PPP_0_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_4_CTRL_PPP_0_CFG_TARG_SA : `DDR_4_CTRL_PPP_0_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_PPP_1_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_5_CTRL_PPP_1_CFG_TARG_SA : `DDR_5_CTRL_PPP_1_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_PPP_2_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_6_CTRL_PPP_2_CFG_TARG_SA : `DDR_6_CTRL_PPP_2_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
        if ($test$plusargs("LPDDR_PPP_3_TARG_CFG")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`DDR_7_CTRL_PPP_3_CFG_TARG_SA : `DDR_7_CTRL_PPP_3_CFG_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // PCIE HOST TARG MT 
        if ($test$plusargs("PCIE_HOST_TARG_MT")) begin
            std::randomize(targ_addr) with {
                targ_addr inside {[`PCIE_HOST_MT_TARG_SA : `PCIE_HOST_MT_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);
        end
  
        // Handling "ALL_AXI_TARGS"
        if ($test$plusargs("ALL_AXI_TARGS")) begin //{
            // Individual address ranges
            std::randomize(targ_addr) with {targ_addr inside {[`APU_TARG_SA : `APU_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            std::randomize(targ_addr) with {targ_addr inside {[`SOC_MGMT_TARG_SA : `SOC_MGMT_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            std::randomize(targ_addr) with {targ_addr inside {[`SOC_PERIPH_TARG_SA : `SOC_PERIPH_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            std::randomize(targ_addr) with {targ_addr inside {[`PCIE_DBI_TARG_SA : `PCIE_DBI_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            std::randomize(targ_addr) with {targ_addr inside {[`NOC_INT_TARG_SA : `NOC_INT_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            //std::randomize(targ_addr) with {targ_addr inside {[`SDMA_0_TARG_SA : `SDMA_0_TARG_EA]};}; //TODO: en after pctl access
            //rand_addr_q.push_back(targ_addr);
  
            //std::randomize(targ_addr) with {targ_addr inside {[`SDMA_1_TARG_SA : `SDMA_1_TARG_EA]};};
            //rand_addr_q.push_back(targ_addr);
  
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_SPM_TARG_SA : `SYS_SPM_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            // L2 Modules
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_0_TARG_SA : `L2_MODULE_0_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_1_TARG_SA : `L2_MODULE_1_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_2_TARG_SA : `L2_MODULE_2_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_3_TARG_SA : `L2_MODULE_3_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_4_TARG_SA : `L2_MODULE_4_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_5_TARG_SA : `L2_MODULE_5_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_6_TARG_SA : `L2_MODULE_6_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_7_TARG_SA : `L2_MODULE_7_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            // AICores
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_0_TARG_SA : `AICORE_0_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_1_TARG_SA : `AICORE_1_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_2_TARG_SA : `AICORE_2_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_3_TARG_SA : `AICORE_3_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_4_TARG_SA : `AICORE_4_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_5_TARG_SA : `AICORE_5_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_6_TARG_SA : `AICORE_6_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_7_TARG_SA : `AICORE_7_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            // PVEs
            //std::randomize(targ_addr) with {targ_addr inside {[`PVE_0_TARG_SA : `PVE_0_TARG_EA]};};
            //rand_addr_q.push_back(targ_addr);
            //std::randomize(targ_addr) with {targ_addr inside {[`PVE_1_TARG_SA : `PVE_1_TARG_EA]};};
            //rand_addr_q.push_back(targ_addr);
  
            //PCIe Host Targ
            std::randomize(targ_addr) with {targ_addr inside {[`PCIE_HOST_MT_TARG_SA : `PCIE_HOST_MT_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            
            // 4x DDR Graph Targ
            repeat (4) begin //{
                std::randomize(targ_addr) with {
                    targ_addr inside {[`DDR_0_GRAPH_TARG_SA : `DDR_0_GRAPH_TARG_EA]};
                };
                rand_addr_q.push_back(targ_addr);
            end //}
  
            // 4x DDR PPP Targ
            repeat (4) begin //{
                std::randomize(targ_addr) with {
                    targ_addr inside {[`DDR_1_PPP_TARG_SA : `DDR_1_PPP_TARG_EA]};
                };
                rand_addr_q.push_back(targ_addr);
            end //}
        end //}
  
        // Handling "ALL_CFG_TARGS"
        if ($test$plusargs("ALL_CFG_TARGS")) begin //{
  
            // AIC SYSCFG Targets
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_AICORE_0_AO_CSR_TARG_SA : `SYS_CFG_AICORE_0_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                      
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_AICORE_1_AO_CSR_TARG_SA : `SYS_CFG_AICORE_1_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                      
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_AICORE_2_AO_CSR_TARG_SA : `SYS_CFG_AICORE_2_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                      
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_AICORE_3_AO_CSR_TARG_SA : `SYS_CFG_AICORE_3_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                      
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_AICORE_4_AO_CSR_TARG_SA : `SYS_CFG_AICORE_4_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                      
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_AICORE_5_AO_CSR_TARG_SA : `SYS_CFG_AICORE_5_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                      
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_AICORE_6_AO_CSR_TARG_SA : `SYS_CFG_AICORE_6_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                      
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_AICORE_7_AO_CSR_TARG_SA : `SYS_CFG_AICORE_7_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            // L2 SYSCFG Targets
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_L2_MODULE_0_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_0_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                            
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_L2_MODULE_1_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_1_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                            
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_L2_MODULE_2_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_2_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                            
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_L2_MODULE_3_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_3_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                            
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_L2_MODULE_4_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_4_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                            
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_L2_MODULE_5_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_5_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                            
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_L2_MODULE_6_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_6_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                                            
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_L2_MODULE_7_AO_CSR_TARG_SA : `SYS_CFG_L2_MODULE_7_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            // LPDDR GRAPH SYSCFG Targets
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_0_GRAPH_0_AO_CSR_TARG_SA : `SYS_CFG_DDR_0_GRAPH_0_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_1_GRAPH_1_AO_CSR_TARG_SA : `SYS_CFG_DDR_1_GRAPH_1_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_2_GRAPH_2_AO_CSR_TARG_SA : `SYS_CFG_DDR_2_GRAPH_2_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_3_GRAPH_3_AO_CSR_TARG_SA : `SYS_CFG_DDR_3_GRAPH_3_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            
            // LPDDR PPP SYSCFG Targets
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_4_PPP_0_AO_CSR_TARG_SA : `SYS_CFG_DDR_4_PPP_0_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_5_PPP_1_AO_CSR_TARG_SA : `SYS_CFG_DDR_5_PPP_1_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_6_PPP_2_AO_CSR_TARG_SA : `SYS_CFG_DDR_6_PPP_2_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_7_PPP_3_AO_CSR_TARG_SA : `SYS_CFG_DDR_7_PPP_3_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
  
            // Other CFG Targets
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_PVE_0_AO_CSR_TARG_SA : `SYS_CFG_PVE_0_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_PVE_1_AO_CSR_TARG_SA : `SYS_CFG_PVE_1_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_PCIE_AO_CSR_TARG_SA : `SYS_CFG_PCIE_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DECODER_AO_CSR_TARG_SA : `SYS_CFG_DECODER_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_APU_AO_CSR_TARG_SA : `SYS_CFG_APU_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SOC_MGMT_AO_CSR_TARG_SA : `SYS_CFG_SOC_MGMT_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SOC_PERIPH_AO_CSR_TARG_SA : `SYS_CFG_SOC_PERIPH_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SYS_SPM_AO_CSR_TARG_SA : `SYS_CFG_SYS_SPM_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_DDR_WEST_PLL_AO_CSR_TARG_SA : `SYS_CFG_DDR_WEST_PLL_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SDMA_0_AO_CSR_TARG_SA : `SYS_CFG_SDMA_0_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SDMA_1_AO_CSR_TARG_SA : `SYS_CFG_SDMA_1_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SOC_MGMT_CLOCK_GEN_TARG_SA : `SYS_CFG_SOC_MGMT_CLOCK_GEN_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SOC_MGMT_RESET_GEN_TARG_SA : `SYS_CFG_SOC_MGMT_RESET_GEN_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SOC_MGMT_NOC_AO_CSR_TARG_SA : `SYS_CFG_SOC_MGMT_NOC_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_CFG_SOC_MGMT_AO_CSR_TARG_SA : `SYS_CFG_SOC_MGMT_AO_CSR_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
        end //}
  
        // Handling "ALL_LT_TARGS"
        if ($test$plusargs("ALL_LT_TARGS")) begin //{
            // List of LT address ranges
            std::randomize(targ_addr) with {targ_addr inside {[`APU_TARG_SA        : `APU_TARG_EA       ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SOC_MGMT_TARG_SA   : `SOC_MGMT_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SOC_PERIPH_TARG_SA : `SOC_PERIPH_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`PCIE_DBI_TARG_SA   : `PCIE_DBI_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`NOC_INT_TARG_SA    : `NOC_INT_TARG_EA   ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SDMA_0_TARG_SA     : `SDMA_0_TARG_EA    ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SDMA_1_TARG_SA     : `SDMA_1_TARG_EA    ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`SYS_SPM_TARG_SA    : `SYS_SPM_TARG_EA   ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_0_TARG_SA   : `AICORE_0_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_1_TARG_SA   : `AICORE_1_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_2_TARG_SA   : `AICORE_2_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_3_TARG_SA   : `AICORE_3_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_4_TARG_SA   : `AICORE_4_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_5_TARG_SA   : `AICORE_5_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_6_TARG_SA   : `AICORE_6_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`AICORE_7_TARG_SA   : `AICORE_7_TARG_EA  ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`PVE_0_TARG_SA      : `PVE_0_TARG_EA     ]};};
            rand_addr_q.push_back(targ_addr);
            std::randomize(targ_addr) with {targ_addr inside {[`PVE_1_TARG_SA      : `PVE_1_TARG_EA     ]};};
            rand_addr_q.push_back(targ_addr);
        end //}
  
        // Handling "ALL_MT_TARGS"
        if ($test$plusargs("ALL_MT_TARGS")) begin //{
            // 4x LPDDR PPP MT Targets 
            repeat (4) begin //{
                std::randomize(targ_addr) with {
                    targ_addr inside {[`DDR_1_PPP_TARG_SA : `DDR_1_PPP_TARG_EA]};
                };
                rand_addr_q.push_back(targ_addr);                                                     
            end //}
  
            // PCIE HOST TARG MT 
            std::randomize(targ_addr) with {
                targ_addr inside {[`PCIE_HOST_MT_TARG_SA : `PCIE_HOST_MT_TARG_EA]};
            };
            rand_addr_q.push_back(targ_addr);                                                     
        end //}
  
        // Handling "ALL_HT_TARGS"
        if ($test$plusargs("ALL_HT_TARGS")) begin //{
            // 4x LPDDR GRAPH HT Targets 
            repeat (4) begin //{
                std::randomize(targ_addr) with {
                    targ_addr inside {[`DDR_0_GRAPH_TARG_SA : `DDR_0_GRAPH_TARG_EA]};
                };
                rand_addr_q.push_back(targ_addr);                                                     
            end //}
  
            // L2 HT Targets
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_0_TARG_SA : `L2_MODULE_0_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                     
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_1_TARG_SA : `L2_MODULE_1_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                     
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_2_TARG_SA : `L2_MODULE_2_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                     
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_3_TARG_SA : `L2_MODULE_3_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                     
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_4_TARG_SA : `L2_MODULE_4_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                     
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_5_TARG_SA : `L2_MODULE_5_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                     
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_6_TARG_SA : `L2_MODULE_6_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);                                                     
            std::randomize(targ_addr) with {targ_addr inside {[`L2_MODULE_7_TARG_SA : `L2_MODULE_7_TARG_EA]};};
            rand_addr_q.push_back(targ_addr);
        end //}
  
    end //}
    else begin //{
        // Reserved address ranges
        std::randomize(targ_addr) with {
            targ_addr inside {[`RESERVED_0_TARG_SA : `RESERVED_0_TARG_EA]};
        };
        rand_addr_q.push_back(targ_addr);
  
        std::randomize(targ_addr) with {
            targ_addr inside {[`RESERVED_1_TARG_SA : `RESERVED_1_TARG_EA]};
        };
        rand_addr_q.push_back(targ_addr);
        std::randomize(targ_addr) with {
            targ_addr inside {[`RESERVED_2_TARG_SA : `RESERVED_2_TARG_EA]};
        };
        rand_addr_q.push_back(targ_addr);
        std::randomize(targ_addr) with {
            targ_addr inside {[`RESERVED_3_TARG_SA : `RESERVED_3_TARG_EA]};
        };
        rand_addr_q.push_back(targ_addr);
        std::randomize(targ_addr) with {
            targ_addr inside {[`RESERVED_4_TARG_SA : `RESERVED_4_TARG_EA]};
        };
        rand_addr_q.push_back(targ_addr);
        std::randomize(targ_addr) with {
            targ_addr inside {[`RESERVED_5_TARG_SA : `RESERVED_5_TARG_EA]};
        };
        rand_addr_q.push_back(targ_addr);
        std::randomize(targ_addr) with {
            targ_addr inside {[`SYS_CFG_RESERVED_0_TARG_SA : `SYS_CFG_RESERVED_0_TARG_EA]};
        };
        rand_addr_q.push_back(targ_addr);
        std::randomize(targ_addr) with {
            targ_addr inside {[`SYS_CFG_RESERVED_1_TARG_SA : `SYS_CFG_RESERVED_1_TARG_EA]};
        };
        rand_addr_q.push_back(targ_addr);
    end //}
  endtask : gen_axi_addrs //}

  // *****************************************************************************************
  // Task to get the required INIT from CLI +Args
  // *****************************************************************************************
  task get_init_from_ext_args();
    if($test$plusargs("ALL_INITS"))
      for(int i=e_aic_0_init_lt; i<=e_pve_1_init_ht; i++) 
        get_init_q.push_back(i);
    
    if($test$plusargs("ALL_LT_INITS")) 
      for(int i=e_aic_0_init_lt; i<=e_soc_periph_init_lt; i++) 
        get_init_q.push_back(i);

    if($test$plusargs("ALL_MT_INITS")) 
      for(int i=e_dcd_dec_0_init_mt; i<=e_pcie_init_mt; i++) 
        get_init_q.push_back(i);

    if($test$plusargs("ALL_HT_INITS")) 
      for(int i=e_aic_0_init_ht; i<=e_pve_1_init_ht; i++) 
        get_init_q.push_back(i);
        
    if($test$plusargs("AIC_0_INIT_LT")) 
        get_init_q.push_back(e_aic_0_init_lt);

    if($test$plusargs("AIC_1_INIT_LT")) 
        get_init_q.push_back(e_aic_1_init_lt);

    if($test$plusargs("AIC_2_INIT_LT")) 
        get_init_q.push_back(e_aic_2_init_lt);

    if($test$plusargs("AIC_3_INIT_LT")) 
        get_init_q.push_back(e_aic_3_init_lt);

    if($test$plusargs("AIC_4_INIT_LT")) 
        get_init_q.push_back(e_aic_4_init_lt);

    if($test$plusargs("AIC_5_INIT_LT")) 
        get_init_q.push_back(e_aic_5_init_lt);

    if($test$plusargs("AIC_6_INIT_LT")) 
        get_init_q.push_back(e_aic_6_init_lt);

    if($test$plusargs("AIC_7_INIT_LT")) 
        get_init_q.push_back(e_aic_7_init_lt);

    if($test$plusargs("SDMA_0_INIT_LT")) 
        get_init_q.push_back(e_sdma_0_init_lt);

    if($test$plusargs("SDMA_1_INIT_LT")) 
        get_init_q.push_back(e_sdma_1_init_lt);

    if($test$plusargs("PVE_0_INIT_LT")) 
        get_init_q.push_back(e_pve_0_init_lt);

    if($test$plusargs("PVE_1_INIT_LT")) 
        get_init_q.push_back(e_pve_1_init_lt);

    if($test$plusargs("APU_INIT_LT")) 
        get_init_q.push_back(e_apu_init_lt);

    if($test$plusargs("SOC_MGMT_INIT_LT")) 
        get_init_q.push_back(e_soc_mgmt_init_lt);

    if($test$plusargs("SOC_PERIPH_INIT_LT")) 
        get_init_q.push_back(e_soc_periph_init_lt);

    if($test$plusargs("DCD_DEC_0_INIT_MT")) 
        get_init_q.push_back(e_dcd_dec_0_init_mt);

    if($test$plusargs("DCD_DEC_1_INIT_MT")) 
        get_init_q.push_back(e_dcd_dec_1_init_mt);

    if($test$plusargs("DCD_DEC_2_INIT_MT")) 
        get_init_q.push_back(e_dcd_dec_2_init_mt);

    if($test$plusargs("DCD_MCU_INIT_LT")) 
        get_init_q.push_back(e_dcd_mcu_init_lt);

    if($test$plusargs("APU_INIT_MT")) 
        get_init_q.push_back(e_apu_init_mt);

    if($test$plusargs("PCIE_INIT_MT")) 
        get_init_q.push_back(e_pcie_init_mt);

    if($test$plusargs("AIC_0_INIT_HT")) 
        get_init_q.push_back(e_aic_0_init_ht);

    if($test$plusargs("AIC_1_INIT_HT")) 
        get_init_q.push_back(e_aic_1_init_ht);

    if($test$plusargs("AIC_2_INIT_HT")) 
        get_init_q.push_back(e_aic_2_init_ht);

    if($test$plusargs("AIC_3_INIT_HT")) 
        get_init_q.push_back(e_aic_3_init_ht);

    if($test$plusargs("AIC_4_INIT_HT")) 
        get_init_q.push_back(e_aic_4_init_ht);

    if($test$plusargs("AIC_5_INIT_HT")) 
        get_init_q.push_back(e_aic_5_init_ht);

    if($test$plusargs("AIC_6_INIT_HT")) 
        get_init_q.push_back(e_aic_6_init_ht);

    if($test$plusargs("AIC_7_INIT_HT")) 
        get_init_q.push_back(e_aic_7_init_ht);

    if($test$plusargs("SDMA_0_INIT_HT_0")) 
        get_init_q.push_back(e_sdma_0_init_ht_0);

    if($test$plusargs("SDMA_0_INIT_HT_1")) 
        get_init_q.push_back(e_sdma_0_init_ht_1);

    if($test$plusargs("SDMA_1_INIT_HT_0")) 
        get_init_q.push_back(e_sdma_1_init_ht_0);

    if($test$plusargs("SDMA_1_INIT_HT_1")) 
        get_init_q.push_back(e_sdma_1_init_ht_1);

    if($test$plusargs("PVE_0_INIT_HT")) 
        get_init_q.push_back(e_pve_0_init_ht);

    if($test$plusargs("PVE_1_INIT_HT")) 
        get_init_q.push_back(e_pve_1_init_ht);
    
  endtask : get_init_from_ext_args
  // *****************************************************************************************
  // Task to check connectivity matrix and generate UVM_ERROR if fails
  // *****************************************************************************************
  function void chk_conn_matrix(input svt_axi_master_transaction req); //{
    if(req != null) begin //{
      if(((req.addr >=  `RESERVED_0_TARG_SA) && 
        (req.addr <=  `RESERVED_0_TARG_EA))  ||
        ((req.addr >= `RESERVED_1_TARG_SA)  && 
        (req.addr <=  `RESERVED_1_TARG_EA))  ||
        ((req.addr >= `RESERVED_2_TARG_SA)  && 
        (req.addr <=  `RESERVED_2_TARG_EA))  ||
        ((req.addr >= `RESERVED_3_TARG_SA)  && 
        (req.addr <=  `RESERVED_3_TARG_EA))  ||
        ((req.addr >= `RESERVED_4_TARG_SA)  && 
        (req.addr <=  `RESERVED_4_TARG_EA))  ||
        ((req.addr >= `RESERVED_5_TARG_SA)  && 
        (req.addr <=  `RESERVED_5_TARG_EA))) begin //{ TODO: also add sys_cfg_rsvd
        if(req.transmitted_channel == svt_axi_master_transaction::WRITE &&
           req.bresp == svt_axi_master_transaction::OKAY) begin //{
          `uvm_error ("ENOC", " RSVD_MEM_CHECK : RSVD_MEM is accessible and received OKAY while Writing")
          `uvm_info  ("ENOC", $sformatf("INIT[%d]: Addr : 40'h%h BRESP : %d", req.port_id, req.addr, req.bresp), UVM_LOW)
        end //}
        else if(req.transmitted_channel == svt_axi_master_transaction::READ &&
                req.rresp[0] == svt_axi_master_transaction::OKAY) begin //{
          `uvm_error ("ENOC", " RSVD_MEM_CHECK : RSVD_MEM is accessible and received OKAY while Reading")
          `uvm_info  ("ENOC", $sformatf("INIT[%d]: Addr : 40'h%h RRESP[0] : %d", req.port_id, req.addr, req.rresp[0]), UVM_LOW)
        end //}
      end //}
      else
        foreach(connectivity[i_init, i_targ]) begin //{
            if(i_init == req.port_id && i_targ == find_target(req.addr)) begin //{
              if(req.transmitted_channel == svt_axi_master_transaction::WRITE) begin //{
                if((connectivity[i_init][i_targ] == 1)  &&
                   req.bresp == svt_axi_master_transaction::OKAY) begin //{
                  `uvm_info  ("CONN_MATRIX_CHECK", $sformatf("INIT:%s TARG:%s Addr : 40'h%h BRESP : %s", i_init, i_targ, req.addr, req.bresp), UVM_LOW)
                end //}
                else if((connectivity[i_init][i_targ] == 0)  &&
                   req.bresp != svt_axi_master_transaction::OKAY) begin //{ 
                  `uvm_info  ("CONN_MATRIX_CHECK", $sformatf("INIT:%s TARG:%s Addr : 40'h%h BRESP : %s", i_init, i_targ, req.addr, req.bresp), UVM_LOW)
                end // }
                else begin //{ 
                  `uvm_error("CONN_MATRIX_CHECK", $sformatf(" CHECK CONNECTION BETWEEN INIT:%s TARG:%s FOR Addr: 40'h%h WHICH RECEIVED BRESP: %s ", i_init, i_targ, req.addr, req.bresp))
                end // }
              end //}
              if(req.transmitted_channel == svt_axi_master_transaction::READ) begin //{ TODO: chk for rresp[i]
                 if((connectivity[i_init][i_targ] == 1)  &&
                 req.rresp[0] == svt_axi_master_transaction::OKAY) begin //{
                  `uvm_info  ("CONN_MATRIX_CHECK", $sformatf("INIT:%s TARG:%s Addr : 40'h%h RRESP[0] : %s", i_init, i_targ, req.addr, req.rresp[0]), UVM_LOW)
                end //} 
                else if((connectivity[i_init][i_targ] == 0)  &&
                 req.rresp[0] != svt_axi_master_transaction::OKAY)begin //{
                  `uvm_info  ("CONN_MATRIX_CHECK", $sformatf("INIT:%s TARG:%s Addr : 40'h%h RRESP[0] : %s", i_init, i_targ, req.addr, req.rresp[0]), UVM_LOW)
                end //}
                else begin //{
                  `uvm_error("CONN_MATRIX_CHECK", $sformatf(" CHECK CONNECTION BETWEEN INIT:%s TARG:%s FOR Addr: 40'h%h WHICH RECEIVED RRESP[0] : %s", i_init, i_targ, req.addr, req.rresp[0]))
                end //}
             end //}
          end //}
        end //}
    end //}
    else
      `uvm_info  ("CONN_MATRIX_CHK", $sformatf("REQ ARE ALWAYS NULL"), UVM_LOW)
  endfunction : chk_conn_matrix //}

  function enoc_all_targs_e find_target(bit [`AXI_HP_ADDR_WIDTH-1 :0] addr); //{
    if (addr >= `APU_TARG_SA && addr < `APU_TARG_EA)
      return   cc_apu_targ_lt;
    else if (addr >= `SOC_MGMT_TARG_SA && addr < `SOC_MGMT_TARG_EA)
      return   cc_soc_mgmt_targ_lt;
    else if (addr >= `SOC_PERIPH_TARG_SA && addr < `SOC_PERIPH_TARG_EA)
      return   cc_soc_periph_targ_lt;
    else if (addr >= `PCIE_DBI_TARG_SA && addr < `PCIE_DBI_TARG_EA)
      return   cc_pcie_targ_cfg_dbi;
    else if (addr >= `NOC_INT_TARG_SA && addr < `NOC_INT_TARG_EA)
      return   cc_noc_csr_targ_int;
    else if (addr >= `SDMA_0_TARG_SA && addr < `SDMA_0_TARG_EA)
      return   cc_sdma_0_targ_lt;
    else if (addr >= `SDMA_1_TARG_SA && addr < `SDMA_1_TARG_EA)
      return   cc_sdma_1_targ_lt;
    else if (addr >= `SYS_SPM_TARG_SA && addr < `SYS_SPM_TARG_EA)
      return   cc_sys_spm_targ_lt;
    else if (addr >= `L2_MODULE_0_TARG_SA && addr < `L2_MODULE_0_TARG_EA)
      return   cc_l2_0_targ_ht;
    else if (addr >= `L2_MODULE_1_TARG_SA && addr < `L2_MODULE_1_TARG_EA)
      return   cc_l2_1_targ_ht;
    else if (addr >= `L2_MODULE_2_TARG_SA && addr < `L2_MODULE_2_TARG_EA)
      return   cc_l2_2_targ_ht;
    else if (addr >= `L2_MODULE_3_TARG_SA && addr < `L2_MODULE_3_TARG_EA)
      return   cc_l2_3_targ_ht;
    else if (addr >= `L2_MODULE_4_TARG_SA && addr < `L2_MODULE_4_TARG_EA)
      return   cc_l2_4_targ_ht;
    else if (addr >= `L2_MODULE_5_TARG_SA && addr < `L2_MODULE_5_TARG_EA)
      return   cc_l2_5_targ_ht;
    else if (addr >= `L2_MODULE_6_TARG_SA && addr < `L2_MODULE_6_TARG_EA)
      return   cc_l2_6_targ_ht;
    else if (addr >= `L2_MODULE_7_TARG_SA && addr < `L2_MODULE_7_TARG_EA)
      return   cc_l2_7_targ_ht;
    else if (addr >= `AICORE_0_TARG_SA && addr < `AICORE_0_TARG_EA)
      return   cc_aic_0_targ_lt;
    else if (addr >= `AICORE_1_TARG_SA && addr < `AICORE_1_TARG_EA)
      return   cc_aic_1_targ_lt;
    else if (addr >= `AICORE_2_TARG_SA && addr < `AICORE_2_TARG_EA)
      return   cc_aic_2_targ_lt;
    else if (addr >= `AICORE_3_TARG_SA && addr < `AICORE_3_TARG_EA)
      return   cc_aic_3_targ_lt;
    else if (addr >= `AICORE_4_TARG_SA && addr < `AICORE_4_TARG_EA)
      return   cc_aic_4_targ_lt;
    else if (addr >= `AICORE_5_TARG_SA && addr < `AICORE_5_TARG_EA)
      return   cc_aic_5_targ_lt;
    else if (addr >= `AICORE_6_TARG_SA && addr < `AICORE_6_TARG_EA)
      return   cc_aic_6_targ_lt;
    else if (addr >= `AICORE_7_TARG_SA && addr < `AICORE_7_TARG_EA)
      return   cc_aic_7_targ_lt;
    else if (addr >= `PVE_0_TARG_SA && addr < `PVE_0_TARG_EA)
      return   cc_pve_0_targ_lt;
    else if (addr >= `PVE_1_TARG_SA && addr < `PVE_1_TARG_EA)
      return   cc_pve_1_targ_lt;
    else if (addr >= `DDR_0_GRAPH_TARG_SA && addr < `DDR_0_GRAPH_TARG_EA)
      return   cc_lpddr_graph_0_targ_mt;                                  //TODO:also include other ddrs
    else if (addr >= `DDR_1_PPP_TARG_SA && addr < `DDR_1_PPP_TARG_EA)
      return   cc_lpddr_ppp_0_targ_ht;                                     //TODO:also include other ddrs
    else if (addr >= `PCIE_HOST_MT_TARG_SA && addr < `PCIE_HOST_MT_TARG_EA)
      return   cc_pcie_targ_mt;
    else if (addr >= `DCD_CFG_TARG_SA && addr < `DCD_CFG_TARG_EA)
      return   cc_dcd_targ_cfg;
    else if (addr >= `DDR_0_CTRL_GRAPH_0_CFG_TARG_SA && addr < `DDR_0_CTRL_GRAPH_0_CFG_TARG_EA)
      return   cc_lpddr_graph_0_targ_cfg;
    else if (addr >= `DDR_1_CTRL_GRAPH_1_CFG_TARG_SA && addr < `DDR_1_CTRL_GRAPH_1_CFG_TARG_EA)
      return   cc_lpddr_graph_1_targ_cfg;
    else if (addr >= `DDR_2_CTRL_GRAPH_2_CFG_TARG_SA && addr < `DDR_2_CTRL_GRAPH_2_CFG_TARG_EA)
      return   cc_lpddr_graph_2_targ_cfg;
    else if (addr >= `DDR_3_CTRL_GRAPH_3_CFG_TARG_SA && addr < `DDR_3_CTRL_GRAPH_3_CFG_TARG_EA)
      return   cc_lpddr_graph_3_targ_cfg;
    else if (addr >= `DDR_4_CTRL_PPP_0_CFG_TARG_SA && addr < `DDR_4_CTRL_PPP_0_CFG_TARG_EA)
      return   cc_lpddr_ppp_0_targ_cfg;
    else if (addr >= `DDR_5_CTRL_PPP_1_CFG_TARG_SA && addr < `DDR_5_CTRL_PPP_1_CFG_TARG_EA)
      return   cc_lpddr_ppp_1_targ_cfg;
    else if (addr >= `DDR_6_CTRL_PPP_2_CFG_TARG_SA && addr < `DDR_6_CTRL_PPP_2_CFG_TARG_EA)
      return   cc_lpddr_ppp_2_targ_cfg;
    else if (addr >= `DDR_7_CTRL_PPP_3_CFG_TARG_SA && addr < `DDR_7_CTRL_PPP_3_CFG_TARG_EA)
      return   cc_lpddr_ppp_3_targ_cfg;
    else if (addr >= `PCIE_CFG_TARG_SA && addr < `PCIE_CFG_TARG_EA)
      return   cc_pcie_targ_cfg;
    else if (addr >= `SYS_CFG_AICORE_0_AO_CSR_TARG_SA && addr < `SYS_CFG_AICORE_0_AO_CSR_TARG_EA)
      return   cc_aic_0_targ_syscfg;
    else if (addr >= `SYS_CFG_AICORE_1_AO_CSR_TARG_SA && addr < `SYS_CFG_AICORE_1_AO_CSR_TARG_EA)
      return   cc_aic_1_targ_syscfg;
    else if (addr >= `SYS_CFG_AICORE_2_AO_CSR_TARG_SA && addr < `SYS_CFG_AICORE_2_AO_CSR_TARG_EA)
      return   cc_aic_2_targ_syscfg;
    else if (addr >= `SYS_CFG_AICORE_3_AO_CSR_TARG_SA && addr < `SYS_CFG_AICORE_3_AO_CSR_TARG_EA)
      return   cc_aic_3_targ_syscfg;
    else if (addr >= `SYS_CFG_AICORE_4_AO_CSR_TARG_SA && addr < `SYS_CFG_AICORE_4_AO_CSR_TARG_EA)
      return   cc_aic_4_targ_syscfg;  
    else if (addr >= `SYS_CFG_AICORE_5_AO_CSR_TARG_SA && addr < `SYS_CFG_AICORE_5_AO_CSR_TARG_EA)
      return   cc_aic_5_targ_syscfg;
    else if (addr >= `SYS_CFG_AICORE_6_AO_CSR_TARG_SA && addr < `SYS_CFG_AICORE_6_AO_CSR_TARG_EA)
      return   cc_aic_6_targ_syscfg;
    else if (addr >= `SYS_CFG_AICORE_7_AO_CSR_TARG_SA && addr < `SYS_CFG_AICORE_7_AO_CSR_TARG_EA)
      return   cc_aic_7_targ_syscfg;
    else if (addr >= `SYS_CFG_L2_MODULE_0_AO_CSR_TARG_SA && addr < `SYS_CFG_L2_MODULE_0_AO_CSR_TARG_EA)
      return   cc_l2_0_targ_syscfg;
    else if (addr >= `SYS_CFG_L2_MODULE_1_AO_CSR_TARG_SA && addr < `SYS_CFG_L2_MODULE_1_AO_CSR_TARG_EA)
      return   cc_l2_1_targ_syscfg;
    else if (addr >= `SYS_CFG_L2_MODULE_2_AO_CSR_TARG_SA && addr < `SYS_CFG_L2_MODULE_2_AO_CSR_TARG_EA)
      return   cc_l2_2_targ_syscfg;
    else if (addr >= `SYS_CFG_L2_MODULE_3_AO_CSR_TARG_SA && addr < `SYS_CFG_L2_MODULE_3_AO_CSR_TARG_EA)
      return   cc_l2_3_targ_syscfg;
    else if (addr >= `SYS_CFG_L2_MODULE_4_AO_CSR_TARG_SA && addr < `SYS_CFG_L2_MODULE_4_AO_CSR_TARG_EA)
      return   cc_l2_4_targ_syscfg;
    else if (addr >= `SYS_CFG_L2_MODULE_5_AO_CSR_TARG_SA && addr < `SYS_CFG_L2_MODULE_5_AO_CSR_TARG_EA)
      return   cc_l2_5_targ_syscfg;
    else if (addr >= `SYS_CFG_L2_MODULE_6_AO_CSR_TARG_SA && addr < `SYS_CFG_L2_MODULE_6_AO_CSR_TARG_EA)
      return   cc_l2_6_targ_syscfg;
    else if (addr >= `SYS_CFG_L2_MODULE_7_AO_CSR_TARG_SA && addr < `SYS_CFG_L2_MODULE_7_AO_CSR_TARG_EA)
      return   cc_l2_7_targ_syscfg;
    else if (addr >= `SYS_CFG_DDR_0_GRAPH_0_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_0_GRAPH_0_AO_CSR_TARG_EA)
      return   cc_lpddr_graph_0_targ_syscfg;
    else if (addr >= `SYS_CFG_DDR_1_GRAPH_1_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_1_GRAPH_1_AO_CSR_TARG_EA)
      return   cc_lpddr_graph_1_targ_syscfg;
    else if (addr >= `SYS_CFG_DDR_2_GRAPH_2_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_2_GRAPH_2_AO_CSR_TARG_EA)
      return   cc_lpddr_graph_2_targ_syscfg;
    else if (addr >= `SYS_CFG_DDR_3_GRAPH_3_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_3_GRAPH_3_AO_CSR_TARG_EA)
      return   cc_lpddr_graph_3_targ_syscfg;
    else if (addr >= `SYS_CFG_DDR_4_PPP_0_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_4_PPP_0_AO_CSR_TARG_EA)
      return   cc_lpddr_ppp_0_targ_syscfg;
    else if (addr >= `SYS_CFG_DDR_5_PPP_1_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_5_PPP_1_AO_CSR_TARG_EA)
      return   cc_lpddr_ppp_1_targ_syscfg;
    else if (addr >= `SYS_CFG_DDR_6_PPP_2_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_6_PPP_2_AO_CSR_TARG_EA)
      return   cc_lpddr_ppp_2_targ_syscfg;
    else if (addr >= `SYS_CFG_DDR_7_PPP_3_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_7_PPP_3_AO_CSR_TARG_EA)
      return   cc_lpddr_ppp_3_targ_syscfg;
    else if (addr >= `SYS_CFG_SYS_SPM_AO_CSR_TARG_SA && addr < `SYS_CFG_SYS_SPM_AO_CSR_TARG_EA)
      return   cc_sys_spm_targ_syscfg;
    else if (addr >= `SYS_CFG_APU_AO_CSR_TARG_SA && addr < `SYS_CFG_APU_AO_CSR_TARG_EA)
      return   cc_apu_targ_syscfg;
    //else if (addr >= `SYS_CFG_DDR_WEST_PLL_AO_CSR_TARG_SA && addr < `SYS_CFG_DDR_WEST_PLL_AO_CSR_TARG_EA)
    //  return   cc_lpddr_graph_0_targ_syscfg                                                               //TODO:CHK WHICH TO MAP
    else if (addr >= `SYS_CFG_SOC_PERIPH_AO_CSR_TARG_SA && addr < `SYS_CFG_SOC_PERIPH_AO_CSR_TARG_EA)
      return   cc_soc_periph_targ_syscfg;
    else if (addr >= `SYS_CFG_SDMA_0_AO_CSR_TARG_SA && addr < `SYS_CFG_SDMA_0_AO_CSR_TARG_EA)
      return   cc_sdma_0_targ_syscfg;
    else if (addr >= `SYS_CFG_SDMA_1_AO_CSR_TARG_SA && addr < `SYS_CFG_SDMA_1_AO_CSR_TARG_EA)
      return   cc_sdma_1_targ_syscfg;
    else if (addr >= `SYS_CFG_PCIE_AO_CSR_TARG_SA && addr < `SYS_CFG_PCIE_AO_CSR_TARG_EA)
      return   cc_pcie_targ_syscfg;
    else if (addr >= `SYS_CFG_DECODER_AO_CSR_TARG_SA && addr < `SYS_CFG_DECODER_AO_CSR_TARG_EA)
      return   cc_dcd_targ_syscfg;
    else if (addr >= `SYS_CFG_PVE_0_AO_CSR_TARG_SA && addr < `SYS_CFG_PVE_0_AO_CSR_TARG_EA)
      return   cc_pve_0_syscfg_lt;
    else if (addr >= `SYS_CFG_PVE_1_AO_CSR_TARG_SA && addr < `SYS_CFG_PVE_1_AO_CSR_TARG_EA)
      return   cc_pve_1_syscfg_lt;
    else if (addr >= `SYS_CFG_SOC_MGMT_CLOCK_GEN_TARG_SA && addr < `SYS_CFG_SOC_MGMT_CLOCK_GEN_TARG_EA)
      return   cc_soc_mgmt_targ_syscfg;
    else if (addr >= `SYS_CFG_SOC_MGMT_RESET_GEN_TARG_SA && addr < `SYS_CFG_SOC_MGMT_RESET_GEN_TARG_EA)
      return   cc_soc_mgmt_targ_syscfg;
    else if (addr >= `SYS_CFG_SOC_MGMT_NOC_AO_CSR_TARG_SA && addr < `SYS_CFG_SOC_MGMT_NOC_AO_CSR_TARG_EA)
      return   cc_soc_mgmt_targ_syscfg;
    else if (addr >= `SYS_CFG_SOC_MGMT_AO_CSR_TARG_SA && addr < `SYS_CFG_SOC_MGMT_AO_CSR_TARG_EA)
      return   cc_soc_mgmt_targ_syscfg;
    else 
      `uvm_info("TARGET CHECK", $sformatf("NO TARGET MAPPED for address: %h", addr), UVM_LOW)
    
  endfunction : find_target //}

// *****************************************************************************************
  // Initialize the array with 'b1' for valid connections
  // *****************************************************************************************
  task initialize_conn_matrix(); //{
    connectivity[e_aic_0_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_0_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_1_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_2_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_3_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_4_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_5_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_6_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_7_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_pcie_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_apu_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_0]           [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_pcie_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_apu_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_0]           [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_pcie_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_apu_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_ht_1]           [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_pcie_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_apu_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_ht_1]           [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_pve_0_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_pve_1_init_ht]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_apu_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_pcie_init_mt]               [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_apu_init_mt]                [cc_pcie_targ_mt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_apu_init_mt]                [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_apu_init_mt]                [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_pcie_targ_mt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_apu_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_dcd_dec_0_init_mt]          [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_pcie_targ_mt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_apu_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_dcd_dec_1_init_mt]          [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_pcie_targ_mt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_apu_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_dcd_dec_2_init_mt]          [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_aic_0_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_aic_1_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_aic_2_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_aic_3_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_aic_4_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_aic_5_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_aic_6_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_aic_7_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_pcie_targ_mt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_apu_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_sdma_0_init_lt]             [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_pcie_targ_mt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_apu_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_sdma_1_init_lt]             [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_pve_0_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_pcie_targ_mt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_apu_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_pve_1_init_lt]              [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_pcie_targ_mt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_apu_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_dcd_mcu_init_lt]            [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_apu_init_lt]                [cc_pcie_targ_mt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_apu_init_lt]                [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_apu_init_lt]                [cc_noc_csr_targ_int] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_pcie_targ_mt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_apu_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_soc_periph_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_sys_spm_targ_syscfg] = 'b1;
    connectivity[e_soc_mgmt_init_lt]           [cc_noc_csr_targ_int] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_0_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_1_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_2_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_3_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_4_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_5_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_6_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_7_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_0_targ_mt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_1_targ_mt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_2_targ_mt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_3_targ_mt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_0_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_1_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_2_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_3_targ_ht] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_pcie_targ_mt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_0_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_1_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_2_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_3_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_4_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_5_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_6_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_7_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_sdma_0_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_sdma_1_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_pve_0_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_pve_1_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_apu_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_dcd_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_soc_mgmt_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_sys_spm_targ_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_0_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_1_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_2_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_3_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_0_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_1_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_2_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_3_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_pcie_targ_cfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_pcie_targ_cfg_dbi] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_0_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_1_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_2_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_3_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_4_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_5_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_6_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_aic_7_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_0_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_1_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_2_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_3_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_4_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_5_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_6_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_l2_7_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_0_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_1_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_2_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_graph_3_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_0_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_1_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_2_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_lpddr_ppp_3_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_pcie_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_pve_0_syscfg_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_pve_1_syscfg_lt] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_apu_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_dcd_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_sdma_0_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_sdma_1_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_soc_mgmt_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_soc_periph_targ_syscfg] = 'b1;
    connectivity[e_soc_periph_init_lt]         [cc_sys_spm_targ_syscfg] = 'b1;

  endtask : initialize_conn_matrix //}

  // *****************************************************************************************
  // Function to identify the rand_addr mapped to any TARG
  // *****************************************************************************************
  function void check_address(bit [`AXI_HP_ADDR_WIDTH-1 :0] address); //{
  
      if (address >= 40'h00000000 && address <= 40'h0000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00010000 && address <= 40'h0001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_BOOTROM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00020000 && address <= 40'h0002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_CSRS mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00030000 && address <= 40'h0003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00040000 && address <= 40'h0004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00050000 && address <= 40'h0005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_PVT mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00060000 && address <= 40'h0006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_PLMT mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00070000 && address <= 40'h003FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00400000 && address <= 40'h007FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00800000 && address <= 40'h00BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_SW_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h00C00000 && address <= 40'h01FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("APU_RESERVED_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h02000000 && address <= 40'h0203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_ROT mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h02040000 && address <= 40'h0204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_OTP_HOST mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h02050000 && address <= 40'h0205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_TMS mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h02060000 && address <= 40'h0206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_CLOCK_GEN mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h02070000 && address <= 40'h0207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_RESET_GEN mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h02080000 && address <= 40'h0208FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_RTC mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h02090000 && address <= 40'h0209FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_WATCHDOG mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h020A0000 && address <= 40'h020AFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_DEBUG mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h020B0000 && address <= 40'h020BFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_MBIST mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h020C0000 && address <= 40'h020CFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_TRACE_BUF mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h020D0000 && address <= 40'h02FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_MGMT_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03000000 && address <= 40'h0300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_PAD_CTRL mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03010000 && address <= 40'h0301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_I2C_0 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03020000 && address <= 40'h0302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_I2C_1 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03030000 && address <= 40'h0303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_GPIO mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03040000 && address <= 40'h0304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_SPI mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03050000 && address <= 40'h0305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_EMMC mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03060000 && address <= 40'h0306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_UART mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03070000 && address <= 40'h0307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_TIMER mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h03080000 && address <= 40'h03FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SOC_PERIPH_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h04000000 && address <= 40'h043FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PCIE_DBI_SLAVE mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h04400000 && address <= 40'h0443FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PCIE_PHY_CFG mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h04440000 && address <= 40'h0444FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("NOC_SERVICE mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h04450000 && address <= 40'h0445FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("NOC_OBSERVER mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h04460000 && address <= 40'h04FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("NOC_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05000000 && address <= 40'h0500FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_AICORE_0_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05010000 && address <= 40'h0501FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_AICORE_1_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05020000 && address <= 40'h0502FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_AICORE_2_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05030000 && address <= 40'h0503FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_AICORE_3_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05040000 && address <= 40'h0504FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_AICORE_4_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05050000 && address <= 40'h0505FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_AICORE_5_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05060000 && address <= 40'h0506FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_AICORE_6_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05070000 && address <= 40'h0507FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_AICORE_7_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05080000 && address <= 40'h0508FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_L2_MODULE_0_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05090000 && address <= 40'h0509FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_L2_MODULE_1_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h050A0000 && address <= 40'h050AFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_L2_MODULE_2_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h050B0000 && address <= 40'h050BFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_L2_MODULE_3_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h050C0000 && address <= 40'h050CFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_L2_MODULE_4_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h050D0000 && address <= 40'h050DFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_L2_MODULE_5_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h050E0000 && address <= 40'h050EFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_L2_MODULE_6_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h050F0000 && address <= 40'h050FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_L2_MODULE_7_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05100000 && address <= 40'h0510FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DDR_0_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05110000 && address <= 40'h0511FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DDR_1_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05120000 && address <= 40'h0512FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DDR_2_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05130000 && address <= 40'h0513FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DDR_3_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05140000 && address <= 40'h0514FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DDR_4_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05150000 && address <= 40'h0515FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DDR_5_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05160000 && address <= 40'h0516FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DDR_6_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05170000 && address <= 40'h0517FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DDR_7_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05180000 && address <= 40'h0518FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_SYS_SPM_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05190000 && address <= 40'h0519FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_APU_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h051A0000 && address <= 40'h051AFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_SOC_MGMT_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h051B0000 && address <= 40'h051BFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_SOC_PERIPH_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h051C0000 && address <= 40'h051CFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_SDMA_0_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h051D0000 && address <= 40'h051DFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_SDMA_1_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h051E0000 && address <= 40'h051EFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_PCIE_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h051F0000 && address <= 40'h051FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_DECODER_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05200000 && address <= 40'h0520FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_PVE_0_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05210000 && address <= 40'h0521FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_PVE_1_AO_CSR mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h05220000 && address <= 40'h05FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_CFG_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h06000000 && address <= 40'h0603FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SDMA_0_DMA_INTERNAL mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h06040000 && address <= 40'h0607FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SDMA_1_DMA_INTERNAL mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h06080000 && address <= 40'h06FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h07000000 && address <= 40'h077FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("SYS_SPM mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h07800000 && address <= 40'h07FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h08000000 && address <= 40'h08FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("L2_MODULE_0 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h09000000 && address <= 40'h09FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("L2_MODULE_1 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h0A000000 && address <= 40'h0AFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("L2_MODULE_2 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h0B000000 && address <= 40'h0BFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("L2_MODULE_3 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h0C000000 && address <= 40'h0CFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("L2_MODULE_4 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h0D000000 && address <= 40'h0DFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("L2_MODULE_5 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h0E000000 && address <= 40'h0EFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("L2_MODULE_6 mapped for address: %h", address), UVM_LOW)
      end
  
  
  
      if (address >= 40'h0F000000 && address <= 40'h0FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("L2_MODULE_7 mapped for address: %h", address), UVM_LOW)
      end
  
      if (address >= 40'h10000000 && address <= 40'h1000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10010000 && address <= 40'h1001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10020000 && address <= 40'h1002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_CSR_INFRA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10030000 && address <= 40'h1003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_CSR_MID mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10040000 && address <= 40'h1004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10050000 && address <= 40'h1005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10060000 && address <= 40'h1006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10070000 && address <= 40'h1007FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10080000 && address <= 40'h1008FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_PMU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h10090000 && address <= 40'h10FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_PERIPHERALS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h11000000 && address <= 40'h1100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_CONTROL_ACD_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h11010000 && address <= 40'h1101FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_CONTROL_ACD_COMMAND mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h11020000 && address <= 40'h1102FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_CONTROL_LP_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h11030000 && address <= 40'h11FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_CONFIGURATION_CONTROL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12000000 && address <= 40'h1200FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12010000 && address <= 40'h1201FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12020000 && address <= 40'h1202FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12030000 && address <= 40'h1203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12040000 && address <= 40'h1204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12050000 && address <= 40'h1205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12060000 && address <= 40'h1206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12070000 && address <= 40'h1207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12080000 && address <= 40'h121FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12200000 && address <= 40'h1220FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12210000 && address <= 40'h1221FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12220000 && address <= 40'h1222FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12230000 && address <= 40'h1223FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12240000 && address <= 40'h123FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12400000 && address <= 40'h1240FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12410000 && address <= 40'h1241FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12420000 && address <= 40'h1242FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12430000 && address <= 40'h125FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12600000 && address <= 40'h1260FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12610000 && address <= 40'h1261FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12620000 && address <= 40'h1262FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12630000 && address <= 40'h127FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_CSR_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12800000 && address <= 40'h1280FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12810000 && address <= 40'h1281FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12820000 && address <= 40'h1282FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12830000 && address <= 40'h1283FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12840000 && address <= 40'h1284FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12850000 && address <= 40'h1285FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12860000 && address <= 40'h1286FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12870000 && address <= 40'h1287FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12880000 && address <= 40'h129FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12A00000 && address <= 40'h12A0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12A10000 && address <= 40'h12A1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12A20000 && address <= 40'h12A2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12A30000 && address <= 40'h12A3FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12A40000 && address <= 40'h12BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12C00000 && address <= 40'h12C0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12C10000 && address <= 40'h12C1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12C20000 && address <= 40'h12C2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12C30000 && address <= 40'h12DFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12E00000 && address <= 40'h12E0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12E10000 && address <= 40'h12E1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12E20000 && address <= 40'h12E2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h12E30000 && address <= 40'h12FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_COMMAND_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13000000 && address <= 40'h1300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13010000 && address <= 40'h1301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13020000 && address <= 40'h1302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13030000 && address <= 40'h1303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13040000 && address <= 40'h1304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13050000 && address <= 40'h1305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13060000 && address <= 40'h1306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13070000 && address <= 40'h1307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13080000 && address <= 40'h131FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13200000 && address <= 40'h1320FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13210000 && address <= 40'h1321FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13220000 && address <= 40'h1322FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13230000 && address <= 40'h1323FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13240000 && address <= 40'h133FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13400000 && address <= 40'h1340FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13410000 && address <= 40'h1341FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13420000 && address <= 40'h1342FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13430000 && address <= 40'h135FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13600000 && address <= 40'h1360FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13610000 && address <= 40'h1361FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13620000 && address <= 40'h1362FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13630000 && address <= 40'h137FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_INSTRUCTIONS_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h13800000 && address <= 40'h13FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_DATAPATH_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h14000000 && address <= 40'h1407FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h14080000 && address <= 40'h17FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h18000000 && address <= 40'h183FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_L1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h18400000 && address <= 40'h1FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_0_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20000000 && address <= 40'h2000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20010000 && address <= 40'h2001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20020000 && address <= 40'h2002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_CSR_INFRA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20030000 && address <= 40'h2003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_CSR_MID mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20040000 && address <= 40'h2004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20050000 && address <= 40'h2005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20060000 && address <= 40'h2006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20070000 && address <= 40'h2007FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20080000 && address <= 40'h2008FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_PMU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h20090000 && address <= 40'h20FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_PERIPHERALS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h21000000 && address <= 40'h2100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_CONTROL_ACD_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h21010000 && address <= 40'h2101FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_CONTROL_ACD_COMMAND mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h21020000 && address <= 40'h2102FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_CONTROL_LP_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h21030000 && address <= 40'h21FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_CONFIGURATION_CONTROL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22000000 && address <= 40'h2200FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22010000 && address <= 40'h2201FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22020000 && address <= 40'h2202FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22030000 && address <= 40'h2203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22040000 && address <= 40'h2204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22050000 && address <= 40'h2205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22060000 && address <= 40'h2206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22070000 && address <= 40'h2207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22080000 && address <= 40'h221FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22200000 && address <= 40'h2220FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22210000 && address <= 40'h2221FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22220000 && address <= 40'h2222FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22230000 && address <= 40'h2223FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22240000 && address <= 40'h223FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22400000 && address <= 40'h2240FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22410000 && address <= 40'h2241FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22420000 && address <= 40'h2242FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22430000 && address <= 40'h225FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22600000 && address <= 40'h2260FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22610000 && address <= 40'h2261FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22620000 && address <= 40'h2262FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22630000 && address <= 40'h227FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_CSR_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22800000 && address <= 40'h2280FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22810000 && address <= 40'h2281FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22820000 && address <= 40'h2282FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22830000 && address <= 40'h2283FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22840000 && address <= 40'h2284FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22850000 && address <= 40'h2285FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22860000 && address <= 40'h2286FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22870000 && address <= 40'h2287FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22880000 && address <= 40'h229FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22A00000 && address <= 40'h22A0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22A10000 && address <= 40'h22A1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22A20000 && address <= 40'h22A2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22A30000 && address <= 40'h22A3FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22A40000 && address <= 40'h22BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22C00000 && address <= 40'h22C0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22C10000 && address <= 40'h22C1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22C20000 && address <= 40'h22C2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22C30000 && address <= 40'h22DFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22E00000 && address <= 40'h22E0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22E10000 && address <= 40'h22E1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22E20000 && address <= 40'h22E2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h22E30000 && address <= 40'h22FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_COMMAND_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23000000 && address <= 40'h2300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23010000 && address <= 40'h2301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23020000 && address <= 40'h2302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23030000 && address <= 40'h2303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23040000 && address <= 40'h2304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23050000 && address <= 40'h2305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23060000 && address <= 40'h2306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23070000 && address <= 40'h2307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23080000 && address <= 40'h231FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23200000 && address <= 40'h2320FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23210000 && address <= 40'h2321FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23220000 && address <= 40'h2322FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23230000 && address <= 40'h2323FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23240000 && address <= 40'h233FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23400000 && address <= 40'h2340FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23410000 && address <= 40'h2341FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23420000 && address <= 40'h2342FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23430000 && address <= 40'h235FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23600000 && address <= 40'h2360FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23610000 && address <= 40'h2361FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23620000 && address <= 40'h2362FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23630000 && address <= 40'h237FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_INSTRUCTIONS_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h23800000 && address <= 40'h23FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_DATAPATH_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h24000000 && address <= 40'h2407FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h24080000 && address <= 40'h27FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h28000000 && address <= 40'h283FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_L1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h28400000 && address <= 40'h2FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_1_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30000000 && address <= 40'h3000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30010000 && address <= 40'h3001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30020000 && address <= 40'h3002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_CSR_INFRA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30030000 && address <= 40'h3003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_CSR_MID mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30040000 && address <= 40'h3004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30050000 && address <= 40'h3005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30060000 && address <= 40'h3006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30070000 && address <= 40'h3007FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30080000 && address <= 40'h3008FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_PMU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h30090000 && address <= 40'h30FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_PERIPHERALS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h31000000 && address <= 40'h3100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_CONTROL_ACD_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h31010000 && address <= 40'h3101FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_CONTROL_ACD_COMMAND mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h31020000 && address <= 40'h3102FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_CONTROL_LP_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h31030000 && address <= 40'h31FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_CONFIGURATION_CONTROL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32000000 && address <= 40'h3200FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32010000 && address <= 40'h3201FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32020000 && address <= 40'h3202FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32030000 && address <= 40'h3203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32040000 && address <= 40'h3204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32050000 && address <= 40'h3205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32060000 && address <= 40'h3206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32070000 && address <= 40'h3207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32080000 && address <= 40'h321FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32200000 && address <= 40'h3220FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32210000 && address <= 40'h3221FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32220000 && address <= 40'h3222FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32230000 && address <= 40'h3223FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32240000 && address <= 40'h323FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32400000 && address <= 40'h3240FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32410000 && address <= 40'h3241FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32420000 && address <= 40'h3242FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32430000 && address <= 40'h325FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32600000 && address <= 40'h3260FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32610000 && address <= 40'h3261FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32620000 && address <= 40'h3262FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32630000 && address <= 40'h327FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_CSR_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32800000 && address <= 40'h3280FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32810000 && address <= 40'h3281FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32820000 && address <= 40'h3282FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32830000 && address <= 40'h3283FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32840000 && address <= 40'h3284FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32850000 && address <= 40'h3285FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32860000 && address <= 40'h3286FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32870000 && address <= 40'h3287FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32880000 && address <= 40'h329FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32A00000 && address <= 40'h32A0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32A10000 && address <= 40'h32A1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32A20000 && address <= 40'h32A2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32A30000 && address <= 40'h32A3FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32A40000 && address <= 40'h32BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32C00000 && address <= 40'h32C0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32C10000 && address <= 40'h32C1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32C20000 && address <= 40'h32C2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32C30000 && address <= 40'h32DFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32E00000 && address <= 40'h32E0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32E10000 && address <= 40'h32E1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32E20000 && address <= 40'h32E2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h32E30000 && address <= 40'h32FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_COMMAND_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33000000 && address <= 40'h3300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33010000 && address <= 40'h3301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33020000 && address <= 40'h3302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33030000 && address <= 40'h3303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33040000 && address <= 40'h3304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33050000 && address <= 40'h3305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33060000 && address <= 40'h3306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33070000 && address <= 40'h3307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33080000 && address <= 40'h331FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33200000 && address <= 40'h3320FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33210000 && address <= 40'h3321FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33220000 && address <= 40'h3322FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33230000 && address <= 40'h3323FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33240000 && address <= 40'h333FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33400000 && address <= 40'h3340FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33410000 && address <= 40'h3341FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33420000 && address <= 40'h3342FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33430000 && address <= 40'h335FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33600000 && address <= 40'h3360FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33610000 && address <= 40'h3361FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33620000 && address <= 40'h3362FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33630000 && address <= 40'h337FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_INSTRUCTIONS_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h33800000 && address <= 40'h33FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_DATAPATH_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h34000000 && address <= 40'h3407FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h34080000 && address <= 40'h37FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h38000000 && address <= 40'h383FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_L1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h38400000 && address <= 40'h3FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_2_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40000000 && address <= 40'h4000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40010000 && address <= 40'h4001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40020000 && address <= 40'h4002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_CSR_INFRA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40030000 && address <= 40'h4003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_CSR_MID mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40040000 && address <= 40'h4004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40050000 && address <= 40'h4005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40060000 && address <= 40'h4006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40070000 && address <= 40'h4007FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40080000 && address <= 40'h4008FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_PMU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h40090000 && address <= 40'h40FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_PERIPHERALS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h41000000 && address <= 40'h4100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_CONTROL_ACD_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h41010000 && address <= 40'h4101FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_CONTROL_ACD_COMMAND mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h41020000 && address <= 40'h4102FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_CONTROL_LP_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h41030000 && address <= 40'h41FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_CONFIGURATION_CONTROL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42000000 && address <= 40'h4200FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42010000 && address <= 40'h4201FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42020000 && address <= 40'h4202FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42030000 && address <= 40'h4203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42040000 && address <= 40'h4204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42050000 && address <= 40'h4205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42060000 && address <= 40'h4206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42070000 && address <= 40'h4207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42080000 && address <= 40'h421FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42200000 && address <= 40'h4220FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42210000 && address <= 40'h4221FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42220000 && address <= 40'h4222FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42230000 && address <= 40'h4223FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42240000 && address <= 40'h423FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42400000 && address <= 40'h4240FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42410000 && address <= 40'h4241FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42420000 && address <= 40'h4242FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42430000 && address <= 40'h425FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42600000 && address <= 40'h4260FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42610000 && address <= 40'h4261FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42620000 && address <= 40'h4262FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42630000 && address <= 40'h427FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_CSR_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42800000 && address <= 40'h4280FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42810000 && address <= 40'h4281FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42820000 && address <= 40'h4282FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42830000 && address <= 40'h4283FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42840000 && address <= 40'h4284FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42850000 && address <= 40'h4285FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42860000 && address <= 40'h4286FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42870000 && address <= 40'h4287FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42880000 && address <= 40'h429FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42A00000 && address <= 40'h42A0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42A10000 && address <= 40'h42A1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42A20000 && address <= 40'h42A2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42A30000 && address <= 40'h42A3FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42A40000 && address <= 40'h42BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42C00000 && address <= 40'h42C0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42C10000 && address <= 40'h42C1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42C20000 && address <= 40'h42C2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42C30000 && address <= 40'h42DFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42E00000 && address <= 40'h42E0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42E10000 && address <= 40'h42E1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42E20000 && address <= 40'h42E2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h42E30000 && address <= 40'h42FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_COMMAND_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43000000 && address <= 40'h4300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43010000 && address <= 40'h4301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43020000 && address <= 40'h4302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43030000 && address <= 40'h4303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43040000 && address <= 40'h4304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43050000 && address <= 40'h4305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43060000 && address <= 40'h4306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43070000 && address <= 40'h4307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43080000 && address <= 40'h431FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43200000 && address <= 40'h4320FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43210000 && address <= 40'h4321FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43220000 && address <= 40'h4322FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43230000 && address <= 40'h4323FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43240000 && address <= 40'h433FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43400000 && address <= 40'h4340FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43410000 && address <= 40'h4341FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43420000 && address <= 40'h4342FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43430000 && address <= 40'h435FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43600000 && address <= 40'h4360FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43610000 && address <= 40'h4361FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43620000 && address <= 40'h4362FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43630000 && address <= 40'h437FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_INSTRUCTIONS_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h43800000 && address <= 40'h43FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_DATAPATH_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h44000000 && address <= 40'h4407FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h44080000 && address <= 40'h47FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h48000000 && address <= 40'h483FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_L1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h48400000 && address <= 40'h4FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_3_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50000000 && address <= 40'h5000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50010000 && address <= 40'h5001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50020000 && address <= 40'h5002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_CSR_INFRA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50030000 && address <= 40'h5003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_CSR_MID mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50040000 && address <= 40'h5004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50050000 && address <= 40'h5005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50060000 && address <= 40'h5006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50070000 && address <= 40'h5007FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50080000 && address <= 40'h5008FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_PMU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h50090000 && address <= 40'h50FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_PERIPHERALS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h51000000 && address <= 40'h5100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_CONTROL_ACD_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h51010000 && address <= 40'h5101FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_CONTROL_ACD_COMMAND mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h51020000 && address <= 40'h5102FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_CONTROL_LP_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h51030000 && address <= 40'h51FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_CONFIGURATION_CONTROL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52000000 && address <= 40'h5200FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52010000 && address <= 40'h5201FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52020000 && address <= 40'h5202FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52030000 && address <= 40'h5203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52040000 && address <= 40'h5204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52050000 && address <= 40'h5205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52060000 && address <= 40'h5206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52070000 && address <= 40'h5207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52080000 && address <= 40'h521FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52200000 && address <= 40'h5220FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52210000 && address <= 40'h5221FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52220000 && address <= 40'h5222FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52230000 && address <= 40'h5223FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52240000 && address <= 40'h523FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52400000 && address <= 40'h5240FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52410000 && address <= 40'h5241FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52420000 && address <= 40'h5242FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52430000 && address <= 40'h525FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52600000 && address <= 40'h5260FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52610000 && address <= 40'h5261FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52620000 && address <= 40'h5262FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52630000 && address <= 40'h527FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_CSR_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52800000 && address <= 40'h5280FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52810000 && address <= 40'h5281FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52820000 && address <= 40'h5282FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52830000 && address <= 40'h5283FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52840000 && address <= 40'h5284FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52850000 && address <= 40'h5285FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52860000 && address <= 40'h5286FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52870000 && address <= 40'h5287FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52880000 && address <= 40'h529FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52A00000 && address <= 40'h52A0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52A10000 && address <= 40'h52A1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52A20000 && address <= 40'h52A2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52A30000 && address <= 40'h52A3FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52A40000 && address <= 40'h52BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52C00000 && address <= 40'h52C0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52C10000 && address <= 40'h52C1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52C20000 && address <= 40'h52C2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52C30000 && address <= 40'h52DFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52E00000 && address <= 40'h52E0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52E10000 && address <= 40'h52E1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52E20000 && address <= 40'h52E2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h52E30000 && address <= 40'h52FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_COMMAND_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53000000 && address <= 40'h5300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53010000 && address <= 40'h5301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53020000 && address <= 40'h5302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53030000 && address <= 40'h5303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53040000 && address <= 40'h5304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53050000 && address <= 40'h5305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53060000 && address <= 40'h5306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53070000 && address <= 40'h5307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53080000 && address <= 40'h531FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53200000 && address <= 40'h5320FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53210000 && address <= 40'h5321FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53220000 && address <= 40'h5322FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53230000 && address <= 40'h5323FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53240000 && address <= 40'h533FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53400000 && address <= 40'h5340FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53410000 && address <= 40'h5341FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53420000 && address <= 40'h5342FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53430000 && address <= 40'h535FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53600000 && address <= 40'h5360FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53610000 && address <= 40'h5361FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53620000 && address <= 40'h5362FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53630000 && address <= 40'h537FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_INSTRUCTIONS_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h53800000 && address <= 40'h53FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_DATAPATH_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h54000000 && address <= 40'h5407FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h54080000 && address <= 40'h57FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h58000000 && address <= 40'h583FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_L1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h58400000 && address <= 40'h5FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_4_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60000000 && address <= 40'h6000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60010000 && address <= 40'h6001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60020000 && address <= 40'h6002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_CSR_INFRA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60030000 && address <= 40'h6003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_CSR_MID mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60040000 && address <= 40'h6004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60050000 && address <= 40'h6005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60060000 && address <= 40'h6006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60070000 && address <= 40'h6007FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60080000 && address <= 40'h6008FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_PMU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h60090000 && address <= 40'h60FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_PERIPHERALS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h61000000 && address <= 40'h6100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_CONTROL_ACD_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h61010000 && address <= 40'h6101FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_CONTROL_ACD_COMMAND mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h61020000 && address <= 40'h6102FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_CONTROL_LP_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h61030000 && address <= 40'h61FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_CONFIGURATION_CONTROL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62000000 && address <= 40'h6200FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62010000 && address <= 40'h6201FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62020000 && address <= 40'h6202FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62030000 && address <= 40'h6203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62040000 && address <= 40'h6204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62050000 && address <= 40'h6205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62060000 && address <= 40'h6206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62070000 && address <= 40'h6207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62080000 && address <= 40'h621FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62200000 && address <= 40'h6220FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62210000 && address <= 40'h6221FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62220000 && address <= 40'h6222FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62230000 && address <= 40'h6223FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62240000 && address <= 40'h623FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62400000 && address <= 40'h6240FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62410000 && address <= 40'h6241FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62420000 && address <= 40'h6242FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62430000 && address <= 40'h625FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62600000 && address <= 40'h6260FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62610000 && address <= 40'h6261FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62620000 && address <= 40'h6262FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62630000 && address <= 40'h627FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_CSR_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62800000 && address <= 40'h6280FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62810000 && address <= 40'h6281FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62820000 && address <= 40'h6282FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62830000 && address <= 40'h6283FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62840000 && address <= 40'h6284FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62850000 && address <= 40'h6285FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62860000 && address <= 40'h6286FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62870000 && address <= 40'h6287FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62880000 && address <= 40'h629FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62A00000 && address <= 40'h62A0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62A10000 && address <= 40'h62A1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62A20000 && address <= 40'h62A2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62A30000 && address <= 40'h62A3FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62A40000 && address <= 40'h62BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62C00000 && address <= 40'h62C0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62C10000 && address <= 40'h62C1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62C20000 && address <= 40'h62C2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62C30000 && address <= 40'h62DFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62E00000 && address <= 40'h62E0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62E10000 && address <= 40'h62E1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62E20000 && address <= 40'h62E2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h62E30000 && address <= 40'h62FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_COMMAND_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63000000 && address <= 40'h6300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63010000 && address <= 40'h6301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63020000 && address <= 40'h6302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63030000 && address <= 40'h6303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63040000 && address <= 40'h6304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63050000 && address <= 40'h6305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63060000 && address <= 40'h6306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63070000 && address <= 40'h6307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63080000 && address <= 40'h631FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63200000 && address <= 40'h6320FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63210000 && address <= 40'h6321FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63220000 && address <= 40'h6322FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63230000 && address <= 40'h6323FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63240000 && address <= 40'h633FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63400000 && address <= 40'h6340FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63410000 && address <= 40'h6341FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63420000 && address <= 40'h6342FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63430000 && address <= 40'h635FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63600000 && address <= 40'h6360FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63610000 && address <= 40'h6361FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63620000 && address <= 40'h6362FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63630000 && address <= 40'h637FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_INSTRUCTIONS_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h63800000 && address <= 40'h63FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_DATAPATH_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h64000000 && address <= 40'h6407FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h64080000 && address <= 40'h67FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h68000000 && address <= 40'h683FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_L1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h68400000 && address <= 40'h6FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_5_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70000000 && address <= 40'h7000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70010000 && address <= 40'h7001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70020000 && address <= 40'h7002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_CSR_INFRA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70030000 && address <= 40'h7003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_CSR_MID mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70040000 && address <= 40'h7004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70050000 && address <= 40'h7005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70060000 && address <= 40'h7006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70070000 && address <= 40'h7007FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70080000 && address <= 40'h7008FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_PMU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h70090000 && address <= 40'h70FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_PERIPHERALS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h71000000 && address <= 40'h7100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_CONTROL_ACD_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h71010000 && address <= 40'h7101FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_CONTROL_ACD_COMMAND mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h71020000 && address <= 40'h7102FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_CONTROL_LP_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h71030000 && address <= 40'h71FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_CONFIGURATION_CONTROL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72000000 && address <= 40'h7200FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72010000 && address <= 40'h7201FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72020000 && address <= 40'h7202FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72030000 && address <= 40'h7203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72040000 && address <= 40'h7204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72050000 && address <= 40'h7205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72060000 && address <= 40'h7206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72070000 && address <= 40'h7207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72080000 && address <= 40'h721FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72200000 && address <= 40'h7220FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72210000 && address <= 40'h7221FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72220000 && address <= 40'h7222FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72230000 && address <= 40'h7223FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72240000 && address <= 40'h723FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72400000 && address <= 40'h7240FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72410000 && address <= 40'h7241FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72420000 && address <= 40'h7242FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72430000 && address <= 40'h725FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72600000 && address <= 40'h7260FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72610000 && address <= 40'h7261FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72620000 && address <= 40'h7262FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72630000 && address <= 40'h727FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_CSR_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72800000 && address <= 40'h7280FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72810000 && address <= 40'h7281FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72820000 && address <= 40'h7282FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72830000 && address <= 40'h7283FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72840000 && address <= 40'h7284FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72850000 && address <= 40'h7285FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72860000 && address <= 40'h7286FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72870000 && address <= 40'h7287FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72880000 && address <= 40'h729FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72A00000 && address <= 40'h72A0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72A10000 && address <= 40'h72A1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72A20000 && address <= 40'h72A2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72A30000 && address <= 40'h72A3FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72A40000 && address <= 40'h72BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72C00000 && address <= 40'h72C0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72C10000 && address <= 40'h72C1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72C20000 && address <= 40'h72C2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72C30000 && address <= 40'h72DFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72E00000 && address <= 40'h72E0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72E10000 && address <= 40'h72E1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72E20000 && address <= 40'h72E2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h72E30000 && address <= 40'h72FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_COMMAND_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73000000 && address <= 40'h7300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73010000 && address <= 40'h7301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73020000 && address <= 40'h7302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73030000 && address <= 40'h7303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73040000 && address <= 40'h7304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73050000 && address <= 40'h7305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73060000 && address <= 40'h7306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73070000 && address <= 40'h7307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73080000 && address <= 40'h731FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73200000 && address <= 40'h7320FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73210000 && address <= 40'h7321FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73220000 && address <= 40'h7322FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73230000 && address <= 40'h7323FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73240000 && address <= 40'h733FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73400000 && address <= 40'h7340FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73410000 && address <= 40'h7341FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73420000 && address <= 40'h7342FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73430000 && address <= 40'h735FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73600000 && address <= 40'h7360FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73610000 && address <= 40'h7361FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73620000 && address <= 40'h7362FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73630000 && address <= 40'h737FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_INSTRUCTIONS_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h73800000 && address <= 40'h73FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_DATAPATH_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h74000000 && address <= 40'h7407FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h74080000 && address <= 40'h77FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h78000000 && address <= 40'h783FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_L1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h78400000 && address <= 40'h7FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_6_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80000000 && address <= 40'h8000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_MAILBOX mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80010000 && address <= 40'h8001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_TOKEN_MANAGER mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80020000 && address <= 40'h8002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_CSR_INFRA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80030000 && address <= 40'h8003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_CSR_MID mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80040000 && address <= 40'h8004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80050000 && address <= 40'h8005FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80060000 && address <= 40'h8006FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_PLIC mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80070000 && address <= 40'h8007FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80080000 && address <= 40'h8008FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_PMU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h80090000 && address <= 40'h80FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_PERIPHERALS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h81000000 && address <= 40'h8100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_CONTROL_ACD_CSR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h81010000 && address <= 40'h8101FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_CONTROL_ACD_COMMAND mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h81020000 && address <= 40'h8102FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_CONTROL_LP_DMA mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h81030000 && address <= 40'h81FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_CONFIGURATION_CONTROL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82000000 && address <= 40'h8200FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82010000 && address <= 40'h8201FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82020000 && address <= 40'h8202FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82030000 && address <= 40'h8203FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82040000 && address <= 40'h8204FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82050000 && address <= 40'h8205FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82060000 && address <= 40'h8206FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82070000 && address <= 40'h8207FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82080000 && address <= 40'h821FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82200000 && address <= 40'h8220FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82210000 && address <= 40'h8221FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82220000 && address <= 40'h8222FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82230000 && address <= 40'h8223FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82240000 && address <= 40'h823FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82400000 && address <= 40'h8240FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82410000 && address <= 40'h8241FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82420000 && address <= 40'h8242FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82430000 && address <= 40'h825FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82600000 && address <= 40'h8260FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82610000 && address <= 40'h8261FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82620000 && address <= 40'h8262FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82630000 && address <= 40'h827FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_CSR_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82800000 && address <= 40'h8280FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82810000 && address <= 40'h8281FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82820000 && address <= 40'h8282FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82830000 && address <= 40'h8283FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82840000 && address <= 40'h8284FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82850000 && address <= 40'h8285FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82860000 && address <= 40'h8286FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82870000 && address <= 40'h8287FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82880000 && address <= 40'h829FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82A00000 && address <= 40'h82A0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82A10000 && address <= 40'h82A1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82A20000 && address <= 40'h82A2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82A30000 && address <= 40'h82A3FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82A40000 && address <= 40'h82BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82C00000 && address <= 40'h82C0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82C10000 && address <= 40'h82C1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82C20000 && address <= 40'h82C2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82C30000 && address <= 40'h82DFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82E00000 && address <= 40'h82E0FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82E10000 && address <= 40'h82E1FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82E20000 && address <= 40'h82E2FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h82E30000 && address <= 40'h82FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_COMMAND_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83000000 && address <= 40'h8300FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_M_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83010000 && address <= 40'h8301FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_M_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83020000 && address <= 40'h8302FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_M_IFD_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83030000 && address <= 40'h8303FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_M_IFD_W mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83040000 && address <= 40'h8304FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_M_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83050000 && address <= 40'h8305FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_D_IFD_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83060000 && address <= 40'h8306FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_D_IFD_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83070000 && address <= 40'h8307FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_D_ODR mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83080000 && address <= 40'h831FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_LS_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83200000 && address <= 40'h8320FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_MID_M_MVMEXE mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83210000 && address <= 40'h8321FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_MID_M_MVMPRG mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83220000 && address <= 40'h8322FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_MID_M_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83230000 && address <= 40'h8323FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_MID_M_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83240000 && address <= 40'h833FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_MID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83400000 && address <= 40'h8340FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_DID_D_DWPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83410000 && address <= 40'h8341FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_DID_D_IAU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83420000 && address <= 40'h8342FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_DID_D_DPU mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83430000 && address <= 40'h835FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_DID_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83600000 && address <= 40'h8360FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83610000 && address <= 40'h8361FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_DMA_HP_DMA_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83620000 && address <= 40'h8362FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_DMA_LEGACY mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83630000 && address <= 40'h837FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_INSTRUCTIONS_DMA_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h83800000 && address <= 40'h83FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_DATAPATH_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h84000000 && address <= 40'h8407FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h84080000 && address <= 40'h87FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h88000000 && address <= 40'h883FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_L1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h88400000 && address <= 40'h8FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("AICORE_7_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h90000000 && address <= 40'h9000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_DMA0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h90010000 && address <= 40'h9001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_DMA1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h90020000 && address <= 40'h9002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_CLINT mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h90030000 && address <= 40'h9003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_PERF_COUNTERS mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h90040000 && address <= 40'h9004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h90050000 && address <= 40'h93FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h94000000 && address <= 40'h9403FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h94040000 && address <= 40'h97FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h98000000 && address <= 40'h983FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_L1_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h98400000 && address <= 40'h987FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_L1_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h98800000 && address <= 40'h98BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_L1_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h98C00000 && address <= 40'h98FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_L1_3 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h99000000 && address <= 40'h9FFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_0_RESERVED_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA0000000 && address <= 40'hA000FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_DMA0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA0010000 && address <= 40'hA001FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_DMA1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA0020000 && address <= 40'hA002FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_CLINT mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA0030000 && address <= 40'hA003FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_PERF_COUNTERS mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA0040000 && address <= 40'hA004FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_TRACE_IP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA0050000 && address <= 40'hA3FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_RESERVED_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA4000000 && address <= 40'hA403FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_SPM mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA4040000 && address <= 40'hA7FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_RESERVED_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA8000000 && address <= 40'hA83FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_L1_0 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA8400000 && address <= 40'hA87FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_L1_1 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA8800000 && address <= 40'hA8BFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_L1_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA8C00000 && address <= 40'hA8FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_L1_3 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hA9000000 && address <= 40'hAFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("PVE_1_RESERVED_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hB0000000 && address <= 40'hB00FFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DECODER_DECODER_INTERNAL mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hB0100000 && address <= 40'hBFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("RESERVED_2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'hC0000000 && address <= 40'hFFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("RESERVED_3 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h100000000 && address <= 40'h100FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_0_CTRL_PHY_PUB mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h101000000 && address <= 40'h10100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_0_CTRL_UMCTL2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h101010000 && address <= 40'h1FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_0_CTRL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h200000000 && address <= 40'h200FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_1_CTRL_PHY_PUB mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h201000000 && address <= 40'h20100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_1_CTRL_UMCTL2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h201010000 && address <= 40'h2FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_1_CTRL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h300000000 && address <= 40'h300FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_2_CTRL_PHY_PUB mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h301000000 && address <= 40'h30100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_2_CTRL_UMCTL2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h301010000 && address <= 40'h3FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_2_CTRL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h400000000 && address <= 40'h400FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_3_CTRL_PHY_PUB mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h401000000 && address <= 40'h40100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_3_CTRL_UMCTL2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h401010000 && address <= 40'h4FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_3_CTRL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h500000000 && address <= 40'h500FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_4_CTRL_PHY_PUB mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h501000000 && address <= 40'h50100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_4_CTRL_UMCTL2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h501010000 && address <= 40'h5FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_4_CTRL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h600000000 && address <= 40'h600FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_5_CTRL_PHY_PUB mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h601000000 && address <= 40'h60100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_5_CTRL_UMCTL2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h601010000 && address <= 40'h6FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_5_CTRL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h700000000 && address <= 40'h700FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_6_CTRL_PHY_PUB mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h701000000 && address <= 40'h70100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_6_CTRL_UMCTL2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h701010000 && address <= 40'h7FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_6_CTRL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h800000000 && address <= 40'h800FFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_7_CTRL_PHY_PUB mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h801000000 && address <= 40'h80100FFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_7_CTRL_UMCTL2 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h801010000 && address <= 40'h8FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_7_CTRL_RESERVED mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h900000000 && address <= 40'h1FFFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("RESERVED_4 mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h2000000000 && address <= 40'h27FFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_0 GRAPH mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h2800000000 && address <= 40'h2FFFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("DDR_1 PPP mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h3000000000 && address <= 40'h3FFFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("HOST mapped for address: %h", address), UVM_LOW)
      end
      
      if (address >= 40'h4000000000 && address <= 40'hFFFFFFFFFF) begin
          `uvm_info("ADDRESS_CHECK", $sformatf("RESERVED_5 mapped for address: %h", address), UVM_LOW)
      end
      
  endfunction //}

  // *****************************************************************************************
  // Calculate the pass or fail status for the test in the final phase method of the
  // test. If a UVM_FATAL, UVM_ERROR, or a UVM_WARNING message has been generated the
  // test will fail.
  // *****************************************************************************************
   function void final_phase(uvm_phase phase);
     uvm_report_server svr;
     `uvm_info("final_phase", "Entered...",UVM_LOW)

     super.final_phase(phase);

     svr = uvm_report_server::get_server();

     if (svr.get_severity_count(UVM_FATAL) +
         svr.get_severity_count(UVM_ERROR) 
         //+ svr.get_severity_count(UVM_WARNING) 
         > 0)
       `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
     else
       `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

     `uvm_info("final_phase", "Exiting...", UVM_LOW)
   endfunction: final_phase

endclass:enoc_base_test

`endif // GUARD_ENOC_BASE_TEST_SV

