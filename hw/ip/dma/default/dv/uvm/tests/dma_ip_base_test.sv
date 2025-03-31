`ifndef GUARD_DMA_IP_BASE_TEST_SV
`define GUARD_DMA_IP_BASE_TEST_SV
// DMA IP base test class
class dma_ip_base_test extends uvm_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(dma_ip_base_test)

   // Declare p sequencer
  // `uvm_declare_p_sequencer(axi_virtual_sequencer)

  // DMA IP RAL Model
  dma_ip_reg_block dma_ip_regmodel;
  
  /** Construct the report catcher extended class*/
//  dma_ip_report_demoter catcher = new();

  /** Instance of the environment */
  dma_ip_env env;

  /** Instance of the environment configuration */
  dma_ip_env_config m_env_cfg;

  /** Customized configuration */
  axi_vip_config axi_vip_cfg;
  
  // Means to Pass key information from TEST to SCBD (so checker can handle the various scenarios)
  dma_ip_transfer_details  test2scbd_details;

  /** Customized configCreator configuration handle */
  //cust_svt_axi_system_cc_configuration cc_cfg;
  uvm_status_e  status;

  // To Advance Time using CLK related Tasks (WAIT_N_CLKS etc)
  virtual clk_if  clk_vif;



  // --------------------------------------------------------------------
  // Control Knobs

  // USER DATA Pattern for Preloading AXI SLAVE AGENT MEMORIES
  bit [7:0] user_data_pattern = 8'haa;

  // CMDBLK Address Size
  bit [15:0]  cmdblk_region = 16'h0fff;
  
  // Address Starts for Per-Channel DMA CMB Blocks
  bit [19:0]  chan0_cmb_block_addr_start = 20'h2_0000;
  bit [19:0]  chan1_cmb_block_addr_start = 20'h2_2000;
  bit [19:0]  chan2_cmb_block_addr_start = 20'h2_4000;
  bit [19:0]  chan3_cmb_block_addr_start = 20'h2_6000;
  bit [19:0]  chan4_cmb_block_addr_start = 20'h2_8000;
  bit [19:0]  chan5_cmb_block_addr_start = 20'h2_a000;
  bit [19:0]  chan6_cmb_block_addr_start = 20'h2_c000;
  bit [19:0]  chan7_cmb_block_addr_start = 20'h2_e000;

  // --------------------------------------------------------------------

  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence  axi_rd_seq;

  dma_reg_types_enum   dma_register;             
	
	bit [63:0]  wdata;
	bit [63:0]  rdata;
	bit [63:0]  exp_data;

  bit [7:0]   backdoor_mem_wdata[];
  bit [7:0]   backdoor_mem_rdata[];

//  axi_slave_mem_response_sequence  axi_slave_stream_iau_base_seq;   TBD REMOVE ? not used via axi_slave_stream_iau_base_seq

  // mvm user Inteface Handle
//  virtual mvm_if mvm_if;


  // ------------------------------------------------------------------------
  // Tasks and Functions
  extern virtual task randomize_data(ref bit [63:0] data);

  extern virtual task DMA_REG_WRITE(dma_reg_types_enum regname, int which_channel=0, logic [63:0] wdata);
  extern virtual task DMA_REG_READ (dma_reg_types_enum regname, int which_channel=0, output logic [63:0] rdata);

  // AXI SLAVE AGENT Memories - BackDoor Tasks
  extern virtual task slvmem_bkdr_clear_all (int slv_id);
  extern virtual task slvmem_bkdr_preload_all (int slv_id, string preload_type);
  extern virtual task slvmem_bkdr_preload_range (int slv_id, string preload_type, bit [39:0] addr_start, bit [39:0] addr_end);
  extern virtual task slvmem_bkdr_write_byte (int slv_id, bit [39:0] addr, bit [7:0] data);
  extern virtual task slvmem_bkdr_write_num_byte (int slv_id, bit [39:0] addr, int num_of_bytes, bit [7:0] data[]);
  extern virtual task slvmem_bkdr_write_num_randbyte (int slv_id, bit [39:0] addr, int num_of_bytes);

  extern virtual task slvmem_bkdr_read_byte (int slv_id, bit [39:0] addr, ref bit [7:0] data);
  extern virtual task slvmem_bkdr_read_num_byte (int slv_id, bit [39:0] addr, int num_of_bytes, ref bit [7:0] data[]);
  extern virtual task slvmem_bkdr_read_range (int slv_id, bit [39:0] addr_start, bit [39:0] addr_end, ref bit [7:0] data[]);

  // ------------------------------------------------------------------------

  /** Class Constructor */
  function new(string name = "dma_ip_base_test", uvm_component parent=null);
    super.new(name,parent);
    uvm_top.set_timeout(5ms,1);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    /** Add uvm_report_cb callback */
//    uvm_report_cb::add(null, catcher);

    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded axi_vip_config ", UVM_LOW)

    /** Create the configuration object */
    axi_vip_cfg = axi_vip_config::type_id::create("axi_vip_cfg");

    /** Set configuration in environment */
    uvm_config_db#(axi_vip_config)::set(this, "env", "cfg", this.axi_vip_cfg);

    // Create the transfer details object and add it into conig DB for reference by SCBD
    test2scbd_details = dma_ip_transfer_details::type_id::create("test2scbd_details");
    uvm_config_db#(dma_ip_transfer_details)::set(this, "env.m_dma_transfer_scbd", "test2scbd_details", this.test2scbd_details);

    /** Create the configuration object for AI Core LS environment */
    m_env_cfg = dma_ip_env_config::type_id::create("m_env_cfg");
    /** Set configuration for AI Core MVM environment */
    uvm_config_db#(dma_ip_env_config)::set(this, "env", "m_env_cfg", this.m_env_cfg);

    /** Create the environment */
    env = dma_ip_env::type_id::create("env", this);

    // ----------------------------------------------------------------------------------------------------------------------------------------------------------------
    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */

    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    // TBD : random selection of slave response normal or zero delay sequence
//    randcase
//      1: begin uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_zero_delay_sequence::type_id::get()); end
//      1: begin uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get()); end
//    endcase
    // ----------------------------------------------------------------------------------------------------------------------------------------------------------------

    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");

    // Get Hanlde to CLK_IF
    if (!uvm_config_db#(virtual clk_if)::get(this,"*","dma_clk_vif", clk_vif))
    begin
        `uvm_fatal(get_type_name(),"No CLK VIF was pushed to config_db!")
    end

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase

  // Start of simulation phase
  function void start_of_simulation_phase (uvm_phase phase);
    // set cfg axi mst agent in config db to be retrieved by non uvm components like report catcher
    uvm_config_db#(svt_axi_master_agent)::set(null,"*", "CFG_AXI_MST_AGENT", env.axi_system_env.master[0]);
  endfunction: start_of_simulation_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
    uvm_top.print_topology();
    `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
  endfunction: end_of_elaboration_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    dma_ip_regmodel = env.dma_ip_regmodel;
  endfunction : connect_phase

  virtual task run_phase(uvm_phase phase);
    `uvm_info("base_test:run_phase", "Entered...", UVM_LOW)
   
    `uvm_info("base_test:run_phase", "Exiting...", UVM_LOW)
  endtask

  /**
   * Calculate the pass or fail status for the test in the final phase method of the
   * test. If a UVM_FATAL, UVM_ERROR, or a UVM_WARNING message has been generated the
   * test will fail.
   */
  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    `uvm_info("final_phase", "Entered...",UVM_LOW)

    super.final_phase(phase);

    svr = uvm_report_server::get_server();

    if (  svr.get_severity_count(UVM_FATAL) 
        + svr.get_severity_count(UVM_ERROR) 
//      + svr.get_severity_count(UVM_WARNING) > 0
       )
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_NONE)
  endfunction: final_phase

endclass:dma_ip_base_test

// ---------------------------------------------------------------------------------------------------------
// Task to generate random data

task dma_ip_base_test::randomize_data(ref bit [63:0] data);
  bit [63:0] i_data;
	
  if(!std::randomize(i_data)) `uvm_error(get_full_name(),$sformatf("UNABLE to RANDOMIZE i_data"));
	data = i_data;
endtask

// ---------------------------------------------------------------------------------------------------------
// Task to WRITE a(non-MMU) DMA Registers by name
// Contents of these tasks could be replaced by RAL WRITE/READ METHODS, without changing the calls to these tasks within the tests
// That is, keep the calls to these tasks but change the deatils inside it (if required)

task dma_ip_base_test::DMA_REG_WRITE(dma_reg_types_enum regname, int which_channel=0, logic [63:0] wdata);
  bit               use_ral_accesses;    // Set when using RAL Methods
  bit               use_direct_acceses;  // Set when NOT using RAL Methods and wish to use diect AXI-ADDRESS Accesses
  uvm_status_e      expected_uvm_status;
  uvm_status_e      status;

  bit [63:0]        reg_addr;
	resp_type_enum    expected_bresp;
  
  use_ral_accesses   = 1'b1;  // Use RAL Methods for the Register, unless unavailable
  use_direct_acceses = 1'b0;  // ANd not Drect AXI-ADDRESS accesses.
  
  case (regname)
    // GLOBAL (COMMON) REGISTERS
    DMA_CH_COMMON_MODE    : dma_ip_regmodel.m_dma_common_reg_block.ch_mode.write(status, wdata);
    DMA_CH_COMMON_STATUS  : dma_ip_regmodel.m_dma_common_reg_block.ch_status.write(status, wdata);

    // CMDBLK Registers - All Point to same FIFO.
    DMA_CH_CMDBLK_FIFO    : begin
    
                              // Choose which address to be used as the FIFO WRITE Address (typically 0 but any other address within range)
                              randcase
                                70 : reg_addr = '0;
                                30 : if (!std::randomize(reg_addr) with {reg_addr inside {[0:cmdblk_region]};
                                                                         reg_addr%8 == 0;                  })   // And a multiple of 8 as writes into FIFO Addr are 8-bytes aligned
                                       `uvm_error(get_full_name(),$sformatf("UNABLE to RANDOMIZE reg_addr"))
                              endcase
                              
                              // Add Base Address dependant upon channel being used
                              case (which_channel)
                                0 : reg_addr += chan0_cmb_block_addr_start;
                                1 : reg_addr += chan1_cmb_block_addr_start;
                                2 : reg_addr += chan2_cmb_block_addr_start;
                                3 : reg_addr += chan3_cmb_block_addr_start;
                                4 : reg_addr += chan4_cmb_block_addr_start;
                                5 : reg_addr += chan5_cmb_block_addr_start;
                                6 : reg_addr += chan6_cmb_block_addr_start;
                                7 : reg_addr += chan7_cmb_block_addr_start;
                              endcase
                              
                              // And since does not have a RAL Method defined, we use direct AXI-ADDRESS transactions
                              use_direct_acceses = 1'b1;  
                            end

    // CHANNEL REGISTER BLOCK
    DMA_CH_CMDBLK_CTRL    : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].cmdblk_ctrl.write(status, wdata);
    DMA_CH_CMDBLK_STATUS  : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].cmdblk_status.write(status, wdata);
    
    DMA_CH_IRQ_EN         : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_IRQ_STATUS     : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_SWDP_CTRL      : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_SWDP_STATUS    : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DP_CTRL        : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DP_STATUS      : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DBG_OBSERVE    : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_CMDGEN_STATUS  : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DBG_SCRATCH    : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DBG_ID         : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_HW_CAPABILITY  : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_CTRL      : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_STATE     : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_STALL     : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_STALL_IN  : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_STALL_OUT : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    
    DMA_CH_CTRL           : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_ctrl.write(status, wdata);
    DMA_CH_CFG            : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_cfg.write(status, wdata);
    DMA_CH_SRC_ADDR       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_src_addr.write(status, wdata);
    DMA_CH_DST_ADDR       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_dst_addr.write(status, wdata);
    DMA_CH_XBYTESIZE      : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_xbytesize.write(status, wdata);
    DMA_CH_YROWSIZE       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_yrowsize.write(status, wdata);
    DMA_CH_TRAN_CFG       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_tran_cfg.write(status, wdata);
    DMA_CH_XADDRINC       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_xaddrinc.write(status, wdata);
    DMA_CH_YADDRSTRIDE    : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_yaddrstride.write(status, wdata);
    DMA_CH_LINK_DESCR     : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_link_descr.write(status, wdata);
    DMA_CH_STATUS         : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_status.write(status, wdata);
    DMA_CH_ERR_INFO       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_err_info.write(status, wdata);
    DMA_CH_REQ_BUS_CTRL   : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_req_bus_ctrl.write(status, wdata);

    default :  `uvm_error(get_name, $sformatf("UNKNOWN Register defined for RAL Method [%s]", regname.name()))
  endcase

  // If Direct Register Accesses, issue it and check RESP
  // If RAL methid, then transaction as already been issued. So check its status
  
  if (use_direct_acceses) begin
    // Direct Register accesses using AXI_ADDR
    expected_bresp = OKAY;
    if (regname inside {DMA_CH_COMMON_STATUS, DMA_CH_STATUS, DMA_CH_ERR_INFO, DMA_CH_CMDBLK_STATUS}) begin
      expected_bresp = SLVERR; 
    end

    if (!axi_wr_seq.randomize() with {
      cfg_addr            == reg_addr;
      sequence_length     == 'd1;
      burst_size_enum_t   == BURST_SIZE_64BIT;
      burst_type_enum_t   == FIXED;
      burst_lenght_enum_t == BURST_LENGTH_1;
      cfg_data[0]         == wdata;
      exp_bresp_t         == expected_bresp;             // Expected Response to this transaction
    })
     `uvm_fatal(get_name, "axi_wr_seq : Randomization Failed!")
    
    `uvm_info(get_full_name(),$sformatf("Sending AXI-WRITE to ADDR : h%016h \t [Register %s Channel-%01d", reg_addr, regname.name(), which_channel), UVM_LOW)
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

  end
  else begin  
    // RAL Methods was used for Register Accesses (already instigated) ensure that the transaction completed as expected
    if (use_ral_accesses) begin
      expected_uvm_status = UVM_IS_OK;
      if (regname inside {DMA_CH_COMMON_STATUS, DMA_CH_STATUS, DMA_CH_ERR_INFO, DMA_CH_CMDBLK_STATUS}) begin
        expected_uvm_status = UVM_NOT_OK;
      end
      
      if (status != expected_uvm_status)
        `uvm_error(get_name, $sformatf("Incorrect uvm_status returned following RAL Write Method [EXP=%s. ACT=%s][%s]", expected_uvm_status.name(), status.name(), regname.name()))
    end
    else begin
      `uvm_error(get_name, $sformatf("RAL Methods currently not defined for [%s]", regname.name()))
    end
    
  end

endtask : DMA_REG_WRITE

// ---------------------------------------------------------------------------------------------------------
// Task to READ a(non-MMU) DMA Registers by name
// Contents of these tasks could be replaced by RAL WRITE/READ METHODS, without changing the calls to these tasks within the tests
// That is, keep the calls to these tasks but change the deatils inside it (if required)

task dma_ip_base_test::DMA_REG_READ(dma_reg_types_enum regname, int which_channel=0, output logic [63:0] rdata);
  bit               use_ral_accesses;    // Set when using RAL Methods
  bit               use_direct_acceses;  // Set when NOT using RAL Methods and wish to use diect AXI-ADDRESS Accesses
  uvm_status_e      expected_uvm_status;
  uvm_status_e      status;

  bit [63:0]  reg_addr;

  use_ral_accesses   = 1'b1;  // Use RAL Methods for the Register, unless unavailable
  use_direct_acceses = 1'b0;  // ANd not Drect AXI-ADDRESS accesses.
  
  case (regname)
    // GLOBAL (COMMON) REGISTERS
    DMA_CH_COMMON_MODE    : dma_ip_regmodel.m_dma_common_reg_block.ch_mode.read(status, rdata);
    DMA_CH_COMMON_STATUS  : dma_ip_regmodel.m_dma_common_reg_block.ch_status.read(status, rdata);

    // CMDBLK Registers - All Point to same FIFO. 
    DMA_CH_CMDBLK_FIFO    : begin
    
                              // Choose which address to be used as the FIFO WRITE Address (typically 0 but any other address within range)
                              randcase
                                70 : reg_addr = '0;
                                30 : if (!std::randomize(reg_addr) with {reg_addr inside {[0:cmdblk_region]};
                                                                         reg_addr%8 == 0;                  })   // And a multiple of 8 as writes into FIFO Addr are 8-bytes aligned
                                       `uvm_error(get_full_name(),$sformatf("UNABLE to RANDOMIZE reg_addr"))
                              endcase
                              
                              // Add Base Address dependant upon channel being used
                              case (which_channel)
                                0 : reg_addr += chan0_cmb_block_addr_start;
                                1 : reg_addr += chan1_cmb_block_addr_start;
                                2 : reg_addr += chan2_cmb_block_addr_start;
                                3 : reg_addr += chan3_cmb_block_addr_start;
                                4 : reg_addr += chan4_cmb_block_addr_start;
                                5 : reg_addr += chan5_cmb_block_addr_start;
                                6 : reg_addr += chan6_cmb_block_addr_start;
                                7 : reg_addr += chan7_cmb_block_addr_start;
                              endcase
                              
                              // And since does not have a RAL Method defined, we use direct AXI-ADDRESS transactions
                              use_direct_acceses = 1'b1;  
                            end

    // CHANNEL REGISTER BLOCK
    DMA_CH_CMDBLK_CTRL    : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].cmdblk_ctrl.read(status, rdata);
    DMA_CH_CMDBLK_STATUS  : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].cmdblk_status.read(status, rdata);
    
    DMA_CH_IRQ_EN         : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_IRQ_STATUS     : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_SWDP_CTRL      : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_SWDP_STATUS    : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DP_CTRL        : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DP_STATUS      : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DBG_OBSERVE    : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_CMDGEN_STATUS  : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DBG_SCRATCH    : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_DBG_ID         : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_HW_CAPABILITY  : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_CTRL      : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_STATE     : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_STALL     : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_STALL_IN  : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    DMA_CH_PERF_STALL_OUT : use_ral_accesses = 1'b0;   // TBD Waiting for this to be available in the RTL
    
    DMA_CH_CTRL           : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_ctrl.read(status, rdata);
    DMA_CH_CFG            : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_cfg.read(status, rdata);
    DMA_CH_SRC_ADDR       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_src_addr.read(status, rdata);
    DMA_CH_DST_ADDR       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_dst_addr.read(status, rdata);
    DMA_CH_XBYTESIZE      : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_xbytesize.read(status, rdata);
    DMA_CH_YROWSIZE       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_yrowsize.read(status, rdata);
    DMA_CH_TRAN_CFG       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_tran_cfg.read(status, rdata);
    DMA_CH_XADDRINC       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_xaddrinc.read(status, rdata);
    DMA_CH_YADDRSTRIDE    : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_yaddrstride.read(status, rdata);
    DMA_CH_LINK_DESCR     : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_link_descr.read(status, rdata);
    DMA_CH_STATUS         : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_status.read(status, rdata);
    DMA_CH_ERR_INFO       : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_err_info.read(status, rdata);
    DMA_CH_REQ_BUS_CTRL   : dma_ip_regmodel.m_dma_channel_reg_block[which_channel].ch_req_bus_ctrl.read(status, rdata);

    default :  `uvm_error(get_name, $sformatf("UNKNOWN Register defined for RAL Method [%s]", regname.name()))
  endcase

  // If Direct Register Accesses, issue it and check RESP
  // If RAL methid, then transaction as already been issued. So check its status
  
  if (use_direct_acceses) begin
    // Direct Register accesses using AXI_ADDR
    if (!axi_rd_seq.randomize() with {
      cfg_addr            == reg_addr;
      sequence_length     == 'd1;
      burst_size_enum_t   == BURST_SIZE_64BIT;
      burst_type_enum_t   == FIXED;
      burst_lenght_enum_t == BURST_LENGTH_1;
      exp_rresp_t         == OKAY;             // Expected Response to this transaction
    })
	   `uvm_fatal(get_name, "axi_rd_seq : Randomization Failed!")

    `uvm_info(get_full_name(),$sformatf("Sending AXI-READ  to ADDR : h%016h \t [Register %s Channel-%01d", reg_addr, regname.name(), which_channel), UVM_LOW)
	  axi_rd_seq.start(env.axi_system_env.master[0].sequencer);

    // Get the read-data following completion of AXI-READ
    rdata = axi_rd_seq.read_data[0];

  end
  else begin  
    // RAL Methods was used for Register Accesses (already instigated) ensure that the transaction completed as expected
    if (use_ral_accesses) begin
      expected_uvm_status = UVM_IS_OK;
      if (status != expected_uvm_status)
        `uvm_error(get_name, $sformatf("Incorrect uvm_status returned following RAL Read Method [EXP=%s. ACT=%s][%s]", expected_uvm_status.name(), status.name(), regname.name()))

      // Get the read-data following completion of AXI-READ
      rdata = rdata;

    end
    else begin
      `uvm_error(get_name, $sformatf("RAL Methods currently not defined for [%s]", regname.name()))
    end
    
  end

  `uvm_info(get_full_name(),$sformatf("READ-DATA=h%016h", rdata), UVM_LOW)
  
endtask : DMA_REG_READ


// ---------------------------------------------------------------------------------------------------------
// AXI SLAVE Memory Preloading Tasks
// Uses write byte methods already built into the svt_axi_slave_agent

// WRITE TASKS
// -----------

// Clears Entire AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
// NOT PRACTICAL to USE. For Memory of size 40-bits, this equates to 1,099,511,627,776 addresses to be indvidually preloaded
task dma_ip_base_test::slvmem_bkdr_clear_all (int slv_id);
  if (slv_id < axi_vip_cfg.num_slaves) begin
    for (bit [63:0] mem_addr=0; mem_addr <= axi_vip_cfg.axi_slave_mem_addr_max; mem_addr++) begin
      case (slv_id)
        0 : env.axi_system_env.slave[0].write_byte(mem_addr, 8'h00);
        1 : env.axi_system_env.slave[1].write_byte(mem_addr, 8'h00);
      endcase
    end
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW) 
  end
endtask : slvmem_bkdr_clear_all


// Preloads Entire AXI SLAVE MEMORY for the given AXI SLAVE AGENT (with specified data)
// ------------------------------------------------------------
// NOT PRACTICAL to USE. For Memory of size 40-bits, this equates to 1,099,511,627,776 addresses to be indvidually preloaded
task dma_ip_base_test::slvmem_bkdr_preload_all (int slv_id, string preload_type);
bit [7:0] memdata;

  if (slv_id < axi_vip_cfg.num_slaves) begin
    for (bit [63:0] mem_addr=0; mem_addr <= axi_vip_cfg.axi_slave_mem_addr_max; mem_addr++) begin
    
      case (preload_type)
        "ONES"  : memdata = '1;
        "ZEROS" : memdata = '0;
        "RAND"  : if (!std::randomize(memdata))  `uvm_error(get_full_name(), $sformatf("FAILED to randomize mem-data"))
        "PATT"  : memdata = user_data_pattern;
      endcase
    
      case (slv_id)
        0 : env.axi_system_env.slave[0].write_byte(mem_addr, memdata);
        1 : env.axi_system_env.slave[1].write_byte(mem_addr, memdata);
      endcase
    end
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW) 
  end
endtask : slvmem_bkdr_preload_all


// Preloads given address regions of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT (with specified data)
// ------------------------------------------------------------
task dma_ip_base_test::slvmem_bkdr_preload_range (int slv_id, string preload_type, bit [39:0] addr_start, bit [39:0] addr_end);
bit [7:0] memdata;

  if (slv_id < axi_vip_cfg.num_slaves) begin
    for (bit [63:0] mem_addr=addr_start; mem_addr <= addr_end; mem_addr++) begin
    
      case (preload_type)
        "ONES"  : memdata = '1;
        "ZEROS" : memdata = '0;
        "RAND"  : if (!std::randomize(memdata))  `uvm_error(get_full_name(), $sformatf("FAILED to randomize mem-data"))
        "PATT"  : memdata = user_data_pattern;
      endcase
    
      case (slv_id)
        0 : env.axi_system_env.slave[0].write_byte(mem_addr, memdata);
        1 : env.axi_system_env.slave[1].write_byte(mem_addr, memdata);
      endcase
    end
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW) 
  end
endtask : slvmem_bkdr_preload_range


// Writes a single given BYTE to given address of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_base_test::slvmem_bkdr_write_byte (int slv_id, bit [39:0] addr, bit [7:0] data);
  if (slv_id < axi_vip_cfg.num_slaves) begin
    case (slv_id)
      0 : env.axi_system_env.slave[0].write_byte(addr, data);
      1 : env.axi_system_env.slave[1].write_byte(addr, data);
    endcase
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW)  
  end
endtask : slvmem_bkdr_write_byte


// Writes a series of given BYTES to the given address of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_base_test::slvmem_bkdr_write_num_byte (int slv_id, bit [39:0] addr,  int num_of_bytes, bit [7:0] data[]);
  if (slv_id < axi_vip_cfg.num_slaves) begin
    case (slv_id)
      0 : env.axi_system_env.slave[0].write_num_byte(addr, num_of_bytes, data);
      1 : env.axi_system_env.slave[1].write_num_byte(addr, num_of_bytes, data);
    endcase
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW) 
  end
endtask : slvmem_bkdr_write_num_byte


// Writes a series of self-generated RANDOM BYTES to given addresses of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_base_test::slvmem_bkdr_write_num_randbyte (int slv_id, bit [39:0] addr,  int num_of_bytes);
bit [7:0] memdata;

  if (slv_id < axi_vip_cfg.num_slaves) begin
    for (int byte_idx=0; byte_idx < num_of_bytes; byte_idx++) begin
      
      if (!std::randomize(memdata)) 
        `uvm_error(get_full_name(), $sformatf("FAILED to randomize mem-data"))
      
      case (slv_id)
        0 : env.axi_system_env.slave[0].write_byte(addr+byte_idx, memdata);
        1 : env.axi_system_env.slave[1].write_byte(addr+byte_idx, memdata);
      endcase
    end
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW)  
  end
endtask : slvmem_bkdr_write_num_randbyte


// READ TASKS
// -----------

// READS a single BYTE from given address of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_base_test::slvmem_bkdr_read_byte (int slv_id, bit [39:0] addr, ref bit [7:0] data);
bit [7:0] readdata;

  if (slv_id < axi_vip_cfg.num_slaves) begin
    case (slv_id)
      0 : env.axi_system_env.slave[0].read_byte(addr, readdata);
      1 : env.axi_system_env.slave[1].read_byte(addr, readdata);
    endcase
  data = readdata;
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW) 
  end
endtask : slvmem_bkdr_read_byte


// READS a series of BYTES from the given address of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_base_test::slvmem_bkdr_read_num_byte (int slv_id, bit [39:0] addr, int num_of_bytes, ref bit [7:0] data[]);
bit [7:0] readdata[];

  readdata = new[num_of_bytes];
  if (slv_id < axi_vip_cfg.num_slaves) begin
    case (slv_id)
      0 : env.axi_system_env.slave[0].read_num_byte(addr, num_of_bytes, readdata);
      1 : env.axi_system_env.slave[1].read_num_byte(addr, num_of_bytes, readdata);
    endcase
    
    foreach (readdata[i]) begin
      data[i] = readdata[i];
    end
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW) 
  end
endtask : slvmem_bkdr_read_num_byte


// READs a series of bytes the given address regions of the AXI SLAVE MEMORY for the given AXI SLAVE AGENT
// ------------------------------------------------------------
task dma_ip_base_test::slvmem_bkdr_read_range (int slv_id, bit [39:0] addr_start, bit [39:0] addr_end, ref bit [7:0] data[]);
bit [7:0]     readdata[];
logic [63:0]  num_bytes_to_access;

  // WORKAROUND. cant do num_bytes_to_access = addr_end - addr_start   (as results depend upon the upper SIGNED bit)
  num_bytes_to_access = 0;
  for (bit [63:0] i = addr_start; i <= addr_end; i++)
    num_bytes_to_access++;

  readdata = new[num_bytes_to_access];

  if (slv_id < axi_vip_cfg.num_slaves) begin
    for (bit [63:0] mem_addr=addr_start; mem_addr <= num_bytes_to_access; mem_addr++) begin
      case (slv_id)
        0 : env.axi_system_env.slave[0].read_byte(mem_addr, readdata[mem_addr]);
        1 : env.axi_system_env.slave[1].read_byte(mem_addr, readdata[mem_addr]);
      endcase
      
      foreach (readdata[i]) begin
        data[i] = readdata[i];
      end
    end
  end
  else begin
    `uvm_info(get_full_name(), $sformatf("Unsupported AXI SLAVE IDX[%0d]. There are only %0d DMA TRANSFER PORTs", slv_id, axi_vip_cfg.num_slaves), UVM_LOW) 
  end
endtask : slvmem_bkdr_read_range




`endif // GUARD_DMA_IP_BASE_TEST_SV
