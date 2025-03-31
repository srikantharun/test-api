// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

//`define EN_OTHER_ADDRS // enables additonal addrs in the axi_addr_Q
`ifndef GUARD_COMMON_SEQ_LIB_BASE_TEST_SV
`define GUARD_COMMON_SEQ_LIB_BASE_TEST_SV
// AI CORE TRITON_NOC base test class


class common_seq_lib_base_test extends uvm_test;
  //bit RAL_TEST;
  /** UVM Component Utility macro */
  `uvm_component_utils(common_seq_lib_base_test)

  test_cfg base_test_cfg;

  bit [40-1:0]    axi_addr[$];
  bit [512-1:0]   axi_write_data;
  
  bit [`AXI_HP_DATA_WIDTH-1:0]      wr_data[];
  
  // Declare p sequencer
  // `uvm_declare_p_sequencer(axi_virtual_sequencer)

  /** Instance of the environment */
  common_seq_lib_env env;

  //Axi reset sequece
  axi_simple_reset_sequence           axi_reset_seq;

  axi_master_write_random_sequence    axi_wr_rand_seq;
  axi_master_read_random_sequence     axi_rd_rand_seq;
  axi_dma_write_sequence              axi_dma_wr_seq;
  axi_dma_read_sequence               axi_dma_rd_seq;
  axi_dma_sequence                    axi_dma_seq;

  axi_cac_read_sequence               axi_cac_rd_seq;
  axi_cac_sequence                    axi_cac_seq;

  /** Class Constructor */
  function new(string name = "common_seq_lib_base_test", uvm_component parent=null);
    super.new(name,parent);
    uvm_top.set_timeout(3ms,1);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    base_test_cfg = test_cfg::type_id::create("base_test_cfg");

    //set default values
    base_test_cfg.SRC_ADDR = 'h0;
    base_test_cfg.DST_ADDR = 'h8000;
    base_test_cfg.BW = BW_full;
    base_test_cfg.DATA_BSIZE = SIZE_1K;
    base_test_cfg.INITIATOR = SDMA;
    uvm_config_db#(test_cfg)::set(this, "*", "base_test_cfg", base_test_cfg);

    /** Create the environment */
    env = common_seq_lib_env::type_id::create("env", this);
    /** Apply the default reset sequence */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());

    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());
    
    axi_reset_seq         = axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    
    axi_wr_rand_seq       = axi_master_write_random_sequence::type_id::create("axi_wr_rand_seq");
    axi_rd_rand_seq       = axi_master_read_random_sequence::type_id::create("axi_rd_rand_seq");
    axi_dma_wr_seq        = axi_dma_write_sequence::type_id::create("axi_dma_wr_seq");
    axi_dma_rd_seq        = axi_dma_read_sequence::type_id::create("axi_dma_rd_seq");
    axi_dma_seq           = axi_dma_sequence::type_id::create("axi_dma_seq");

    axi_cac_rd_seq        = axi_cac_read_sequence::type_id::create("axi_cac_rd_seq");
    axi_cac_seq           = axi_cac_sequence::type_id::create("axi_cac_seq");

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
    uvm_status_e status;
    int size;
    `uvm_info ("common_seq_lib_base_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

      // Start reset sequence on the sequencer
      axi_reset_seq.start(env.sequencer);

`ifndef DUT
      // Initializing 12K of data with incrementing values for common_seq_lib testing purposes
      // User may skip this by overriding init_data() and check_read_data_against_init()
      // delay added after data init can also be re-defined
      init_data();
      check_read_data_against_init();
`endif
      #`DELAY_AFTER_INIT;

    phase.drop_objection(this);
    `uvm_info ("common_seq_lib_base_test", "Objection dropped", UVM_HIGH)
  
  endtask : run_phase

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

    if (svr.get_severity_count(UVM_FATAL) +
        svr.get_severity_count(UVM_ERROR) +
        svr.get_severity_count(UVM_WARNING) > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else
      `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    `uvm_info("final_phase", "Exiting...", UVM_LOW)
  endfunction: final_phase

  extern virtual task check_read_data_against_init();
  extern virtual task init_data();
  extern virtual task dma_read();
  extern virtual task dma_write();
  extern virtual task dma_move();

endclass:common_seq_lib_base_test

`endif // GUARD_COMMON_SEQ_LIB_BASE_TEST_SV

