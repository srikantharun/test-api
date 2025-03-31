// *** (C) Copyright Axelera AI 2024        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : ana.stoisavljevic@axelera.ai  *** //

`ifndef GUARD_FABRIC_CSL_BASE_TEST_SV
`define GUARD_FABRIC_CSL_BASE_TEST_SV

class fabric_csl_base_test extends uvm_test;
  /** UVM Component Utility macro */
  `uvm_component_utils(fabric_csl_base_test)

  //test_cfg base_test_cfg;
  pve_fabric_configuration pve_fabric_cfg;

  bit [`AXI_LP_ADDR_WIDTH-1:0]    axi_addr_a[int];
  bit [512-1:0]   axi_write_data;
  
  bit [`AXI_HP_DATA_WIDTH-1:0]      wr_data[];
  
  /** Instance of the environment */
  fabric_csl_env env;

  //Axi reset sequece
  axi_simple_reset_sequence           axi_reset_seq;

  axi_master_write_random_sequence    axi_wr_rand_seq;
  axi_master_read_random_sequence     axi_rd_rand_seq;

  /** Class Constructor */
  function new(string name = "fabric_csl_base_test", uvm_component parent=null);
    super.new(name,parent);
    uvm_top.set_timeout(3ms,1);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    pve_fabric_cfg = pve_fabric_configuration::type_id::create("pve_fabric_cfg");

    // INT HTF -> LTF: HTF MST0 and MST2 can access LTF EXT (SLV6) trough internal connection
    // INT LTF -> HTF: LTF MST0-7 Cluster can access HTF SLV0-3 L1 trough internal connection

    //                                                        LTF MST -> LTF SLV                       LTF MST -> HTF SLV
    //                                              SLV0  SLV1  SLV2  SLV3  SLV4  SLV5  SLV6      SLV7  SLV8  SLV9  SLV10 SLV11
    //                                              DMA0  DMA1  CLI   PERFC TRACE SPM   EXT_LT    L1_0  L1_1  L1_2  L1_3  EXT_HT

    pve_fabric_cfg.pve_conn_matrix[init_cl0cpu0] = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_cl0cpu1] = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_cl1cpu0] = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_cl1cpu1] = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_cl2cpu0] = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_cl2cpu1] = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_cl3cpu0] = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_cl3cpu1] = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_trace]   = {1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1, 1'b1,     1'b0, 1'b0, 1'b0, 1'b0, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_lt_ext]  = {1'b1, 1'b1, 1'b1, 1'b0, 1'b0, 1'b1, 1'b0,     1'b0, 1'b0, 1'b0, 1'b0, 1'b0}; // FIXME: after perfc is enabled, fix appropriate connection

    //                                                        HTF MST -> LTF SLV                       HTF MST -> HTF SLV
    pve_fabric_cfg.pve_conn_matrix[init_dma0_0]  = {1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b1,     1'b0, 1'b0, 1'b0, 1'b0, 1'b1};
    pve_fabric_cfg.pve_conn_matrix[init_dma0_1]  = {1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};
    pve_fabric_cfg.pve_conn_matrix[init_dma1_0]  = {1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b1,     1'b0, 1'b0, 1'b0, 1'b0, 1'b1};
    pve_fabric_cfg.pve_conn_matrix[init_dma1_1]  = {1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0,     1'b1, 1'b1, 1'b1, 1'b1, 1'b0};

    uvm_config_db#(pve_fabric_configuration)::set(null, "uvm_test_top", "pve_fabric_cfg", pve_fabric_cfg);

    /** Create the environment */
    env = fabric_csl_env::type_id::create("env", this);
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
  endfunction : connect_phase
  // Run phase //
  virtual task run_phase(uvm_phase phase);
    uvm_status_e status;
    int size;
    `uvm_info ("fabric_csl_base_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    // Start reset sequence on the sequencer
    axi_reset_seq.start(env.sequencer);

    phase.drop_objection(this);
    `uvm_info ("fabric_csl_base_test", "Objection dropped", UVM_HIGH)
  
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

  function targ_t get_target(bit [`AXI_HP_ADDR_WIDTH :0] addr, init_t port_id);
     if ((port_id == init_dma0_0 || port_id == init_dma1_0) && (addr < `PVE_BASE + `L1_0_SA || addr > `PVE_BASE + `L1_3_EA))
        return targ_ht_ext;
     else if (addr > `PVE_BASE + `DMA0_SA           && addr < `PVE_BASE + `DMA0_EA) 
        return targ_dma0;
     else if (addr > `PVE_BASE + `DMA1_SA           && addr < `PVE_BASE + `DMA1_EA)
        return targ_dma1;
     else if (addr > `PVE_BASE + `CLINT_SA          && addr < `PVE_BASE + `CLINT_EA)
        return targ_clint;
     else if (addr > `PVE_BASE + `PERF_COUNTERS_SA  && addr < `PVE_BASE + `PERF_COUNTERS_EA)
        return targ_perfc;
     else if (addr > `PVE_BASE + `TRACE_IP_SA       && addr < `PVE_BASE + `TRACE_IP_EA)
        return targ_trace;
     else if (addr > `PVE_BASE + `SPM_SA            && addr < `PVE_BASE + `SPM_EA)
        return targ_spm;
     else if (addr > `PVE_BASE + `L1_0_SA           && addr < `PVE_BASE + `L1_0_EA)
        return targ_l1_0;
     else if (addr > `PVE_BASE + `L1_1_SA           && addr < `PVE_BASE + `L1_1_EA)
        return targ_l1_1;
     else if (addr > `PVE_BASE + `L1_2_SA           && addr < `PVE_BASE + `L1_2_EA)
        return targ_l1_2;
     else if (addr > `PVE_BASE + `L1_3_SA           && addr < `PVE_BASE + `L1_3_EA)
        return targ_l1_3;
     else
        return targ_lt_ext;
 endfunction 

  task check_conn_matrix(input svt_axi_master_transaction req_resp);
    if (pve_fabric_cfg.pve_conn_matrix[req_resp.port_id][get_target(req_resp.addr, req_resp.port_id)] == 1) begin
       `uvm_info("PVE fabric", $sformatf("CONNECTIVITY_CHECK : + INIT[%s]: TARG : %s CONN: %0d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), pve_fabric_cfg.pve_conn_matrix[req_resp.port_id][get_target(req_resp.addr, req_resp.port_id)]), UVM_LOW)
       if(req_resp.transmitted_channel == svt_axi_master_transaction::WRITE) begin
          if (req_resp.bresp != svt_axi_master_transaction::OKAY && req_resp.bresp != svt_axi_master_transaction::EXOKAY) 
             `uvm_error ("PVE fabric", $sformatf("CONNECTIVITY_CHECK : Received non OKAY response! INIT[%s]: TARG : %s BRESP : %d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), req_resp.bresp))
          else
             `uvm_info ("PVE fabric", $sformatf("CONNECTIVITY_CHECK : Received OKAY response! INIT[%s]: TARG : %s BRESP : %d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), req_resp.bresp), UVM_LOW)
       end
       else if(req_resp.transmitted_channel == svt_axi_master_transaction::READ) begin
          if(req_resp.rresp[0] != svt_axi_master_transaction::OKAY && req_resp.rresp[0] != svt_axi_master_transaction::EXOKAY) 
             `uvm_error ("PVE fabric", $sformatf("CONNECTIVITY_CHECK : Received non OKAY response! INIT[%s]: TARG : %s RRESP : %d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), req_resp.rresp[0]))
          else
             `uvm_info("PVE fabric", $sformatf("CONNECTIVITY_CHECK : Received OKAY response! INIT[%s]: TARG : %s RRESP : %d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), req_resp.rresp[0]), UVM_LOW)
       end
    end
    else begin
       `uvm_info("PVE fabric", $sformatf("CONNECTIVITY_CHECK : - INIT[%s]: TARG : %s CONN: %0d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), pve_fabric_cfg.pve_conn_matrix[req_resp.port_id][get_target(req_resp.addr, req_resp.port_id)]), UVM_LOW)
       if(req_resp.transmitted_channel == svt_axi_master_transaction::WRITE) begin
          if(req_resp.bresp == svt_axi_master_transaction::OKAY || req_resp.bresp == svt_axi_master_transaction::EXOKAY)
             `uvm_error ("PVE fabric", $sformatf("CONNECTIVITY_CHECK : Received OKAY response! INIT[%s]: TARG : %s BRESP : %d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), req_resp.bresp))
          else
             `uvm_info ("PVE fabric", $sformatf("CONNECTIVITY_CHECK : Received error response as expected! INIT[%s]: TARG : %s BRESP : %d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), req_resp.bresp), UVM_LOW)
       end
       else if(req_resp.transmitted_channel == svt_axi_master_transaction::READ) begin
          if(req_resp.rresp[0] == svt_axi_master_transaction::OKAY || req_resp.rresp[0] == svt_axi_master_transaction::EXOKAY)
             `uvm_error ("PVE fabric", $sformatf("CONNECTIVITY_CHECK : Received OKAY response! INIT[%s]: TARG : %s RRESP : %d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), req_resp.rresp[0]))
          else
             `uvm_info("PVE fabric", $sformatf("CONNECTIVITY_CHECK : Received error response as expected! INIT[%s]: TARG : %s RRESP : %d", init_t'(req_resp.port_id), get_target(req_resp.addr, req_resp.port_id), req_resp.rresp[0]), UVM_LOW)
       end
    end
  endtask

  task randomize_axi_address();
      axi_addr_a[0] = $urandom_range(`PVE_BASE + `DMA0_SA, `PVE_BASE + `DMA0_EA);
      axi_addr_a[1] = $urandom_range(`PVE_BASE + `DMA1_SA, `PVE_BASE + `DMA1_EA);
      axi_addr_a[2] = $urandom_range(`PVE_BASE + `CLINT_SA, `PVE_BASE + `CLINT_EA);
      axi_addr_a[3] = $urandom_range(`PVE_BASE + `PERF_COUNTERS_SA, `PVE_BASE + `PERF_COUNTERS_EA);
      axi_addr_a[3] = $urandom_range(`PVE_BASE + `TRACE_IP_SA, `PVE_BASE + `TRACE_IP_EA);
      axi_addr_a[4] = $urandom_range(`PVE_BASE + `SPM_SA, `PVE_BASE + `SPM_EA);
      axi_addr_a[5] = $urandom_range(`PVE_BASE + `L1_0_SA, `PVE_BASE + `L1_0_EA);
      axi_addr_a[6] = $urandom_range(`PVE_BASE + `L1_1_SA, `PVE_BASE + `L1_1_EA);
      axi_addr_a[7] = $urandom_range(`PVE_BASE + `L1_2_SA, `PVE_BASE + `L1_2_EA);
      axi_addr_a[8] = $urandom_range(`PVE_BASE + `L1_3_SA, `PVE_BASE + `L1_3_EA);
      axi_addr_a[9] = $urandom_range(`PVE_BASE, `PVE_EA);
      axi_addr_a[10] = $urandom_range(0, `PVE_BASE);
      axi_addr_a[11] = $urandom_range(`PVE_EA, 32'hFFFF_FFFF);
      axi_addr_a[12] = $urandom_range(`PVE_BASE + `EXT_0_SA, `PVE_BASE + `EXT_0_EA );
      axi_addr_a[13] = $urandom_range(`PVE_BASE + `EXT_1_SA, `PVE_BASE + `EXT_1_EA );
      axi_addr_a[14] = $urandom_range(`PVE_BASE + `EXT_2_SA, `PVE_BASE + `EXT_2_EA );
      axi_addr_a[15] = {$urandom_range(0, 8'hFF),$urandom_range(`PVE_EA, 32'hFFFF_FFFF)};
  endtask

  function bit[`AXI_LP_ADDR_WIDTH-1:0] axi_legal_addr(init_t i);
      if (i == init_lt_ext)
        randcase
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `DMA0_SA, `PVE_BASE + `DMA0_EA); // FIXME: add perfc space once it is implemented
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `DMA1_SA, `PVE_BASE + `DMA1_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `CLINT_SA, `PVE_BASE + `CLINT_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `SPM_SA, `PVE_BASE + `SPM_EA);
        endcase
      else if (i == init_dma0_0 || i == init_dma1_0)
        randcase
          1 : axi_legal_addr = $urandom_range(0, `PVE_BASE + `L1_0_SA);
          1 : axi_legal_addr = {$urandom_range(8'hFF), $urandom_range(`PVE_BASE + `L1_3_EA, 32'hFFFF_FFFF)};
        endcase
      else if (i == init_dma0_1 || i == init_dma1_1)
          axi_legal_addr = $urandom_range(`PVE_BASE + `L1_0_SA,`PVE_BASE + `L1_3_EA );
      else
        randcase
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `DMA0_SA, `PVE_BASE + `DMA0_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `DMA1_SA, `PVE_BASE + `DMA1_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `CLINT_SA, `PVE_BASE + `CLINT_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `TRACE_IP_SA, `PVE_BASE + `TRACE_IP_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `SPM_SA, `PVE_BASE + `SPM_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `L1_0_SA, `PVE_BASE + `L1_0_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `L1_1_SA, `PVE_BASE + `L1_1_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `L1_2_SA, `PVE_BASE + `L1_2_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `L1_3_SA, `PVE_BASE + `L1_3_EA);
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `EXT_0_SA, `PVE_BASE + `EXT_0_EA );
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `EXT_1_SA, `PVE_BASE + `EXT_1_EA );
          1 : axi_legal_addr = $urandom_range(`PVE_BASE + `EXT_2_SA, `PVE_BASE + `EXT_2_EA );
          1 : axi_legal_addr = $urandom_range(0, `PVE_BASE);
          1 : axi_legal_addr = {$urandom_range(8'hFF),$urandom_range(`PVE_EA, 40'hFFFF_FFFF)};
        endcase
  endfunction

endclass:fabric_csl_base_test

`endif // GUARD_COMMON_SEQ_LIB_BASE_TEST_SV

