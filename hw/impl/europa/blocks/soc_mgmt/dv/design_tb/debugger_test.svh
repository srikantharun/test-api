// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>

// Test the debugger connectivity

task debugger_test();
  `uvm_warning("DEBUGGER_TEST", "USING FORCE")
  `uvm_info("DEBUGGER_TEST", "Debugger test Start", UVM_NONE)

  repeat(10e3) @ (posedge i_ref_clk) begin
    // Inputs
    i_hart_unavail     = $urandom( );
    i_hart_under_reset = $urandom( );
    i_lt_axi_m_awready = $urandom( );
    i_lt_axi_m_wready  = $urandom( );
    i_lt_axi_m_bid     = $urandom( );
    i_lt_axi_m_bresp   = $urandom( );
    i_lt_axi_m_bvalid  = $urandom( );
    i_lt_axi_m_arready = $urandom( );
    i_lt_axi_m_rid     = $urandom( );
    i_lt_axi_m_rdata   = $urandom( );
    i_lt_axi_m_rresp   = $urandom( );
    i_lt_axi_m_rlast   = $urandom( );
    i_lt_axi_m_rvalid  = $urandom( );

    // debug outputs to top pins
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_debugint      = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_resethaltreq  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_dmactive      = $urandom();

    // debugger SYS_AXI to outputs
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awaddr   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awid     = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awlen    = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awsize   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awburst  = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awlock   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awcache  = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awprot   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awvalid  = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_wdata    = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_wstrb    = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_wlast    = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_wvalid   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_bready   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arid     = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_araddr   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arlen    = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arsize   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arburst  = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arlock   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arcache  = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arprot   = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arvalid  = $urandom();
    force i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_rready   = $urandom();

    // smu fabric to debugger AXI RV inputs
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_araddr  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arburst = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arcache = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arid    = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arlen   = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arlock  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arprot  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arsize  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arvalid = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awaddr  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awburst = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awcache = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awid    = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awlen   = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awlock  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awprot  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awsize  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awvalid = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_bready  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_rready  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_wdata   = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_wlast   = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_wstrb   = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_wvalid  = $urandom();

    // debugger AXI RV outputs to smu fabric
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_arready  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_awready  = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_bid      = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_bresp    = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_bvalid   = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rdata    = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rid      = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rlast    = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rresp    = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rvalid   = $urandom();
    force  i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_wready   = $urandom();

  end

  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_debugint     ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_resethaltreq ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_dmactive     ;

  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awaddr   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awid     ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awlen    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awsize   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awburst  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awlock   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awcache  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awprot   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_awvalid  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_wdata    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_wstrb    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_wlast    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_wvalid   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_bready   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arid     ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_araddr   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arlen    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arsize   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arburst  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arlock   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arcache  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arprot   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_arvalid  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_sys_rready   ;

  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_araddr  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arburst ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arcache ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arid    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arlen   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arlock  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arprot  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arsize  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_arvalid ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awaddr  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awburst ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awcache ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awid    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awlen   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awlock  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awprot  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awsize  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_awvalid ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_bready  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_rready  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_wdata   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_wlast   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_wstrb   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_bus_fabric_wrapper.u_smu_fabric_subsys.ex_smu_axi_fabric_lt_axi_dbgr_m_wvalid  ;

  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_arready  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_awready  ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_bid      ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_bresp    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_bvalid   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rdata    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rid      ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rlast    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rresp    ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_rvalid   ;
  release i_soc_mgmt_p_dut.u_soc_mgmt.u_nds_pldm_wrapper.o_rv_wready   ;

endtask



