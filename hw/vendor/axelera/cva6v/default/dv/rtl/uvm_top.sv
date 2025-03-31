module hdl_top;
  // Time unit and precision
  timeunit 1ps; timeprecision 1ps;

  import cva6v_ai_core_pkg::*;
  import raptor_pkg::*;
  import cva6v_ariane_pkg::*;
  import cva6v_config_pkg::*;
  import cva6v_test_pkg::*;
  import axe_tcl_sram_pkg::*;

  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  parameter int unsigned RVFI_NRET          = CVA6VConfig.CVA6Cfg.NrCommitPorts;
  parameter int unsigned MemPortBeWidth     = (CVA6VConfig.MemPortWidth + 'd8 - 'd1) / 'd8;
  parameter int unsigned TOTAL_NUM_BANKS    = CVA6VConfig.VRFBankCount*CVA6VConfig.VRFBankColumnCount+CVA6VConfig.CVA6Cfg.NrSRAMs;
  parameter int unsigned PerfEventPortCount = CVA6VConfig.CVA6Cfg.NrCommitPorts + 1;
  parameter int unsigned PerfEventAddrWidth = CVA6VConfig.PerfEventAddrWidth;
  parameter int unsigned PerfEventCount     = CVA6VConfig.PerfEventCount;
  parameter type impl_inp_t                 = axe_tcl_sram_pkg::impl_inp_t;
  parameter type impl_oup_t                 = axe_tcl_sram_pkg::impl_oup_t;
  parameter type perf_event_delta_t         = logic [$clog2(CVA6VConfig.VRFBankCount*CVA6VConfig.VRFPortWidth+1)-1:0];

  realtime      CLK_PERIOD = 0.625ns;  // 1.6GHz


  logic                                                                         clk_i;
  logic                                                                         rst_ni;
  // Config
  logic [CVA6VConfig.CVA6Cfg.XLEN   -1:0]                                       boot_addr_i;
  logic [CVA6VConfig.CVA6Cfg.XLEN   -1:0]                                       hart_id_i;
  // Memory regions
  logic [CVA6VConfig.MemRegionCount-1:0][CVA6VConfig.CVA6Cfg.PLEN-1:0]          memreg_addr_i;
  logic [CVA6VConfig.MemRegionCount-1:0][$clog2(CVA6VConfig.CVA6Cfg.PLEN) -1:0] memreg_size_i;
  logic [CVA6VConfig.MemRegionCount-1:0]                                        memreg_tcdm_i;
  // Interrupt inputs
  logic [               1:0]                                                    irq_i;
  logic                                                                         ipi_i;
  logic                                                                         time_irq_i;
  logic [CVA6VConfig.CVA6Cfg.PIRQ_WIDTH-1:0]                                    platform_irq_i;
  // Debug
  logic                                                                         debug_req_i;
  logic                                                                         debug_rst_halt_req_i;
  logic                                                                         debug_stop_time_o;
  // Hart status
  logic                                                                         hart_is_wfi_o;
  logic                                                                         hart_unavail_o;
  logic                                                                         hart_under_reset_o;
  // Memory side, AXI Master
  axi_req_t                                                                     axi_req_o;
  axi_rsp_t                                                                     axi_resp_i;
  axi_req_t                                                                     axi_atomics_req_o;
  axi_rsp_t                                                                     axi_atomics_resp_i;
  // Raptor memory ports
  logic [CVA6VConfig.MemPortCount  -1:0]                                        mem_req_valid_o;
  logic [CVA6VConfig.MemPortCount  -1:0]                                        mem_req_ready_i;
  logic [CVA6VConfig.MemPortCount  -1:0][CVA6VConfig.MemPortAddrWidth-1:0]      mem_req_addr_o;
  logic [CVA6VConfig.MemPortCount  -1:0]                                        mem_req_we_o;
  logic [CVA6VConfig.MemPortCount  -1:0][MemPortBeWidth-1:0]                    mem_req_be_o;
  logic [CVA6VConfig.MemPortCount  -1:0][CVA6VConfig.MemPortWidth-1:0]          mem_req_wdata_o;
  logic [CVA6VConfig.MemPortCount  -1:0]                                        mem_res_valid_i;
  logic [CVA6VConfig.MemPortCount  -1:0][CVA6VConfig.MemPortWidth-1:0]          mem_res_rdata_i;
  logic [CVA6VConfig.MemPortCount  -1:0]                                        mem_res_err_i;


  // Raptor performance counter signals
  fu_status_e               [FunctUnitCount        -1:0]                        perf_cntr_fu_status_o;
  logic                                                                         perf_cntr_dispatch_queue_full_o;
  logic                                                                         perf_cntr_dispatch_queue_empty_o;
  logic                                                                         perf_cntr_commit_queue_full_o;
  logic                                                                         perf_cntr_commit_queue_empty_o;

  logic [PerfEventPortCount-2:0][CVA6Cfg.PLEN      -2:0]                        perf_event_addr_full_o;
  logic [PerfEventAddrWidth-1:0]                                                perf_event_addr_last_o;
  perf_event_delta_t [PerfEventPortCount-1:0][PerfEventCount    -1:0]           perf_event_deltas_o;

  // Raptor tracing signals
  raptor_trace_sigs_t                                                           trace_raptor_o;
  // RISC-V instruction tracing
  cva6v_ai_core_pkg::riscv_etrace_t                                             etrace_o;
  // SRAM implementation ports.
  impl_inp_t [TOTAL_NUM_BANKS-1:0]                                              impl_i;
  impl_oup_t [TOTAL_NUM_BANKS-1:0]                                              impl_o;

  // CVA6 Tracer
  logic [31:0]                                                                  tb_exit_o;

  cva6v_test_pkg::rvfi_probes_t                                                 rvfi_probes_o;

  cva6v_test_pkg::rvfi_probes_instr_t                                           rvfi_probes_instr;
  cva6v_test_pkg::rvfi_probes_csr_t                                             rvfi_probes_csr;
  cva6v_test_pkg::rvfi_instr_t   [CVA6VConfig.CVA6Cfg.NrCommitPorts-1:0]        rvfi_instr;
  cva6v_test_pkg::rvfi_csr_t                                                    rvfi_csr;
  cva6v_test_pkg::rvvi_trace_t                                                  rvvi_trace;

  svt_axi_if                                                                    i_svt_axi_if ();

  logic use_riscv_atomics_module;

  // -----------------------------
  // SVT AXI START
  // -----------------------------
  assign i_svt_axi_if.common_aclk = clk_i;
  assign i_svt_axi_if.slave_if[0].aresetn  = rst_ni;

  assign i_svt_axi_if.slave_if[0].awvalid  = (use_riscv_atomics_module) ? axi_atomics_req_o.aw_valid : axi_req_o.aw_valid;
  assign i_svt_axi_if.slave_if[0].awaddr   = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.addr : axi_req_o.aw.addr;
  assign i_svt_axi_if.slave_if[0].awid     = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.id : axi_req_o.aw.id;
  assign i_svt_axi_if.slave_if[0].awlen    = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.len : axi_req_o.aw.len;
  assign i_svt_axi_if.slave_if[0].awsize   = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.size : axi_req_o.aw.size;
  assign i_svt_axi_if.slave_if[0].awburst  = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.burst : axi_req_o.aw.burst;
  assign i_svt_axi_if.slave_if[0].awlock   = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.lock : axi_req_o.aw.lock;
  assign i_svt_axi_if.slave_if[0].awcache  = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.cache : axi_req_o.aw.cache;
  assign i_svt_axi_if.slave_if[0].awprot   = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.prot : axi_req_o.aw.prot;
  assign i_svt_axi_if.slave_if[0].awqos    = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.qos : axi_req_o.aw.qos;
  assign i_svt_axi_if.slave_if[0].awregion = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.region : axi_req_o.aw.region;
  assign i_svt_axi_if.slave_if[0].awuser   = (use_riscv_atomics_module) ? axi_atomics_req_o.aw.user : axi_req_o.aw.user;
  assign axi_resp_i.aw_ready               = (use_riscv_atomics_module) ? axi_atomics_resp_i.aw_ready : i_svt_axi_if.slave_if[0].awready;

  assign i_svt_axi_if.slave_if[0].wvalid   = (use_riscv_atomics_module) ? axi_atomics_req_o.w_valid : axi_req_o.w_valid;
  assign i_svt_axi_if.slave_if[0].wlast    = (use_riscv_atomics_module) ? axi_atomics_req_o.w.last : axi_req_o.w.last;
  assign i_svt_axi_if.slave_if[0].wdata    = (use_riscv_atomics_module) ? axi_atomics_req_o.w.data : axi_req_o.w.data;
  assign i_svt_axi_if.slave_if[0].wstrb    = (use_riscv_atomics_module) ? axi_atomics_req_o.w.strb : axi_req_o.w.strb;
  assign i_svt_axi_if.slave_if[0].wuser    = (use_riscv_atomics_module) ? axi_atomics_req_o.w.user : axi_req_o.w.user;
  assign axi_resp_i.w_ready                = (use_riscv_atomics_module) ? axi_atomics_resp_i.w_ready : i_svt_axi_if.slave_if[0].wready;

  assign axi_resp_i.b_valid                = (use_riscv_atomics_module) ? axi_atomics_resp_i.b_valid : i_svt_axi_if.slave_if[0].bvalid;
  assign axi_resp_i.b.id                   = (use_riscv_atomics_module) ? axi_atomics_resp_i.b.id : i_svt_axi_if.slave_if[0].bid;
  assign axi_resp_i.b.resp                 = (use_riscv_atomics_module) ? axi_atomics_resp_i.b.resp : i_svt_axi_if.slave_if[0].bresp;
  assign axi_resp_i.b.user                 = (use_riscv_atomics_module) ? '0 : '0;
  assign i_svt_axi_if.slave_if[0].bready   = (use_riscv_atomics_module) ? axi_atomics_req_o.b_ready : axi_req_o.b_ready;

  assign i_svt_axi_if.slave_if[0].arvalid  = (use_riscv_atomics_module) ? axi_atomics_req_o.ar_valid : axi_req_o.ar_valid;
  assign i_svt_axi_if.slave_if[0].araddr   = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.addr : axi_req_o.ar.addr;
  assign i_svt_axi_if.slave_if[0].arid     = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.id : axi_req_o.ar.id;
  assign i_svt_axi_if.slave_if[0].arlen    = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.len : axi_req_o.ar.len;
  assign i_svt_axi_if.slave_if[0].arsize   = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.size : axi_req_o.ar.size;
  assign i_svt_axi_if.slave_if[0].arburst  = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.burst : axi_req_o.ar.burst;
  assign i_svt_axi_if.slave_if[0].arlock   = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.lock : axi_req_o.ar.lock;
  assign i_svt_axi_if.slave_if[0].arcache  = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.cache : axi_req_o.ar.cache;
  assign i_svt_axi_if.slave_if[0].arprot   = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.prot : axi_req_o.ar.prot;
  assign i_svt_axi_if.slave_if[0].arqos    = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.qos : axi_req_o.ar.qos;
  assign i_svt_axi_if.slave_if[0].arregion = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.region : axi_req_o.ar.region;
  assign i_svt_axi_if.slave_if[0].aruser   = (use_riscv_atomics_module) ? axi_atomics_req_o.ar.user : axi_req_o.ar.user;
  assign axi_resp_i.ar_ready               = (use_riscv_atomics_module) ? axi_atomics_resp_i.ar_ready : i_svt_axi_if.slave_if[0].arready;

  assign axi_resp_i.r_valid                = (use_riscv_atomics_module) ? axi_atomics_resp_i.r_valid : i_svt_axi_if.slave_if[0].rvalid;
  assign axi_resp_i.r.id                   = (use_riscv_atomics_module) ? axi_atomics_resp_i.r.id : i_svt_axi_if.slave_if[0].rid;
  assign axi_resp_i.r.last                 = (use_riscv_atomics_module) ? axi_atomics_resp_i.r.last : i_svt_axi_if.slave_if[0].rlast;
  assign axi_resp_i.r.data                 = (use_riscv_atomics_module) ? axi_atomics_resp_i.r.data : i_svt_axi_if.slave_if[0].rdata;
  assign axi_resp_i.r.resp                 = (use_riscv_atomics_module) ? axi_atomics_resp_i.r.resp : i_svt_axi_if.slave_if[0].rresp;
  assign axi_resp_i.r.user                 = (use_riscv_atomics_module) ? '0 : '0;
  assign i_svt_axi_if.slave_if[0].rready   = (use_riscv_atomics_module) ? axi_atomics_req_o.r_ready : axi_req_o.r_ready;

  // -----------------------------
  // SVT AXI END
  // -----------------------------

`ifndef NO_DUT

  assign boot_addr_i           = 64'h20_0000_0000;
  assign hart_id_i             = 0;
  assign memreg_addr_i         = 0;               // TODO
  assign memreg_size_i         = 8;             // TODO
  assign memreg_tcdm_i         = 1;               // TODO

  // Assign/initialize inputs
  assign irq_i           = 0; // TODO
  assign ipi_i           = 0; // TODO
  assign time_irq_i      = 0; // TODO
  assign platform_irq_i  = 0; // TODO
  assign mem_req_ready_i = 0; // TODO
  assign mem_res_valid_i = 0; // TODO
  assign mem_res_rdata_i = 0; // TODO
  assign mem_res_err_i   = 0; // TODO
  assign debug_req_i     = 0; // TODO
  assign debug_rst_halt_req_i = 0; // TODO

  assign impl_i          = 0;

  cva6v_top #(
    .axi_aw_chan_t          (cva6v_ai_core_pkg::axi_aw_chan_t),
    .axi_w_chan_t           (cva6v_ai_core_pkg::axi_w_chan_t),
    .axi_b_chan_t           (cva6v_ai_core_pkg::axi_b_chan_t),
    .axi_ar_chan_t          (cva6v_ai_core_pkg::axi_ar_chan_t),
    .axi_r_chan_t           (cva6v_ai_core_pkg::axi_r_chan_t),
    .axi_req_t              (cva6v_ai_core_pkg::axi_req_t),
    .axi_rsp_t              (cva6v_ai_core_pkg::axi_rsp_t),
    .rvfi_probes_t          (cva6v_test_pkg::rvfi_probes_t),
    .raptor_trace_sigs_t    (cva6v_test_pkg::raptor_trace_sigs_t),
    .riscv_etrace_t         (cva6v_ai_core_pkg::riscv_etrace_t),
    .CVA6VConfig            (CVA6VConfig),
    .impl_inp_t             (impl_inp_t),
    .impl_oup_t             (impl_oup_t)
  ) dut (.*);

`endif

  // DUT -> axi_req_o ->                Atomics ->  axi_atomics_req_o (MUX) -> VIP
  //     <- (MUX) axi_atomics_resp_i <-         <- axi_resp_i               <-
    // Axi sizes
  localparam int unsigned AxiAddrWidth = CVA6Cfg.AxiAddrWidth;
  localparam int unsigned AxiDataWidth = CVA6Cfg.AxiDataWidth;
  localparam int unsigned AxiUserWidth = CVA6Cfg.AxiUserWidth;
  localparam int unsigned AxiIdWidthIn = CVA6Cfg.AxiIdWidth;

  axe_axi_riscv_atomics #(
    .AxiAddrWidth     ( AxiAddrWidth                     ),
    .AxiDataWidth     ( AxiDataWidth                     ),
    .AxiIdWidth       ( AxiIdWidthIn                     ),
    .AxiUserWidth     ( AxiUserWidth                     ),
    .AxiMaxReadTxns   ( 4                                ),
    .AxiMaxWriteTxns  ( 4                                ),
    .RiscvWordWidth   ( CVA6Cfg.XLEN                     ),
    .NumCuts          ( 1                                ),
    .axi_aw_t         ( cva6v_ai_core_pkg::axi_aw_chan_t ),
    .axi_w_t          ( cva6v_ai_core_pkg::axi_w_chan_t  ),
    .axi_b_t          ( cva6v_ai_core_pkg::axi_b_chan_t  ),
    .axi_ar_t         ( cva6v_ai_core_pkg::axi_ar_chan_t ),
    .axi_r_t          ( cva6v_ai_core_pkg::axi_r_chan_t  )
  ) i_axi_riscv_atomics (
    .i_clk            ( clk_i                            ),
    .i_rst_n          ( rst_ni                           ),
    .i_axi_s_aw       ( axi_req_o.aw                     ),
    .i_axi_s_aw_valid ( axi_req_o.aw_valid               ),
    .o_axi_s_aw_ready ( axi_atomics_resp_i.aw_ready      ),
    .i_axi_s_w        ( axi_req_o.w                      ),
    .i_axi_s_w_valid  ( axi_req_o.w_valid                ),
    .o_axi_s_w_ready  ( axi_atomics_resp_i.w_ready       ),
    .o_axi_s_b        ( axi_atomics_resp_i.b             ),
    .o_axi_s_b_valid  ( axi_atomics_resp_i.b_valid       ),
    .i_axi_s_b_ready  ( axi_req_o.b_ready                ),
    .i_axi_s_ar       ( axi_req_o.ar                     ),
    .i_axi_s_ar_valid ( axi_req_o.ar_valid               ),
    .o_axi_s_ar_ready ( axi_atomics_resp_i.ar_ready      ),
    .o_axi_s_r        ( axi_atomics_resp_i.r             ),
    .o_axi_s_r_valid  ( axi_atomics_resp_i.r_valid       ),
    .i_axi_s_r_ready  ( axi_req_o.r_ready                ),
    .o_axi_m_aw       ( axi_atomics_req_o.aw             ),
    .o_axi_m_aw_valid ( axi_atomics_req_o.aw_valid       ),
    .i_axi_m_aw_ready ( i_svt_axi_if.slave_if[0].awready ),
    .o_axi_m_w        ( axi_atomics_req_o.w              ),
    .o_axi_m_w_valid  ( axi_atomics_req_o.w_valid        ),
    .i_axi_m_w_ready  ( i_svt_axi_if.slave_if[0].wready  ),
    .i_axi_m_b        ( '{
      resp: i_svt_axi_if.slave_if[0].rvalid,
      id:   i_svt_axi_if.slave_if[0].bid,
      user: '0
    }),
    .i_axi_m_b_valid  ( i_svt_axi_if.slave_if[0].bvalid  ),
    .o_axi_m_b_ready  ( axi_atomics_req_o.b_ready        ),
    .o_axi_m_ar       ( axi_atomics_req_o.ar             ),
    .o_axi_m_ar_valid ( axi_atomics_req_o.ar_valid       ),
    .i_axi_m_ar_ready ( i_svt_axi_if.slave_if[0].arready ),
    .i_axi_m_r        ( '{
      data: i_svt_axi_if.slave_if[0].rdata,
      resp: i_svt_axi_if.slave_if[0].rresp,
      last: i_svt_axi_if.slave_if[0].rlast,
      id:   i_svt_axi_if.slave_if[0].rid,
      user: '0
    }),
    .i_axi_m_r_valid  ( i_svt_axi_if.slave_if[0].rvalid  ),
    .o_axi_m_r_ready  ( axi_atomics_req_o.r_ready        )
  );

  typedef virtual cva6v_rvvi_eot_if  #(cva6v_test_pkg::rvvi_trace_t) cva6v_rvvi_eot_if_t;

  // DV's RVVI EOT Interface
  cva6v_rvvi_eot_if #(
    cva6v_test_pkg::rvvi_trace_t
  ) rvvi_eot_if (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rvvi_i(rvvi_trace),
    .hart_is_wfi_i(hart_is_wfi_o),
    .tb_exit_o(tb_exit_o)
  );

  // Design's RVVI module

  cva6v_rvvi #(
    .rvfi_probes_instr_t ( rvfi_probes_instr_t        ),
    .rvfi_probes_csr_t   ( rvfi_probes_csr_t           ),
    .rvfi_probes_t       ( rvfi_probes_t               ),
    .rvvi_trace_t        ( rvvi_trace_t                ),
    .raptor_trace_t      ( raptor_trace_sigs_t         ),
    .cva6_config_t       ( cva6v_config_pkg::cva6_cfg_t),
    .cva6v_config_t      ( cva6v_pkg::cva6v_config_t   ),
    .CVA6VConfig         ( CVA6VConfig                 )
  ) i_cva6v_rvvi (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .rvfi_probes_i  ( rvfi_probes_o  ),
    .raptor_trace_i ( trace_raptor_o ),
    .rvvi_trace_o   ( rvvi_trace     )
  );

  // DV's RVVI tracer
  rvvi_tracer  #(
    .CVA6Cfg(CVA6VConfig.CVA6Cfg),
    .rvvi_instr_t(rvvi_trace_t),
    //
    .HART_ID(8'h0),
    .DEBUG_START(0),
    .DEBUG_STOP(0)
  ) i_rvvi_tracer (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rvvi_i(rvvi_trace)
  ) ;

`ifdef ADD_DUMP_IF
  cva6v_rvvi_dump_if rvvi_dump_if[CVA6VConfig.CVA6Cfg.NrCommitPorts](clk_i, rst_ni);
  `include "dump_connections.svh"
`endif


  initial begin
    uvm_config_db#(cva6v_rvvi_eot_if_t)::set(.cntxt(null), .inst_name("*"),  .field_name("rvvi_eot_vif"),  .value(rvvi_eot_if));
  end

  always begin
    clk_i <= 1;
    #(CLK_PERIOD / 2);
    clk_i <= 0;
    #(CLK_PERIOD / 2);
  end

  initial begin
    rst_ni = 0;
    #(CLK_PERIOD * 2);
    rst_ni = 1;
  end

  initial begin
    $display("Debugging hdl_top: CVA6VConfig.CVA6Cfg XLEN: %0d cva6v_config_pkg ILEN: %0d", CVA6VConfig.CVA6Cfg.XLEN, cva6v_config_pkg::ILEN);
    $display("Debugging hdl_top: CVA6VConfig NrCommitPorts: %0d", CVA6VConfig.CVA6Cfg.NrCommitPorts);
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.m_env.m_axi_system_env", "vif", i_svt_axi_if);
    $timeformat(-9, 3, " ns", 10);

    run_test();
  end

  // =============================================================================================================
  // Configuration database settings
  // =============================================================================================================
  initial begin
    import uvm_pkg::uvm_config_db;
    use_riscv_atomics_module = 1;
  end

endmodule : hdl_top
