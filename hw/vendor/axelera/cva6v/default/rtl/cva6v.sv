// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>
//        Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// CVA6V vendorization wrapper
///
module cva6v
  import raptor_pkg::fu_status_e;
  import raptor_pkg::FunctUnitCount;
  #(
  parameter  type           axi_aw_chan_t          = cva6v_ai_core_pkg::axi_aw_chan_t,
  parameter  type           axi_w_chan_t           = cva6v_ai_core_pkg::axi_w_chan_t,
  parameter  type           axi_b_chan_t           = cva6v_ai_core_pkg::axi_b_chan_t,
  parameter  type           axi_ar_chan_t          = cva6v_ai_core_pkg::axi_ar_chan_t,
  parameter  type           axi_r_chan_t           = cva6v_ai_core_pkg::axi_r_chan_t,
  parameter  type           axi_req_t              = cva6v_ai_core_pkg::axi_req_t,
  parameter  type           axi_rsp_t              = cva6v_ai_core_pkg::axi_rsp_t,
  parameter  type           rvfi_probes_t          = vendor_cva6v_pkg::rvfi_probes_t,
  parameter  type           raptor_trace_sigs_t    = logic,
  parameter  type           riscv_etrace_t         = cva6v_ai_core_pkg::riscv_etrace_t,
  parameter  type           impl_inp_t             = axe_tcl_sram_pkg::impl_inp_t,
  parameter  type           impl_oup_t             = axe_tcl_sram_pkg::impl_oup_t,
  parameter  type           cva6_config_t          = cva6v_config_pkg::cva6_cfg_t,
  parameter  type           cva6v_config_t         = cva6v_pkg::cva6v_config_t,
  parameter  cva6v_config_t CVA6VConfig            = cva6v_ai_core_pkg::CVA6VConfig,
  // Extracted parameters
  localparam int unsigned   VRFBankCount           = CVA6VConfig.VRFBankCount,
  localparam int unsigned   VRFPortWidth           = CVA6VConfig.VRFPortWidth,
  localparam int unsigned   VRFBankColumnCount     = CVA6VConfig.VRFBankColumnCount,
  localparam int unsigned   MemPortCount           = CVA6VConfig.MemPortCount,
  localparam int unsigned   MemPortWidth           = CVA6VConfig.MemPortWidth,
  localparam int unsigned   MemPortAddrWidth       = CVA6VConfig.MemPortAddrWidth,
  localparam bit            MemPortCutEn           = CVA6VConfig.MemPortCutEn,
  localparam bit            MemReqQueueCutEn       = CVA6VConfig.MemReqQueueCutEn,
  localparam int unsigned   MemReqQueueDepth       = CVA6VConfig.MemReqQueueDepth,
  localparam int unsigned   MemRegionCount         = CVA6VConfig.MemRegionCount,
  localparam int unsigned   TokenLineCount         = CVA6VConfig.TokenLineCount,
  localparam bit            RIFOffCutEn            = CVA6VConfig.RIFOffCutEn,
  localparam int unsigned   CommitQueueDepth       = CVA6VConfig.CommitQueueDepth,
  localparam int unsigned   DispatchQueueDepth     = CVA6VConfig.DispatchQueueDepth,
  localparam int unsigned   FUTaskQueuesDepth      = CVA6VConfig.FUTaskQueuesDepth,
  localparam int unsigned   TaskCount              = CVA6VConfig.TaskCount,
  localparam int unsigned   DataflowDelay          = CVA6VConfig.DataflowDelay,
  localparam int unsigned   VLSULaneWidth          = CVA6VConfig.VLSULaneWidth,
  localparam int unsigned   VLSULaneCount          = CVA6VConfig.VLSULaneCount,
  localparam int unsigned   VLSUOperandBufferDepth = CVA6VConfig.VLSUOperandBufferDepth,
  localparam int unsigned   VLSUResultBufferDepth  = CVA6VConfig.VLSUResultBufferDepth,
  localparam bit            VLSUTranslationRegEn   = CVA6VConfig.VLSUTranslationRegEn,
  localparam int unsigned   VLSUMaxPendingReq      = CVA6VConfig.VLSUMaxPendingReq,
  localparam int unsigned   VTLBDepth              = CVA6VConfig.VTLBDepth,
  localparam int unsigned   VALUVRFSwapLevelCount  = CVA6VConfig.VALUVRFSwapLevelCount,
  localparam logic [3:0]    VALUPipelineStageEn    = CVA6VConfig.VALUPipelineStageEn,
  localparam int unsigned   VFPUPipelineDepth      = CVA6VConfig.VFPUPipelineDepth,
  localparam int unsigned   VSLDDatapathWidth      = CVA6VConfig.VSLDDatapathWidth,
  localparam int unsigned   VSLDOperandBufferDepth = CVA6VConfig.VSLDOperandBufferDepth,
  localparam int unsigned   VSLDResultBufferDepth  = CVA6VConfig.VSLDResultBufferDepth,
  localparam int unsigned   PerfEventAddrWidth     = CVA6VConfig.PerfEventAddrWidth,
  localparam int unsigned   PerfEventCount         = CVA6VConfig.PerfEventCount,
  localparam int unsigned   PerfEventTraceDelay    = CVA6VConfig.PerfEventTraceDelay,
  localparam int unsigned   MemPortBeWidth         = (MemPortWidth + 'd8 - 'd1) / 'd8,
  localparam cva6_config_t  CVA6Cfg                = CVA6VConfig.CVA6Cfg,
  localparam int unsigned   PerfEventPortCount     = CVA6Cfg.NrCommitPorts + 1,
  localparam type           perf_event_delta_t     = logic [$clog2(VRFBankCount*VRFPortWidth+1)-1:0],
  localparam int unsigned   MemoryMacroCount       = VRFBankCount*VRFBankColumnCount+CVA6Cfg.NrSRAMs
) (
  input  logic                                                  i_clk,
  input  logic                                                  i_rst_n,
  // Config
  input  logic                     [CVA6Cfg.XLEN          -1:0] i_boot_addr,
  input  logic                     [CVA6Cfg.XLEN          -1:0] i_hart_id,
  // Memory regions
  input  logic [MemRegionCount-1:0][CVA6Cfg.PLEN          -1:0] i_memreg_addr,
  input  logic [MemRegionCount-1:0][$clog2(CVA6Cfg.PLEN)  -1:0] i_memreg_size,
  input  logic [MemRegionCount-1:0]                             i_memreg_tcdm,
  // Interrupt inputs
  input  logic                     [                       1:0] i_irq,
  input  logic                                                  i_ipi,
  input  logic                                                  i_time_irq,
  input  logic                     [CVA6Cfg.PIRQ_WIDTH    -1:0] i_platform_irq,
  // Debug
  input  logic                                                  i_debug_req,
  input  logic                                                  i_debug_rst_halt_req,
  output logic                                                  o_debug_stop_time,
  // Hart status
  output logic                                                  o_hart_is_wfi,
  output logic                                                  o_hart_unavail,
  output logic                                                  o_hart_under_reset,
  // Memory side, AXI Master
  output axi_req_t                                              o_axi_req,
  input  axi_rsp_t                                              i_axi_resp,
  // Raptor memory ports
  output logic [MemPortCount  -1:0]                             o_mem_req_valid,
  input  logic [MemPortCount  -1:0]                             i_mem_req_ready,
  output logic [MemPortCount  -1:0][MemPortAddrWidth      -1:0] o_mem_req_addr,
  output logic [MemPortCount  -1:0]                             o_mem_req_we,
  output logic [MemPortCount  -1:0][MemPortBeWidth        -1:0] o_mem_req_be,
  output logic [MemPortCount  -1:0][MemPortWidth          -1:0] o_mem_req_wdata,
  input  logic [MemPortCount  -1:0]                             i_mem_res_valid,
  input  logic [MemPortCount  -1:0][MemPortWidth          -1:0] i_mem_res_rdata,
  input  logic [MemPortCount  -1:0]                             i_mem_res_err,
  // Raptor performance counter signals
  output fu_status_e               [FunctUnitCount        -1:0] o_perf_cntr_fu_status,
  output logic                                                  o_perf_cntr_dispatch_queue_full,
  output logic                                                  o_perf_cntr_dispatch_queue_empty,
  output logic                                                  o_perf_cntr_commit_queue_full,
  output logic                                                  o_perf_cntr_commit_queue_empty,
  // CVA6V performance event signals -- multiple ports, each with an address and event deltas
  output logic              [PerfEventPortCount-2:0][CVA6Cfg.PLEN      -2:0] o_perf_event_addr_full,
  output logic                                      [PerfEventAddrWidth-1:0] o_perf_event_addr_last,
  output perf_event_delta_t [PerfEventPortCount-1:0][PerfEventCount    -1:0] o_perf_event_deltas,
  // CVA6 RISC-V formal interface port
  output rvfi_probes_t                                          o_rvfi_probes,
  // Raptor tracing signals
  output raptor_trace_sigs_t                                    o_trace_raptor,
  // RISC-V instruction tracing
  output riscv_etrace_t                                         o_etrace,
  // SRAM implementation ports.
  input  impl_inp_t                                             i_impl,
  output impl_oup_t                                             o_impl
);

  impl_inp_t [MemoryMacroCount-1:0] cfg_sram_inp;
  impl_oup_t [MemoryMacroCount-1:0] cfg_sram_oup;

  axe_tcl_sram_cfg #(
    .NUM_SRAMS(MemoryMacroCount)
  ) u_sram_cfg (
    .i_s(i_impl),
    .o_s(o_impl),
    .o_m(cfg_sram_inp),
    .i_m(cfg_sram_oup)
  );

  cva6v_top #(
    .axi_aw_chan_t       ( axi_aw_chan_t       ),
    .axi_w_chan_t        ( axi_w_chan_t        ),
    .axi_b_chan_t        ( axi_b_chan_t        ),
    .axi_ar_chan_t       ( axi_ar_chan_t       ),
    .axi_r_chan_t        ( axi_r_chan_t        ),
    .axi_req_t           ( axi_req_t           ),
    .axi_rsp_t           ( axi_rsp_t           ),
    .rvfi_probes_t       ( rvfi_probes_t       ),
    .raptor_trace_sigs_t ( raptor_trace_sigs_t ),
    .riscv_etrace_t      ( riscv_etrace_t      ),
    .cva6_config_t       ( cva6_config_t       ),
    .cva6v_config_t      ( cva6v_config_t      ),
    .CVA6VConfig         ( CVA6VConfig         ),
    .impl_inp_t          ( impl_inp_t          ),
    .impl_oup_t          ( impl_oup_t          )
  ) u_cva6v_top (
    .clk_i                            ( i_clk                            ),
    .rst_ni                           ( i_rst_n                          ),
    // Config
    .boot_addr_i                      ( i_boot_addr                      ),
    .hart_id_i                        ( i_hart_id                        ),
    // Memory regions
    .memreg_addr_i                    ( i_memreg_addr                    ),
    .memreg_size_i                    ( i_memreg_size                    ),
    .memreg_tcdm_i                    ( i_memreg_tcdm                    ),
    // Interrupt inputs
    .irq_i                            ( i_irq                            ),
    .ipi_i                            ( i_ipi                            ),
    .time_irq_i                       ( i_time_irq                       ),
    .platform_irq_i                   ( i_platform_irq                   ),
    // Debug
    .debug_req_i                      ( i_debug_req                      ),
    .debug_rst_halt_req_i             ( i_debug_rst_halt_req             ),
    .debug_stop_time_o                ( o_debug_stop_time                ),
    // Hart status
    .hart_is_wfi_o                    ( o_hart_is_wfi                    ),
    .hart_unavail_o                   ( o_hart_unavail                   ),
    .hart_under_reset_o               ( o_hart_under_reset               ),
    // Memory side, AXI Master
    .axi_req_o                        ( o_axi_req                        ),
    .axi_resp_i                       ( i_axi_resp                       ),
    // Raptor memory ports
    .mem_req_valid_o                  ( o_mem_req_valid                  ),
    .mem_req_ready_i                  ( i_mem_req_ready                  ),
    .mem_req_addr_o                   ( o_mem_req_addr                   ),
    .mem_req_we_o                     ( o_mem_req_we                     ),
    .mem_req_be_o                     ( o_mem_req_be                     ),
    .mem_req_wdata_o                  ( o_mem_req_wdata                  ),
    .mem_res_valid_i                  ( i_mem_res_valid                  ),
    .mem_res_rdata_i                  ( i_mem_res_rdata                  ),
    .mem_res_err_i                    ( i_mem_res_err                    ),
    // Raptor performance counter signals
    .perf_cntr_fu_status_o            ( o_perf_cntr_fu_status            ),
    .perf_cntr_dispatch_queue_full_o  ( o_perf_cntr_dispatch_queue_full  ),
    .perf_cntr_dispatch_queue_empty_o ( o_perf_cntr_dispatch_queue_empty ),
    .perf_cntr_commit_queue_full_o    ( o_perf_cntr_commit_queue_full    ),
    .perf_cntr_commit_queue_empty_o   ( o_perf_cntr_commit_queue_empty   ),
    // CVA6V performance event signals -- multiple ports, each with an address and event deltas
    .perf_event_addr_full_o           ( o_perf_event_addr_full           ),
    .perf_event_addr_last_o           ( o_perf_event_addr_last           ),
    .perf_event_deltas_o              ( o_perf_event_deltas              ),
    // CVA6 RISC-V formal interface port
    .rvfi_probes_o                    ( o_rvfi_probes                    ),
    // Raptor tracing signals
    .trace_raptor_o                   ( o_trace_raptor                   ),
    // RISC-V instruction tracing
    .etrace_o                         ( o_etrace                         ),
    // SRAM implementation ports.
    .impl_i                           ( cfg_sram_inp                     ),
    .impl_o                           ( cfg_sram_oup                     )
  );

endmodule : cva6v
