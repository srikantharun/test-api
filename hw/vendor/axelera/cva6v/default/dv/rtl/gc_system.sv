// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: General compute system - instantiates CVA6V
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

module gc_system #(
  // SoC AXI (slave ports) types
  parameter  type           axi_out_ar_chan_t       = logic,
  parameter  type           axi_out_aw_chan_t       = logic,
  parameter  type           axi_out_w_chan_t        = logic,
  parameter  type           axi_out_b_chan_t        = logic,
  parameter  type           axi_out_r_chan_t        = logic,
  parameter  type           axi_out_req_t           = logic,
  parameter  type           axi_out_resp_t          = logic,
  // SoC AXI input (slave ports) types
  parameter  type           axi_in_ar_chan_t        = logic,
  parameter  type           axi_in_aw_chan_t        = logic,
  parameter  type           axi_in_w_chan_t         = logic,
  parameter  type           axi_in_b_chan_t         = logic,
  parameter  type           axi_in_r_chan_t         = logic,
  parameter  type           axi_in_req_t            = logic,
  parameter  type           axi_in_resp_t           = logic,
  // CVA6V tracing types
  parameter  type           rvfi_probes_t           = logic,
  parameter  type           raptor_trace_sigs_t     = logic,
  parameter  type           riscv_etrace_t          = logic,
  // CVA6V configuration types
  parameter  type           cva6_config_t           = cva6v_config_pkg::cva6_cfg_t,
  parameter  type           cva6v_config_t          = cva6v_pkg::cva6v_config_t,
  // System Configuration
  parameter  int unsigned   NrHarts                 = 'd1,
  // Memory
  parameter  logic [63:0]   L1Base                  = 64'h4000_0000,
  parameter  logic [63:0]   L1Size                  = 64'h400,
  parameter  int unsigned   L1BankCount             = 'd1,
  parameter  int unsigned   L1Latency               = 'd1,
  // DRAM (external)
  parameter  logic [63:0]   DRAMBase                = 64'h20_0000_0000,
  parameter  logic [63:0]   DRAMSize                = 64'h18_0000_0000,
  // CLINT Address Region
  parameter  logic [63:0]   ClintBase               = 64'h1000_0000,
  parameter  logic [63:0]   ClintSize               = 64'h0001_0000,
  // Performance Counter Address Region
  parameter  logic [63:0]   PerfCntrsBase           = ClintBase + ClintSize,
  parameter  logic [63:0]   PerfCntrsSize           = 64'h1_0000,
  // CVA6V configuration
  parameter  cva6v_config_t CVA6VConfig             = '0,
  // Extracted parameters
  localparam cva6_config_t  CVA6Cfg                 = CVA6VConfig.CVA6Cfg,
  localparam int unsigned   NrCommitPorts           = CVA6Cfg.NrCommitPorts
) (
  input  logic                                                clk_i,
  input  logic                                                rst_ni,
  // System reset ouput
  output logic                                                sys_rst_no,
  // Config
  input  logic                            [CVA6Cfg.XLEN -1:0] hart_id_i,
  input  logic                            [CVA6Cfg.XLEN -1:0] boot_addr_i,
  // Memory side, AXI Master
  output axi_out_req_t                                        axi_out_req_o,
  input  axi_out_resp_t                                       axi_out_resp_i,
  // NoC side, AXI Slave
  input  axi_in_req_t                                         axi_in_req_i,
  output axi_in_resp_t                                        axi_in_resp_o,
  // CVA6 debug request signal
  output logic               [NrHarts-1:0]                    trace_debug_req_o,
  // CVA6 RISC-V formal interface port
  output rvfi_probes_t       [NrHarts-1:0]                    rvfi_probes_o,
  // Raptor tracing signals
  output raptor_trace_sigs_t [NrHarts-1:0]                    trace_raptor_o,
  // RISC-V instruction tracing
  output riscv_etrace_t      [NrHarts-1:0]                    etrace_o,
  // IRQs
  input logic [NrHarts-1:0][1:0]                              irq_i // machine/supervisor interrupts
);

  // Include FF
  `include "common_cells/registers.svh"
  // Include tcdm req rsp types
  `include "cva6v_vector_fabric/typedef.svh"


  //////////////////////
  // Types and Params //
  //////////////////////

  // Size casting types
  typedef logic [31:0] uint32_t;
  typedef logic [63:0] uint64_t;

  // Axi sizes
  localparam int unsigned AxiAddrWidth = CVA6Cfg.AxiAddrWidth;
  localparam int unsigned AxiDataWidth = CVA6Cfg.AxiDataWidth;
  localparam int unsigned AxiUserWidth = CVA6Cfg.AxiUserWidth;
  localparam int unsigned AxiIdWidthIn = CVA6Cfg.AxiIdWidth;

  // Raptor mem port sizes
  localparam int unsigned MemPortCount     = CVA6VConfig.MemPortCount;
  localparam int unsigned MemPortWidth     = CVA6VConfig.MemPortWidth;
  localparam int unsigned MemPortBeWidth   = (MemPortWidth + 'd8 - 'd1) / 'd8;
  localparam int unsigned MemPortAddrWidth = CVA6VConfig.MemPortAddrWidth;

  // Number of memory regions
  localparam int unsigned MemRegionCount = CVA6VConfig.MemRegionCount;

  // Byte enable width of SoC Axi ports
  localparam int unsigned SoCAxiBeWidth = (AxiDataWidth + 'd8 - 'd1) / 'd8;

  // Data path ratio between CVA6 (AxiDataWidth) and Raptor memory ports
  localparam int unsigned RaptorToCVA6DataRatio      = MemPortWidth/AxiDataWidth;
  localparam int unsigned RaptorToCVA6DataRatioWidth = RaptorToCVA6DataRatio > 'd1 ? $clog2(RaptorToCVA6DataRatio) :
                                                                                     'd1;
  localparam int unsigned PerfEventPortCount       = NrCommitPorts + 1;
  localparam int unsigned PerfEventCount           = CVA6VConfig.PerfEventCount;
  localparam int unsigned PerfEventAddrWidth       = CVA6VConfig.PerfEventAddrWidth;
  localparam int unsigned VRFBankCount             = CVA6VConfig.VRFBankCount;
  localparam int unsigned VRFPortWidth             = CVA6VConfig.VRFPortWidth;
  localparam type         perf_event_delta_t       = logic [$clog2(VRFBankCount*VRFPortWidth+1)-1:0];


  //////////////////
  // System Reset //
  //////////////////

  // System reset is triggered externally
  // This could also be combined with a debug module
  logic sys_rst_n;
  assign sys_rst_n  = rst_ni;
  assign sys_rst_no = sys_rst_n;


  ////////////////
  // Interrupts //
  ////////////////

  logic [NrHarts-1:0]                         machine_external_irqs;
  logic [NrHarts-1:0]                         supervisor_external_irqs;
  logic [NrHarts-1:0][1                   :0] irq;                      // machine/supervisor interrupts
  logic [NrHarts-1:0][CVA6Cfg.PIRQ_WIDTH-1:0] platform_irq;             // platform interrupts

  for (genvar i = 0; i < NrHarts; i++) begin : gen_assign_interrupts
    assign machine_external_irqs[i]    = '0;
    assign supervisor_external_irqs[i] = '0;

    //assign irq[i]          = {supervisor_external_irqs[i], machine_external_irqs[i]};
    assign irq[i] = irq_i[i];
    assign platform_irq[i] = '0;
  end


  //////////////////////////////////
  // Perf Counter Tracing Signals //
  //////////////////////////////////

  raptor_pkg::fu_status_e [NrHarts-1:0][raptor_pkg::FunctUnitCount                -1:0] perf_cntr_fu_status;
  logic                   [NrHarts-1:0]                                                 perf_cntr_dispatch_queue_full;
  logic                   [NrHarts-1:0]                                                 perf_cntr_dispatch_queue_empty;
  logic                   [NrHarts-1:0]                                                 perf_cntr_commit_queue_full;
  logic                   [NrHarts-1:0]                                                 perf_cntr_commit_queue_empty;
  logic                   [NrHarts-1:0][PerfEventPortCount-1:0][PerfEventAddrWidth-1:0] perf_cntr_instr_entry_addr;
  perf_event_delta_t      [NrHarts-1:0][PerfEventPortCount-1:0][PerfEventCount    -1:0] perf_cntr_instr_event_deltas;


  //////////////
  // Axi Xbar //
  //////////////

  localparam int unsigned AxiMstPortCount = 1 + NrHarts; // NOC, harts
  localparam int unsigned AxiSlvPortCount = 5;

  typedef logic [$clog2(AxiMstPortCount)-1:0] axi_masters_t;
  typedef enum axi_masters_t {
    CVA6,
    NOC
  } axi_masters_e;

  typedef logic [$clog2(AxiSlvPortCount)-1:0] axi_slaves_t;
  typedef enum axi_slaves_t {
    ERROR,
    DRAM,
    L1_MEMORY,
    CLINT,
    PERF_CNTRS
  } axi_slaves_e;

  typedef struct packed {
    logic [$clog2(AxiSlvPortCount)-1:0] index;
    logic [AxiAddrWidth           -1:0] addr_start;
    logic [AxiAddrWidth           -1:0] addr_end;
  } xbar_rule_t;

  localparam int unsigned AxiIdWidthOut = AxiIdWidthIn + $clog2(AxiMstPortCount);
  localparam int unsigned AxiRuleCount = AxiSlvPortCount - 1;

  // Xbar master connections
  axi_in_req_t  [AxiMstPortCount-1:0] mst_req;
  axi_in_resp_t [AxiMstPortCount-1:0] mst_resp;

  // Xbar slave connections
  axi_out_req_t  [AxiSlvPortCount-1:0] slv_req;
  axi_out_resp_t [AxiSlvPortCount-1:0] slv_resp;

  // Xbar address map
  xbar_rule_t addr_map [AxiRuleCount-1:0];
  always_comb begin
    addr_map[0] = '{
      index     : uint32_t'(L1_MEMORY),
      addr_start: AxiAddrWidth'(L1Base),
      addr_end  : AxiAddrWidth'(L1Base + L1Size)
    };
    addr_map[1] = '{
      index     : uint32_t'(CLINT),
      addr_start: AxiAddrWidth'(ClintBase),
      addr_end  : AxiAddrWidth'(ClintBase + ClintSize)
    };
    addr_map[2] = '{
      index     : uint32_t'(PERF_CNTRS),
      addr_start: AxiAddrWidth'(PerfCntrsBase),
      addr_end  : AxiAddrWidth'(PerfCntrsBase + PerfCntrsSize)
    };
    addr_map[3] = '{
      index     : uint32_t'(DRAM),
      addr_start: AxiAddrWidth'(DRAMBase),
      addr_end  : AxiAddrWidth'(DRAMBase + DRAMSize)
    };
  end

  // Subordinate Port
  axi_in_aw_chan_t axi_s_aw[AxiMstPortCount];
  logic            axi_s_aw_valid[AxiMstPortCount];
  logic            axi_s_aw_ready[AxiMstPortCount];
  axi_in_w_chan_t  axi_s_w[AxiMstPortCount];
  logic            axi_s_w_valid[AxiMstPortCount];
  logic            axi_s_w_ready[AxiMstPortCount];
  axi_in_b_chan_t  axi_s_b[AxiMstPortCount];
  logic            axi_s_b_valid[AxiMstPortCount];
  logic            axi_s_b_ready[AxiMstPortCount];
  axi_in_ar_chan_t axi_s_ar[AxiMstPortCount];
  logic            axi_s_ar_valid[AxiMstPortCount];
  logic            axi_s_ar_ready[AxiMstPortCount];
  axi_in_r_chan_t  axi_s_r[AxiMstPortCount];
  logic            axi_s_r_valid[AxiMstPortCount];
  logic            axi_s_r_ready[AxiMstPortCount];

  for (genvar i = 0; i < AxiMstPortCount; i++) begin
    assign axi_s_aw[i]          = mst_req[i].aw;
    assign axi_s_aw_valid[i]    = mst_req[i].aw_valid;
    assign mst_resp[i].aw_ready = axi_s_aw_ready[i];
    assign axi_s_w[i]           = mst_req[i].w;
    assign axi_s_w_valid[i]     = mst_req[i].w_valid;
    assign mst_resp[i].w_ready  = axi_s_w_ready[i];
    assign mst_resp[i].b        = axi_s_b[i];
    assign mst_resp[i].b_valid  = axi_s_b_valid[i];
    assign axi_s_b_ready[i]     = mst_req[i].b_ready;
    assign axi_s_ar[i]          = mst_req[i].ar;
    assign axi_s_ar_valid[i]    = mst_req[i].ar_valid;
    assign mst_resp[i].ar_ready = axi_s_ar_ready[i];
    assign mst_resp[i].r        = axi_s_r[i];
    assign mst_resp[i].r_valid  = axi_s_r_valid[i];
    assign axi_s_r_ready[i]     = mst_req[i].r_ready;
  end

  // Manager Port
  axi_out_aw_chan_t axi_m_aw[AxiSlvPortCount];
  logic             axi_m_aw_valid[AxiSlvPortCount];
  logic             axi_m_aw_ready[AxiSlvPortCount];
  axi_in_w_chan_t   axi_m_w[AxiSlvPortCount];
  logic             axi_m_w_valid[AxiSlvPortCount];
  logic             axi_m_w_ready[AxiSlvPortCount];
  axi_out_b_chan_t  axi_m_b[AxiSlvPortCount];
  logic             axi_m_b_valid[AxiSlvPortCount];
  logic             axi_m_b_ready[AxiSlvPortCount];
  axi_out_ar_chan_t axi_m_ar[AxiSlvPortCount];
  logic             axi_m_ar_valid[AxiSlvPortCount];
  logic             axi_m_ar_ready[AxiSlvPortCount];
  axi_out_r_chan_t  axi_m_r[AxiSlvPortCount];
  logic             axi_m_r_valid[AxiSlvPortCount];
  logic             axi_m_r_ready[AxiSlvPortCount];

  for (genvar i = 0; i < AxiSlvPortCount; i++) begin
    assign slv_req[i].aw       = axi_m_aw[i];
    assign slv_req[i].aw_valid = axi_m_aw_valid[i];
    assign axi_m_aw_ready[i]   = slv_resp[i].aw_ready;
    assign slv_req[i].w        = axi_m_w[i];
    assign slv_req[i].w_valid  = axi_m_w_valid[i];
    assign axi_m_w_ready[i]    = slv_resp[i].w_ready;
    assign axi_m_b[i]          = slv_resp[i].b;
    assign axi_m_b_valid[i]    = slv_resp[i].b_valid;
    assign slv_req[i].b_ready  = axi_m_b_ready[i];
    assign slv_req[i].ar       = axi_m_ar[i];
    assign slv_req[i].ar_valid = axi_m_ar_valid[i];
    assign axi_m_ar_ready[i]   = slv_resp[i].ar_ready;
    assign axi_m_r[i]          = slv_resp[i].r;
    assign axi_m_r_valid[i]    = slv_resp[i].r_valid;
    assign slv_req[i].r_ready  = axi_m_r_ready[i];
  end

  axe_axi_xbar #(
    .NumSubPorts    ( uint32_t'(AxiMstPortCount) ),
    .NumManPorts    ( uint32_t'(AxiSlvPortCount) ),
    .MaxSubTxn      ( 4                          ),
    .MaxManTxn      ( 4                          ),
    .FallThrough    ( 1'b0                       ),
    .LatencyMode    ( axi_xbar_pkg::NO_LATENCY   ),
    .LatencyCross   ( 0                          ),
    .SubAxiIdWidth  ( uint32_t'(AxiIdWidthIn)    ),
    .UniqueIds      ( 1'b0                       ),
    .AxiIdUsedWidth ( uint32_t'(AxiIdWidthIn)    ),
    .AxiAddrWidth   ( uint32_t'(AxiAddrWidth)    ),
    .NumAddrRules   ( uint32_t'(AxiRuleCount)    ),
    .SupportAtops   ( 1'b1                       ),
    .Connectivity   ( '1                         ),
    .axi_s_aw_t     ( axi_in_aw_chan_t           ),
    .axi_m_aw_t     ( axi_out_aw_chan_t          ),
    .axi_w_t        ( axi_in_w_chan_t            ),
    .axi_s_b_t      ( axi_in_b_chan_t            ),
    .axi_m_b_t      ( axi_out_b_chan_t           ),
    .axi_s_ar_t     ( axi_in_ar_chan_t           ),
    .axi_m_ar_t     ( axi_out_ar_chan_t          ),
    .axi_s_r_t      ( axi_in_r_chan_t            ),
    .axi_m_r_t      ( axi_out_r_chan_t           ),
    .addr_rule_t    ( xbar_rule_t                )
  ) i_axi_xbar (
    .i_clk               ( clk_i                       ),
    .i_rst_n             ( sys_rst_n                   ),
    .i_axi_s_aw          ( axi_s_aw                    ),
    .i_axi_s_aw_valid    ( axi_s_aw_valid              ),
    .o_axi_s_aw_ready    ( axi_s_aw_ready              ),
    .i_axi_s_w           ( axi_s_w                     ),
    .i_axi_s_w_valid     ( axi_s_w_valid               ),
    .o_axi_s_w_ready     ( axi_s_w_ready               ),
    .o_axi_s_b           ( axi_s_b                     ),
    .o_axi_s_b_valid     ( axi_s_b_valid               ),
    .i_axi_s_b_ready     ( axi_s_b_ready               ),
    .i_axi_s_ar          ( axi_s_ar                    ),
    .i_axi_s_ar_valid    ( axi_s_ar_valid              ),
    .o_axi_s_ar_ready    ( axi_s_ar_ready              ),
    .o_axi_s_r           ( axi_s_r                     ),
    .o_axi_s_r_valid     ( axi_s_r_valid               ),
    .i_axi_s_r_ready     ( axi_s_r_ready               ),
    .o_axi_m_aw          ( axi_m_aw                    ),
    .o_axi_m_aw_valid    ( axi_m_aw_valid              ),
    .i_axi_m_aw_ready    ( axi_m_aw_ready              ),
    .o_axi_m_w           ( axi_m_w                     ),
    .o_axi_m_w_valid     ( axi_m_w_valid               ),
    .i_axi_m_w_ready     ( axi_m_w_ready               ),
    .i_axi_m_b           ( axi_m_b                     ),
    .i_axi_m_b_valid     ( axi_m_b_valid               ),
    .o_axi_m_b_ready     ( axi_m_b_ready               ),
    .o_axi_m_ar          ( axi_m_ar                    ),
    .o_axi_m_ar_valid    ( axi_m_ar_valid              ),
    .i_axi_m_ar_ready    ( axi_m_ar_ready              ),
    .i_axi_m_r           ( axi_m_r                     ),
    .i_axi_m_r_valid     ( axi_m_r_valid               ),
    .o_axi_m_r_ready     ( axi_m_r_ready               ),
    .i_addr_map          ( addr_map                    ),
    .i_default_m_port_en ( '{default: 1'b1}            ),
    .i_default_m_port    ( '{default: ERROR}           )
  );

  assign mst_req[NOC] = axi_in_req_i;
  assign axi_in_resp_o = mst_resp[NOC];

  // Route external out of system
  axe_axi_riscv_atomics #(
    .AxiAddrWidth     ( AxiAddrWidth      ),
    .AxiDataWidth     ( AxiDataWidth      ),
    .AxiIdWidth       ( AxiIdWidthOut     ),
    .AxiUserWidth     ( AxiUserWidth      ),
    .AxiMaxReadTxns   ( 4                 ),
    .AxiMaxWriteTxns  ( 4                 ),
    .RiscvWordWidth   ( CVA6Cfg.XLEN      ),
    .NumCuts          ( 1                 ),
    .axi_aw_t         ( axi_out_aw_chan_t ),
    .axi_w_t          ( axi_in_w_chan_t   ),
    .axi_b_t          ( axi_out_b_chan_t  ),
    .axi_ar_t         ( axi_out_ar_chan_t ),
    .axi_r_t          ( axi_out_r_chan_t  )
  ) i_axi_riscv_atomics (
    .i_clk            ( clk_i                       ),
    .i_rst_n          ( rst_ni                      ),
    .i_axi_s_aw       ( slv_req[DRAM].aw            ),
    .i_axi_s_aw_valid ( slv_req[DRAM].aw_valid      ),
    .o_axi_s_aw_ready ( slv_resp[DRAM].aw_ready     ),
    .i_axi_s_w        ( slv_req[DRAM].w             ),
    .i_axi_s_w_valid  ( slv_req[DRAM].w_valid       ),
    .o_axi_s_w_ready  ( slv_resp[DRAM].w_ready      ),
    .o_axi_s_b        ( slv_resp[DRAM].b            ),
    .o_axi_s_b_valid  ( slv_resp[DRAM].b_valid      ),
    .i_axi_s_b_ready  ( slv_req[DRAM].b_ready       ),
    .i_axi_s_ar       ( slv_req[DRAM].ar            ),
    .i_axi_s_ar_valid ( slv_req[DRAM].ar_valid      ),
    .o_axi_s_ar_ready ( slv_resp[DRAM].ar_ready     ),
    .o_axi_s_r        ( slv_resp[DRAM].r            ),
    .o_axi_s_r_valid  ( slv_resp[DRAM].r_valid      ),
    .i_axi_s_r_ready  ( slv_req[DRAM].r_ready       ),
    .o_axi_m_aw       ( axi_out_req_o.aw            ),
    .o_axi_m_aw_valid ( axi_out_req_o.aw_valid      ),
    .i_axi_m_aw_ready ( axi_out_resp_i.aw_ready     ),
    .o_axi_m_w        ( axi_out_req_o.w             ),
    .o_axi_m_w_valid  ( axi_out_req_o.w_valid       ),
    .i_axi_m_w_ready  ( axi_out_resp_i.w_ready      ),
    .i_axi_m_b        ( axi_out_resp_i.b            ),
    .i_axi_m_b_valid  ( axi_out_resp_i.b_valid      ),
    .o_axi_m_b_ready  ( axi_out_req_o.b_ready       ),
    .o_axi_m_ar       ( axi_out_req_o.ar            ),
    .o_axi_m_ar_valid ( axi_out_req_o.ar_valid      ),
    .i_axi_m_ar_ready ( axi_out_resp_i.ar_ready     ),
    .i_axi_m_r        ( axi_out_resp_i.r            ),
    .i_axi_m_r_valid  ( axi_out_resp_i.r_valid      ),
    .o_axi_m_r_ready  ( axi_out_req_o.r_ready       )
  );

  // Generate AXI error for all non mapped addresses
  axe_axi_err_sub #(
    .AxiIdWidth ( AxiIdWidthOut     ),
    .DataWidth  ( AxiDataWidth      ),
    .axi_aw_t   ( axi_out_aw_chan_t ),
    .axi_w_t    ( axi_out_w_chan_t  ),
    .axi_b_t    ( axi_out_b_chan_t  ),
    .axi_ar_t   ( axi_out_ar_chan_t ),
    .axi_r_t    ( axi_out_r_chan_t  )
  ) i_axe_axi_err_sub (
    .i_clk            ( clk_i                   ),
    .i_rst_n          ( rst_ni                  ),
    .i_axi_s_aw       ( slv_req[ERROR].aw        ),
    .i_axi_s_aw_valid ( slv_req[ERROR].aw_valid  ),
    .o_axi_s_aw_ready ( slv_resp[ERROR].aw_ready ),
    .i_axi_s_w        ( slv_req[ERROR].w         ),
    .i_axi_s_w_valid  ( slv_req[ERROR].w_valid   ),
    .o_axi_s_w_ready  ( slv_resp[ERROR].w_ready  ),
    .o_axi_s_b        ( slv_resp[ERROR].b        ),
    .o_axi_s_b_valid  ( slv_resp[ERROR].b_valid  ),
    .i_axi_s_b_ready  ( slv_req[ERROR].b_ready   ),
    .i_axi_s_ar       ( slv_req[ERROR].ar        ),
    .i_axi_s_ar_valid ( slv_req[ERROR].ar_valid  ),
    .o_axi_s_ar_ready ( slv_resp[ERROR].ar_ready ),
    .o_axi_s_r        ( slv_resp[ERROR].r        ),
    .o_axi_s_r_valid  ( slv_resp[ERROR].r_valid  ),
    .i_axi_s_r_ready  ( slv_req[ERROR].r_ready   )
  );


  ///////////////
  // CVA6V Top //
  ///////////////

  logic [NrHarts-1:0] debug_req;
  logic [NrHarts-1:0] debug_rst_halt_req;
  assign debug_req          = '0;
  assign trace_debug_req_o  = debug_req;
  assign debug_rst_halt_req = '0;

  logic [NrHarts-1:0] ipi;      // inter processor interrupts
  logic [NrHarts-1:0] time_irq; // timer interrupts

  logic [NrHarts-1:0][MemPortCount-1:0]                             mem_req_valid;
  logic [NrHarts-1:0][MemPortCount-1:0]                             mem_req_ready;
  logic [NrHarts-1:0][MemPortCount-1:0][MemPortAddrWidth      -1:0] mem_req_addr;
  logic [NrHarts-1:0][MemPortCount-1:0]                             mem_req_we;
  logic [NrHarts-1:0][MemPortCount-1:0][MemPortBeWidth        -1:0] mem_req_be;
  logic [NrHarts-1:0][MemPortCount-1:0][MemPortWidth          -1:0] mem_req_wdata;
  logic [NrHarts-1:0][MemPortCount-1:0]                             mem_res_valid;
  logic [NrHarts-1:0][MemPortCount-1:0][MemPortWidth          -1:0] mem_res_rdata;
  logic [NrHarts-1:0][MemPortCount-1:0]                             mem_res_err;

  // Set memory regions
  logic [MemRegionCount-1:0][CVA6Cfg.PLEN        -1:0] memreg_addr;
  logic [MemRegionCount-1:0][$clog2(CVA6Cfg.PLEN)-1:0] memreg_size;
  logic [MemRegionCount-1:0]                           memreg_tcdm;
  for (genvar i = 0; i < MemRegionCount; i++) begin
    assign memreg_addr[i] = CVA6Cfg.PLEN'(L1Base) + (CVA6Cfg.PLEN'(i*L1Size/uint64_t'(MemRegionCount)));
    assign memreg_size[i] = $clog2(CVA6Cfg.PLEN)'($clog2(L1Size/uint64_t'(MemRegionCount)));
    assign memreg_tcdm[i] = 1'b1;
  end
  logic [NrHarts-1:0][PerfEventPortCount-2:0][CVA6Cfg.PLEN-2:0]  cva6v_perf_event_addr_full;
  logic [NrHarts-1:0][PerfEventAddrWidth-1:0] cva6v_perf_event_addr_last;

  for (genvar i = 0; i < NrHarts; i++) begin : gen_cva6v_top
    logic [CVA6Cfg.XLEN-1:0] hart_id;
    assign hart_id = hart_id_i + CVA6Cfg.XLEN'(i);

    for (genvar j = 0; j < PerfEventPortCount-1; j++) begin : gen_assign_perf_entry_addr
      assign perf_cntr_instr_entry_addr[i][j] = cva6v_perf_event_addr_full[i][j][PerfEventAddrWidth-1:0];
    end
    assign perf_cntr_instr_entry_addr[i][PerfEventPortCount-1] = cva6v_perf_event_addr_last[i][PerfEventAddrWidth-1:0];

    cva6v_top #(
      .axi_aw_chan_t       ( axi_in_aw_chan_t       ),
      .axi_w_chan_t        ( axi_in_w_chan_t        ),
      .axi_b_chan_t        ( axi_in_b_chan_t        ),
      .axi_ar_chan_t       ( axi_in_ar_chan_t       ),
      .axi_r_chan_t        ( axi_in_r_chan_t        ),
      .axi_req_t           ( axi_in_req_t           ),
      .axi_rsp_t           ( axi_in_resp_t          ),
      .rvfi_probes_t       ( rvfi_probes_t          ),
      .raptor_trace_sigs_t ( raptor_trace_sigs_t    ),
      .riscv_etrace_t      ( riscv_etrace_t         ),
      .CVA6VConfig         ( CVA6VConfig            )
    ) i_cva6v_top (
      .clk_i                            ( clk_i                             ),
      .rst_ni                           ( sys_rst_n                         ),
      .boot_addr_i                      ( boot_addr_i                       ),
      .hart_id_i                        ( hart_id                           ),
      .memreg_addr_i                    ( memreg_addr                       ),
      .memreg_size_i                    ( memreg_size                       ),
      .memreg_tcdm_i                    ( memreg_tcdm                       ),
      .irq_i                            ( irq[i]                            ),
      .ipi_i                            ( ipi[i]                            ),
      .time_irq_i                       ( time_irq[i]                       ),
      .platform_irq_i                   ( platform_irq[i]                   ),
      .debug_req_i                      ( debug_req[i]                      ),
      .debug_rst_halt_req_i             ( debug_rst_halt_req[i]             ),
      .debug_stop_time_o                ( /* Unused */                      ),
      .hart_is_wfi_o                    ( /* Unused */                      ),
      .hart_unavail_o                   ( /* Unused */                      ),
      .hart_under_reset_o               ( /* Unused */                      ),
      .axi_req_o                        ( mst_req[uint32_t'(CVA6)+i]        ),
      .axi_resp_i                       ( mst_resp[uint32_t'(CVA6)+i]       ),
      .mem_req_valid_o                  ( mem_req_valid[i]                  ),
      .mem_req_ready_i                  ( mem_req_ready[i]                  ),
      .mem_req_addr_o                   ( mem_req_addr[i]                   ),
      .mem_req_we_o                     ( mem_req_we[i]                     ),
      .mem_req_be_o                     ( mem_req_be[i]                     ),
      .mem_req_wdata_o                  ( mem_req_wdata[i]                  ),
      .mem_res_valid_i                  ( mem_res_valid[i]                  ),
      .mem_res_rdata_i                  ( mem_res_rdata[i]                  ),
      .mem_res_err_i                    ( mem_res_err[i]                    ),
      .perf_cntr_fu_status_o            ( perf_cntr_fu_status[i]            ),
      .perf_cntr_dispatch_queue_full_o  ( perf_cntr_dispatch_queue_full[i]  ),
      .perf_cntr_dispatch_queue_empty_o ( perf_cntr_dispatch_queue_empty[i] ),
      .perf_cntr_commit_queue_full_o    ( perf_cntr_commit_queue_full[i]    ),
      .perf_cntr_commit_queue_empty_o   ( perf_cntr_commit_queue_empty[i]   ),
      .perf_event_addr_full_o           ( cva6v_perf_event_addr_full[i]     ),
      .perf_event_addr_last_o           ( cva6v_perf_event_addr_last[i]     ),
      .perf_event_deltas_o              ( perf_cntr_instr_event_deltas[i]   ),
      .rvfi_probes_o                    ( rvfi_probes_o[i]                  ),
      .trace_raptor_o                   ( trace_raptor_o[i]                 ),
      .etrace_o                         ( etrace_o[i]                       ),
      .impl_i                           ( '0                                ),
      .impl_o                           ( /* Unused */                      )
    );
  end


  ///////////
  // CLINT //
  ///////////

  gc_clint #(
    .AxiAddrWidth ( AxiAddrWidth   ),
    .AxiDataWidth ( AxiDataWidth   ),
    .AxiIdWidth   ( AxiIdWidthOut  ),
    .NrHarts      ( NrHarts        ),
    .axi_req_t    ( axi_out_req_t  ),
    .axi_resp_t   ( axi_out_resp_t )
  ) i_gc_clint (
    .clk_i       ( clk_i           ),
    .rst_ni      ( rst_ni          ),
    .axi_req_i   ( slv_req [CLINT] ),
    .axi_resp_o  ( slv_resp[CLINT] ),
    .timer_irq_o ( time_irq        ),
    .ipi_o       ( ipi             )
  );


  ///////////////////
  // Perf Counters //
  ///////////////////

  cva6v_perf_counters_top #(
    .NrHarts                 ( NrHarts                 ),
    .EventCount              ( PerfEventCount          ),
    .AxiAddrWidth            ( AxiAddrWidth            ),
    .AxiDataWidth            ( AxiDataWidth            ),
    .AxiIdWidth              ( AxiIdWidthOut           ),
    .AxiUserWidth            ( AxiUserWidth            ),
    .axi_req_t               ( axi_out_req_t           ),
    .axi_rsp_t               ( axi_out_resp_t          ),
    .cva6v_config_t          ( cva6v_config_t          ),
    .CVA6VConfig             ( CVA6VConfig             ),
    .L1Latency               ( L1Latency               )
  ) i_perf_counters (
    .clk_i,
    .rst_ni,
    .axi_req_i                    ( slv_req [PERF_CNTRS]           ),
    .axi_rsp_o                    ( slv_resp[PERF_CNTRS]           ),
    .trace_fu_status_i            ( perf_cntr_fu_status            ),
    .trace_dispatch_queue_full_i  ( perf_cntr_dispatch_queue_full  ),
    .trace_dispatch_queue_empty_i ( perf_cntr_dispatch_queue_empty ),
    .trace_commit_queue_full_i    ( perf_cntr_commit_queue_full    ),
    .trace_commit_queue_empty_i   ( perf_cntr_commit_queue_empty   ),
    .trace_instr_entry_addr_i     ( perf_cntr_instr_entry_addr     ),
    .trace_instr_event_delta_i    ( perf_cntr_instr_event_deltas   )
  );


  ///////////////
  // L1 Memory //
  ///////////////

  localparam MemReqCount = NrHarts * MemPortCount + 1;

  /////////////////
  // CVA6 Request

  logic                            cva6_mem_req_valid;
  logic                            cva6_mem_req_gnt;
  logic [CVA6Cfg.AxiAddrWidth-1:0] cva6_mem_req_addr;
  logic [CVA6Cfg.XLEN        -1:0] cva6_mem_req_wdata, cva6_mem_req_rdata;
  logic [CVA6Cfg.XLEN/8      -1:0] cva6_mem_req_strb;
  logic                            cva6_mem_req_we;
  logic                            cva6_mem_req_rvalid;

  verif_cva6v_axi_to_mem #(
    .axi_req_t  ( axi_out_req_t  ),
    .axi_resp_t ( axi_out_resp_t ),
    .AddrWidth  ( AxiAddrWidth   ),
    .DataWidth  ( AxiDataWidth   ),
    .IdWidth    ( AxiIdWidthOut  ),
    .NumBanks   ( 1              )
  ) i_axi_to_mem (
    .clk_i        ( clk_i               ),
    .rst_ni       ( sys_rst_n           ),
    .busy_o       ( /* Unused */        ),
    .axi_req_i    ( slv_req [L1_MEMORY] ),
    .axi_resp_o   ( slv_resp[L1_MEMORY] ),
    .mem_req_o    ( cva6_mem_req_valid  ),
    .mem_gnt_i    ( cva6_mem_req_gnt    ),
    .mem_addr_o   ( cva6_mem_req_addr   ),
    .mem_wdata_o  ( cva6_mem_req_wdata  ),
    .mem_strb_o   ( cva6_mem_req_strb   ),
    .mem_atop_o   ( /* Unused */        ),
    .mem_we_o     ( cva6_mem_req_we     ),
    .mem_rvalid_i ( cva6_mem_req_rvalid ),
    .mem_rdata_i  ( cva6_mem_req_rdata  )
  );

  //////////////////////
  // TCDM Interconnect

  localparam int unsigned L1WordsBankCount = uint32_t'(L1Size)/(MemPortWidth/8)/L1BankCount;

  `MEM_TYPEDEF_ALL(
    tcdm,
    logic [MemPortAddrWidth-1:0],
    logic [MemPortWidth    -1:0],
    logic [MemPortBeWidth  -1:0],
    logic
  )
  `MEM_TYPEDEF_ALL(
    l1,
    logic [$clog2(L1WordsBankCount)-1:0],
    logic [MemPortWidth            -1:0],
    logic [MemPortBeWidth          -1:0],
    logic
  )

  tcdm_req_t [MemReqCount-1:0] tcdm_req;
  tcdm_rsp_t [MemReqCount-1:0] tcdm_rsp;

  l1_req_t [L1BankCount-1:0] bank_req;
  l1_rsp_t [L1BankCount-1:0] bank_rsp;

  cva6v_vector_fabric #(
    .NumInp                ( MemReqCount              ),
    .NumOut                ( L1BankCount              ),
    .tcdm_req_t            ( tcdm_req_t               ),
    .tcdm_rsp_t            ( tcdm_rsp_t               ),
    .mem_req_t             ( l1_req_t                 ),
    .mem_rsp_t             ( l1_rsp_t                 ),
    .MemAddrWidth          ( $clog2(L1WordsBankCount) ),
    .DataWidth             ( MemPortWidth             ),
    .MemoryResponseLatency ( L1Latency                )
  ) i_cva6v_vector_fabric (
    .clk_i     ( clk_i    ),
    .rst_ni    ( sys_rst_n),
    .req_i     ( tcdm_req ),
    .rsp_o     ( tcdm_rsp ),
    .mem_req_o ( bank_req ),
    .mem_rsp_i ( bank_rsp )
  );

  ///////////////////
  // Raptor req/rsp

  for (genvar i = 0; i < NrHarts; i++) begin : gen_hart_req_rsp
    for (genvar p = 0; p < MemPortCount; p++) begin : gen_raptor_tcdm_req_rsp
      // request
      assign tcdm_req[i*MemPortCount+p].q_valid = mem_req_valid[i][p];
      assign tcdm_req[i*MemPortCount+p].q.addr  = mem_req_addr [i][p];
      assign tcdm_req[i*MemPortCount+p].q.write = mem_req_we   [i][p];
      assign tcdm_req[i*MemPortCount+p].q.data  = mem_req_wdata[i][p];
      assign tcdm_req[i*MemPortCount+p].q.strb  = mem_req_be   [i][p];
      assign tcdm_req[i*MemPortCount+p].q.user  = '0;

      // response
      assign mem_req_ready[i][p] = tcdm_rsp[i*MemPortCount+p].q_ready;
      assign mem_res_valid[i][p] = tcdm_rsp[i*MemPortCount+p].p_valid;
      assign mem_res_rdata[i][p] = tcdm_rsp[i*MemPortCount+p].p.data;
      assign mem_res_err  [i][p] = '0;
    end
  end

  ////////////////
  // AXI req/rsp

  // Delay response data shift amount
  // NOTE: If we simulate higher L1 latencies, this would need to be a fifo
  logic [RaptorToCVA6DataRatioWidth-1:0] cva6_rsp_data_shamt_d, cva6_rsp_data_shamt_q;
  `FFL(cva6_rsp_data_shamt_q, cva6_rsp_data_shamt_d, cva6_mem_req_valid, '0);

  // request
  assign tcdm_req[MemReqCount-1].q_valid = cva6_mem_req_valid;
  assign tcdm_req[MemReqCount-1].q.addr  = CVA6VConfig.MemPortAddrWidth'(cva6_mem_req_addr);
  assign tcdm_req[MemReqCount-1].q.write = cva6_mem_req_we;
  if (MemPortWidth == AxiDataWidth) begin : gen_tcdm_req_strb
    assign tcdm_req[MemReqCount-1].q.data = cva6_mem_req_wdata;
    assign tcdm_req[MemReqCount-1].q.strb = cva6_mem_req_strb;
    assign cva6_rsp_data_shamt_d          = '0;
  end else begin
    assign tcdm_req[MemReqCount-1].q.data = {RaptorToCVA6DataRatio{cva6_mem_req_wdata}};
    assign tcdm_req[MemReqCount-1].q.strb = MemPortBeWidth'(cva6_mem_req_strb) <<
                                            (cva6_rsp_data_shamt_d * SoCAxiBeWidth);
    assign cva6_rsp_data_shamt_d          = cva6_mem_req_addr[$clog2(MemPortBeWidth)-1:$clog2(SoCAxiBeWidth)];
  end
  assign tcdm_req[MemReqCount-1].q.user  = '0;

  // response
  assign cva6_mem_req_rvalid = tcdm_rsp[MemReqCount-1].p_valid;
  assign cva6_mem_req_rdata  = AxiDataWidth'(tcdm_rsp[MemReqCount-1].p.data >>
                                             (cva6_rsp_data_shamt_q * AxiDataWidth));
  assign cva6_mem_req_gnt    = tcdm_rsp[MemReqCount-1].q_ready;

  /////////////
  // L1 Banks

  for (genvar b = 0; b < L1BankCount; b++) begin : gen_l1banks
    logic [63:0] addr_offset;
    assign addr_offset = longint'(L1Base) + b * (longint'(MemPortWidth)/8);

    mini_soc_tc_sram #(
      .DataWidth  ( MemPortWidth                           ),
      .NumWords   ( L1WordsBankCount                       ),
      .NumPorts   ( 1                                      ),
      .Latency    ( L1Latency                              ),
      .SimInit    ( "none"                                 ),
      .BusAlign   ( $clog2(L1BankCount * (MemPortWidth/8)) )
    ) i_l1_mem (
      .clk_i         ( clk_i               ),
      .rst_ni        ( sys_rst_n           ),
      .req_i         ( bank_req[b].q_valid ),
      .we_i          ( bank_req[b].q.write ),
      .addr_i        ( bank_req[b].q.addr  ),
      .wdata_i       ( bank_req[b].q.data  ),
      .be_i          ( bank_req[b].q.strb  ),
      .rdata_o       ( bank_rsp[b].p.data  ),
      .addr_offset_i ( addr_offset         )
    );

    assign bank_rsp[b].q_ready = 1'b1;

    cva6v_shift_reg #(
      .dtype  ( logic               ),
      .Depth  ( L1Latency           )
    ) i_l1_mem_valid_shift_reg (
      .clk_i  ( clk_i               ),
      .rst_ni ( rst_ni              ),
      .d_i    ( bank_req[b].q_valid ),
      .d_o    ( bank_rsp[b].p_valid )
    );
  end : gen_l1banks


  ////////////////
  // Assertions //
  ////////////////

  if (AxiIdWidthIn < 4)
    $error("[gc_system] `AxiIdWidthIn` needs to be at least 4-bits. ");

  if (L1BankCount != 2**$clog2(L1BankCount))
    $error("[gc_system] The L1 bank count (L1BankCount) needs to be a power of two.");

  if (L1BankCount * MemPortBeWidth > L1Size)
    $error("[gc_system] The L1 Size is not big enough for the number of banks and raptor memory ports.");

  if (MemPortWidth < AxiDataWidth)
    $error("[gc_system] The MemPortWidth has to be bigger or equal to the AxiDataWidth");

  if (PerfCntrsBase[cva6v_perf_cntr_reg_reg_pkg::BlockAw-1:0] != '0)
    $error(
        "[gc_system] PerfCntrsBase must be aligned to the perf counter address width (%d) but had value: 0x%016x",
        cva6v_perf_cntr_reg_reg_pkg::BlockAw,
        PerfCntrsBase
    );

endmodule : gc_system
