module hdl_top;
  // Time unit and precision
  timeunit 1ps; timeprecision 1ps;

  import cva6v_ai_core_pkg::*;
  import raptor_pkg::*;
  import cva6v_ariane_pkg::*;
  import cva6v_config_pkg::*;

  import "DPI-C" function void load_binary_file (input string filename);

  `include "axi/typedef.svh"
  `include "cva6v/include/rvfi_types.svh"
  `include "cva6v/include/cva6v/cva6v_tracing.svh"

  `include "cva6v_dv_typedefs.svh"

  realtime CLK_PERIOD = 0.625ns;  // 1.6GHz
  logic    clk_i;
  logic    rst_ni;
  logic    sys_rst_ni;
  logic    hart_is_wfi_i;

  // Tracer
  logic                                                  tb_exit_o;
  rvfi_probes_t                                          rvfi_probes;
  rvfi_instr_t   [CVA6VConfig.CVA6Cfg.NrCommitPorts-1:0] rvfi_instr;
  rvfi_csr_t                                             rvfi_csr;
  raptor_trace_sigs_t                                    trace_raptor;
  rvvi_trace_t                                           rvvi_trace;

  //////////////////////
  // Types and Params //
  //////////////////////
  // Test Control
  int unsigned drain_cycles = 8000;

  // Raptor derived parameters
  localparam int unsigned NrHarts = 1;

  // L1
  localparam longint unsigned L1Base      = 64'h0800_0000;
  localparam longint unsigned L1Size      = 64'h0040_0000;
  localparam int     unsigned L1BankCount = 2 * MemPortCount;
  localparam int     unsigned L1Latency   = 3;

  // DRAM
  localparam longint unsigned DRAMBase = 64'h20_0000_0000;
  localparam longint unsigned DRAMSize = 64'h18_0000_0000;

  // Peripherals
  localparam longint unsigned PeriphBase = 64'h1000_0000;
  localparam longint unsigned PeriphSize = 64'h3000_0000;

  // Clint
  localparam longint unsigned ClintBase = PeriphBase + 64'h0001_0000;
  localparam longint unsigned ClintSize = 64'h0001_0000;

  // Clint
  localparam longint unsigned PerfCntrsBase = ClintBase + ClintSize;
  localparam longint unsigned PerfCntrsSize = 64'h0001_0000;

  // Size casting types
  typedef logic [31:0] uint32_t;
  typedef logic [63:0] uint64_t;

  // IRQs
  logic [1:0] irq_tb_line;

  //////////////////
  // SoC Axi Xbar //
  //////////////////

  // ID Width of `gc_system` input port.
  localparam GCSystemAxiIdWidthIn = 4;
  // AXI masters in gc_system: CVA6, NoC in
  localparam GCSystemAxiIdWidthOut = GCSystemAxiIdWidthIn + $clog2(NrHarts + 1);

  typedef logic [AxiAddrWidth-1:0]   axi_addr_t;
  typedef logic [AxiDataWidth-1:0]   axi_data_t;
  typedef logic [AxiDataWidth/8-1:0] axi_strb_t;
  typedef logic [AxiUserWidth-1:0]   axi_user_t;

  localparam int unsigned AxiSoCIdWidthIn = GCSystemAxiIdWidthOut;
  localparam int unsigned AxiSoCIdWidthOut = AxiSoCIdWidthIn;

  typedef logic [AxiSoCIdWidthIn-1:0] axi_id_in_t;         // 5
  typedef logic [AxiSoCIdWidthOut-1:0] axi_id_out_t;       // 5
  typedef logic [GCSystemAxiIdWidthIn-1:0] axi_id_gc_in_t; // 4

  `AXI_TYPEDEF_ALL(axi_soc_in, axi_addr_t, axi_id_in_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_ALL(axi_gc_in, axi_addr_t, axi_id_gc_in_t, axi_data_t, axi_strb_t, axi_user_t)

  axi_soc_in_req_t   axi_req;
  axi_soc_in_resp_t  axi_resp;

  cva6v_ai_core_pkg::riscv_etrace_t  riscv_etrace;

  // Dut
  gc_system #(
    // SoC AXI (slave ports) types
    .axi_out_ar_chan_t      ( axi_soc_in_ar_chan_t   ),
    .axi_out_aw_chan_t      ( axi_soc_in_aw_chan_t   ),
    .axi_out_w_chan_t       ( axi_soc_in_w_chan_t    ),
    .axi_out_b_chan_t       ( axi_soc_in_b_chan_t    ),
    .axi_out_r_chan_t       ( axi_soc_in_r_chan_t    ),
    .axi_out_req_t          ( axi_soc_in_req_t       ),
    .axi_out_resp_t         ( axi_soc_in_resp_t      ),
    // SoC AXI input (slave ports) types
    .axi_in_ar_chan_t       ( axi_gc_in_ar_chan_t    ),
    .axi_in_aw_chan_t       ( axi_gc_in_aw_chan_t    ),
    .axi_in_w_chan_t        ( axi_gc_in_w_chan_t     ),
    .axi_in_b_chan_t        ( axi_gc_in_b_chan_t     ),
    .axi_in_r_chan_t        ( axi_gc_in_r_chan_t     ),
    .axi_in_req_t           ( axi_gc_in_req_t        ),
    .axi_in_resp_t          ( axi_gc_in_resp_t       ),
    // CVA6V tracing types
    //.cva6_rvfi_instr_t      ( rvfi_instr_t         ),
    .rvfi_probes_t          ( rvfi_probes_t          ),
    .raptor_trace_sigs_t    ( raptor_trace_sigs_t    ),
    .riscv_etrace_t         ( riscv_etrace_t         ),
    // CVA6V configuration types
    .cva6_config_t          ( cva6v_config_pkg::cva6_cfg_t),
    .cva6v_config_t         ( cva6v_pkg::cva6v_config_t),
    // System Configuration
    .NrHarts                ( NrHarts                ),
    // Memory
    .L1Base                 ( L1Base                 ),
    .L1Size                 ( L1Size                 ),
    .L1BankCount            ( L1BankCount            ),
    .L1Latency              ( L1Latency              ),
    // DRAM mapping
    .DRAMBase               ( DRAMBase               ),
    .DRAMSize               ( DRAMSize               ),
    // Clint
    .ClintBase              ( ClintBase              ),
    .ClintSize              ( ClintSize              ),
    // Performance Counter Address Region
    .PerfCntrsBase          ( PerfCntrsBase          ),
    .PerfCntrsSize          ( PerfCntrsSize          ),
    // CVA6V configuration
    .CVA6VConfig            ( CVA6VConfig            )
  ) i_gc_system (
    .clk_i                  ( clk_i                  ),
    .rst_ni                 ( rst_ni                 ),
    .sys_rst_no             ( sys_rst_ni             ),
    .hart_id_i              ( '0                     ),
    .boot_addr_i            ( DRAMBase               ),
    .axi_out_req_o          ( axi_req                ),
    .axi_out_resp_i         ( axi_resp               ),
    .axi_in_req_i           ( '0                     ),
    .axi_in_resp_o          ( /* Unused */           ),
    .trace_debug_req_o      ( /* Unused */           ),
    .rvfi_probes_o          ( rvfi_probes            ),
    .trace_raptor_o         ( trace_raptor           ),
    .etrace_o               ( riscv_etrace           ),
    .irq_i                  ( irq_tb_line)
  );

  //////////
  // DRAM //
  //////////

  logic                      dram_req_valid;
  logic                      dram_req_gnt;
  logic [AxiAddrWidth  -1:0] dram_req_addr;
  logic [AxiDataWidth  -1:0] dram_req_wdata, dram_req_rdata;
  logic [AxiDataWidth/8-1:0] dram_req_strb;
  logic                      dram_req_we;
  logic                      dram_req_rvalid;

  localparam int unsigned DRAMLatency   = 20;

  verif_cva6v_axi_to_mem #(
    .axi_req_t  ( axi_soc_in_req_t  ),
    .axi_resp_t ( axi_soc_in_resp_t ),
    .AddrWidth  ( AxiAddrWidth      ),
    .DataWidth  ( AxiDataWidth      ),
    .IdWidth    ( AxiSoCIdWidthOut  ),
    .NumBanks   ( 1                 ),
    .BufDepth   ( DRAMLatency       )
  ) i_axi_to_dram (
    .clk_i        ( clk_i           ),
    .rst_ni       ( sys_rst_ni      ),
    .busy_o       ( /* Unused */    ),
    .axi_req_i    ( axi_req         ),
    .axi_resp_o   ( axi_resp        ),
    .mem_req_o    ( dram_req_valid  ),
    .mem_gnt_i    ( 1'b1            ),
    .mem_addr_o   ( dram_req_addr   ),
    .mem_wdata_o  ( dram_req_wdata  ),
    .mem_strb_o   ( dram_req_strb   ),
    .mem_atop_o   ( /* Unused */    ),
    .mem_we_o     ( dram_req_we     ),
    .mem_rvalid_i ( dram_req_rvalid ),
    .mem_rdata_i  ( dram_req_rdata  )
  );

  localparam longint unsigned DRAMNumWords  = DRAMSize / (AxiDataWidth / 8);
  mini_soc_tc_sram #(
    .DataWidth ( AxiDataWidth   ),
    .NumWords  ( DRAMNumWords   ),
    .NumPorts  ( 1              ),
    .Latency   ( DRAMLatency    ),
    .SimInit   ( "none"         ),
    .AddrWidth ( AxiAddrWidth-$clog2(AxiDataWidth/8) )
  ) i_dram (
    .clk_i         ( clk_i             ),
    .rst_ni        ( sys_rst_ni        ),
    .req_i         ( dram_req_valid    ),
    .we_i          ( dram_req_we       ),
    .addr_i        ( dram_req_addr[AxiAddrWidth-1:$clog2(AxiDataWidth/8)]),
    .wdata_i       ( dram_req_wdata    ),
    .be_i          ( dram_req_strb     ),
    .rdata_o       ( dram_req_rdata    ),
    .addr_offset_i ( 64'h0             ) // Using absolute addresses
  );

  // Delay request valid signal by DRAMLatency cycles
  cva6v_shift_reg #(
    .dtype  ( logic       ),
    .Depth  ( DRAMLatency )
  ) i_dram_req_valid_shift_reg (
    .clk_i  ( clk_i           ),
    .rst_ni ( sys_rst_ni      ),
    .d_i    ( dram_req_valid  ),
    .d_o    ( dram_req_rvalid )
  );

  // DV's RVVI Interface
  cva6v_rvvi_eot_if #(
    rvvi_trace_t
  ) rvvi_eot_if (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rvvi_i(rvvi_trace),
    .hart_is_wfi_i(hart_is_wfi_i),
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
    .clk_i          ( clk_i        ),
    .rst_ni         ( rst_ni       ),
    .rvfi_probes_i  ( rvfi_probes  ),
    .raptor_trace_i ( trace_raptor ),
    .rvvi_trace_o   ( rvvi_trace   )
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

  interrupt_generator i_interrupt_generator (
    .clk_i(clk_i),
    .begin_irq_driving(i_rvvi_tracer.begin_irq_driving),
    .end_irq_driving(i_rvvi_tracer.end_irq_driving),
    .irq_tb_line(irq_tb_line)
  );

`ifdef ADD_DUMP_IF
  cva6v_rvvi_dump_if rvvi_dump_if[CVA6VConfig.CVA6Cfg.NrCommitPorts](clk_i, rst_ni);
  `include "dump_connections.svh"
`endif

  always begin
    clk_i <= 1;
    #(CLK_PERIOD / 2);
    clk_i <= 0;
    #(CLK_PERIOD / 2);
  end

  initial begin
    $timeformat(-9, 3, " ns", 10);
    rst_ni = 0;
    #(CLK_PERIOD * 2);
    rst_ni = 1;
  end

  initial begin
    string binary;
    int drain_cycles_arg;
    int ticker_period_ns = 50_000; // 50 us
    void'($value$plusargs("TICKER_PERIOD_NS=%s", ticker_period_ns));

    // Check if DRAIN_CYCLES is provided, otherwise keep the default value
    if ($value$plusargs("MINISOC_DRAIN_CYCLES=%d", drain_cycles_arg)) begin
      drain_cycles = drain_cycles_arg;
    end

    fork
      forever begin
        #(1000*ticker_period_ns) // because of ps timeunit
        $display("[%t]: %m: [ticker] minisoc alive! Commit Port 0 current PC: 0x%0h", $time, i_cva6v_rvvi.rvvi_trace_o.pc_rdata[0]);
      end
    join_none

    void'($value$plusargs("elf_file=%s", binary));
    if (binary != "") begin
      load_binary_file(binary);
      $display("Load binary done! %s", binary);
    end else begin
      $error("Unable to find preload binary (%s).", binary);
      $finish(1);
    end
    rvvi_eot_if.wait_end_of_test(drain_cycles);
    $display("[%t] rvvi_eot_if.wait_end_of_test done!", $time);
    $finish;
  end

  final begin
    if ($test$plusargs("enable_irqs")) begin
      assert(i_rvvi_tracer.irq_trap_taken_cnt > 0) $display("[IRQ] At least one trap was taken!");
        else $fatal("[IRQ] Less irq traps (%0d) than irqs (%0d)!", i_rvvi_tracer.irq_trap_taken_cnt, i_interrupt_generator.irq_number);
    end
  end

`ifdef BREKER
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  trek_uvm i_trek_uvm();

  final begin
    uvm_report_server svr;
    svr = uvm_report_server::get_server();

     if (svr.get_severity_count(UVM_FATAL) +
         svr.get_severity_count(UVM_ERROR)
	       > 0)
       `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
     else
       `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    svr.report_summarize();
  end
`endif

  assign hart_is_wfi_i = i_gc_system.gen_cva6v_top[0].i_cva6v_top.hart_is_wfi_o;

endmodule : hdl_top
