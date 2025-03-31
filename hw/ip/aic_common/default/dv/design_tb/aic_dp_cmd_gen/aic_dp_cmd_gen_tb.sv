// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Design sanity testbench
///
module aic_dp_cmd_gen_tb;

  /////////////////////
  // Clock and Reset //
  /////////////////////
  parameter int unsigned TbResetCycles =      10;
  parameter int unsigned TbNumCycles   = 100_000;
  parameter int unsigned TbFreqMhz     =     900;

  parameter int unsigned TbSoftTimeout = 2 * TbNumCycles * int'(1000.0 / real'(TbFreqMhz));
  parameter int unsigned TbHardTimeout = 3 * TbNumCycles * int'(1000.0 / real'(TbFreqMhz));
  parameter int unsigned TbTickerTime  = 1_000_000;

  wire  tb_clk;
  logic tb_clk_en;
  wire  tb_rst;
  logic tb_rst_n;
  logic tb_flush;

  bit   tb_active, tb_done;

  axe_clk_generator u_axe_clk_generator (
    .i_enable(tb_clk_en),
    .o_clk   (tb_clk)
  );

  axe_rst_generator u_axe_rst_generator (
    .i_clk(tb_clk),
    .o_rst(tb_rst)
  );
  always_comb tb_rst_n = ~tb_rst;

  axe_timeout u_axe_timeout();


  initial begin : proc_clk
    automatic int unsigned RandCycles;
    automatic int unsigned RandSrcFreq;
    automatic int unsigned RandDstFreq;

    tb_clk_en <= 1'b1;
    tb_flush  <= 1'b0;
    tb_active <= 1'b0;
    tb_done   <= 1'b0;

    u_axe_timeout.timeout(TbSoftTimeout, TbHardTimeout);
    u_axe_timeout.ticker(TbTickerTime, "The TB is alive!");
    u_axe_clk_generator.set_clock(.freq_mhz(TbFreqMhz), .duty(50));
    u_axe_rst_generator.sync_rst(.duration_cycles(TbResetCycles));

    repeat (TbResetCycles+1) @(posedge tb_clk);

    tb_active <= 1'b1;
    $display("%t: %m: Tb is active.", $time);

    repeat (TbNumCycles) @(posedge tb_clk);
    tb_done <= 1'b1;
  end

  ///////////////////
  // Command Input //
  ///////////////////
  aic_dp_cmd_gen_pkg::cmdb_cmd_t     tb_cmdb_command;
  aic_dp_cmd_gen_pkg::cmd_format_e   tb_cmdb_format;
  aic_dp_cmd_gen_pkg::cmd_config_t   tb_cmdb_config;
  logic                              tb_cmdb_valid;
  logic                              tb_cmdb_ready;
  logic                              tb_cmdb_done;

  // TODO:
  initial begin : proc_commands
    tb_cmdb_command = '0;
    tb_cmdb_format  = aic_dp_cmd_gen_pkg::LoopsM1N0;
    tb_cmdb_config  = aic_dp_cmd_gen_pkg::cmd_config_t'('hAB);
    tb_cmdb_valid   = 1'b0;

    @(posedge tb_rst_n);

    ////////////////////////
    // Sanity Single Loop //
    ////////////////////////
    @(posedge tb_clk);
    tb_cmdb_command.view_struct.main_0 <= '{
      iteration: 2,
      length:   10,
      default:  '0
    };
    tb_cmdb_valid <= 1'b1;
    do @(posedge tb_clk); while (!tb_cmdb_ready);

    ////////////////////////
    // Sanity Three Loops //
    ////////////////////////
    tb_cmdb_format = aic_dp_cmd_gen_pkg::LoopsM3N0;
    tb_cmdb_command.view_struct.main_1 <= '{
      start:    30,
      iteration: 4,
      length:    3,
      default:  '0
    };
    tb_cmdb_command.view_struct.main_2 <= '{
      start:     50,
      iteration: 10,
      length:     5,
      default:   '0
    };
    do @(posedge tb_clk); while (!tb_cmdb_ready);
    //////////////////////////////////
    // Sanity Two Loops with nested //
    //////////////////////////////////
    tb_cmdb_format = aic_dp_cmd_gen_pkg::LoopsM2N2;
    tb_cmdb_command.view_struct.main_0 <= '{
      start:     0,
      iteration: 4,
      length:    10,
      default:  '0
    };
    tb_cmdb_command.view_struct.main_1 <= '{
      start:    30,
      iteration: 4,
      length:    3,
      default:  '0
    };
    tb_cmdb_command.view_struct.nested_0 <= '{
      start:     0,
      iteration: 10,
      length:    5,
      default:  '0
    };
    tb_cmdb_command.view_struct.nested_1_map_main = 1;
    tb_cmdb_command.view_struct.nested_1 <= '{
      start:    31,
      iteration: 4,
      length:    1,
      default:  '0
    };

    tb_cmdb_command.view_struct.main_2 <= '{
      default:   '0
    };
    do @(posedge tb_clk); while (!tb_cmdb_ready);

    tb_cmdb_valid <= 1'b0;
  end


  initial begin : proc_monitor_done
    repeat (3) begin
      do @(posedge tb_clk); while (!tb_cmdb_done);
    end
    repeat (10) @(posedge tb_clk);
    $display("All sanity commands done: Success!");
    $finish();
  end



  ////////////////////
  // AXI parameters //
  ////////////////////
  /// ID width
  parameter  int unsigned TbAxiIdWidth = 4;
  /// Address width
  parameter  int unsigned TbAxiAddrWidth = 16;
  /// Data width
  parameter  int unsigned TbAxiDataWidth = 64;
  /// Strobe width
  localparam int unsigned TbAxiStrbWidth = TbAxiDataWidth / 8;

  logic [  TbAxiIdWidth-1:0]         tb_axi_s_aw_id;
  logic [TbAxiAddrWidth-1:0]         tb_axi_s_aw_addr;
  axi_pkg::axi_len_t                 tb_axi_s_aw_len;
  axi_pkg::axi_size_t                tb_axi_s_aw_size;
  axi_pkg::axi_burst_t               tb_axi_s_aw_burst;
  logic                              tb_axi_s_aw_valid;
  logic                              tb_axi_s_aw_ready;
  logic [TbAxiDataWidth-1:0]         tb_axi_s_w_data;
  logic [TbAxiStrbWidth-1:0]         tb_axi_s_w_strb;
  logic                              tb_axi_s_w_last;
  logic                              tb_axi_s_w_valid;
  logic                              tb_axi_s_w_ready;
  logic [  TbAxiIdWidth-1:0]         tb_axi_s_b_id;
  axi_pkg::axi_resp_t                tb_axi_s_b_resp;
  logic                              tb_axi_s_b_valid;
  logic                              tb_axi_s_b_ready;
  logic [  TbAxiIdWidth-1:0]         tb_axi_s_ar_id;
  logic [TbAxiAddrWidth-1:0]         tb_axi_s_ar_addr;
  axi_pkg::axi_len_t                 tb_axi_s_ar_len;
  axi_pkg::axi_size_t                tb_axi_s_ar_size;
  axi_pkg::axi_burst_t               tb_axi_s_ar_burst;
  logic                              tb_axi_s_ar_valid;
  logic                              tb_axi_s_ar_ready;
  logic [  TbAxiIdWidth-1:0]         tb_axi_s_r_id;
  logic [TbAxiDataWidth-1:0]         tb_axi_s_r_data;
  axi_pkg::axi_resp_t                tb_axi_s_r_resp;
  logic                              tb_axi_s_r_last;
  logic                              tb_axi_s_r_valid;
  logic                              tb_axi_s_r_ready;


  always_comb tb_axi_s_aw_id    = '0;
  always_comb tb_axi_s_aw_addr  = '0;
  always_comb tb_axi_s_aw_len   = '0;
  always_comb tb_axi_s_aw_size  = '0;
  always_comb tb_axi_s_aw_burst = '0;
  always_comb tb_axi_s_aw_valid = '0;
  always_comb tb_axi_s_w_data   = '0;
  always_comb tb_axi_s_w_strb   = '0;
  always_comb tb_axi_s_w_last   = '0;
  always_comb tb_axi_s_w_valid  = '0;
  always_comb tb_axi_s_b_ready  = '0;
  always_comb tb_axi_s_ar_id    = '0;
  always_comb tb_axi_s_ar_addr  = '0;
  always_comb tb_axi_s_ar_len   = '0;
  always_comb tb_axi_s_ar_size  = '0;
  always_comb tb_axi_s_ar_burst = '0;
  always_comb tb_axi_s_ar_valid = '0;
  always_comb tb_axi_s_r_ready  = '0;


  /////////////////
  // Intructions //
  /////////////////
  aic_dp_cmd_gen_pkg::dummy_dp_command_t tb_dp_command_data;
  aic_dp_cmd_gen_pkg::metadata_t         tb_dp_command_metadata;
  aic_dp_cmd_gen_pkg::loop_iterations_t  tb_dp_command_iterations;
  logic                                  tb_dp_command_last;
  logic                                  tb_dp_command_valid;
  logic                                  tb_dp_command_ready;
  logic                                  tb_dp_done;

  // TODO:
  always_comb begin
    tb_dp_command_ready = 1'b1;
    tb_dp_done = tb_dp_command_ready & tb_dp_command_valid & tb_dp_command_last;
  end

  initial begin : proc_print_command
    forever begin
      @(posedge tb_clk);
      if (tb_dp_command_valid && tb_dp_command_ready)
        $display(
          "Command:                 %p\n", tb_dp_command_data,
          "Metadata:                %p\n", tb_dp_command_metadata,
          "Iterations.main_index:   %0d\n", tb_dp_command_iterations.main_index,
          "Iterations.main:         %0d\n", tb_dp_command_iterations.main,
          "Iterations.nested_0:     %0d\n", tb_dp_command_iterations.nested_0,
          "Iterations.nested_1:     %0d\n", tb_dp_command_iterations.nested_1,
          "Iterations.overall_last: %0d\n", tb_dp_command_iterations.overall_last,
          "Last:                    0b%0b\n", tb_dp_command_last
        );
    end
  end


  aic_dp_cmd_gen_pkg::loop_errors_t  tb_errors;


  ////////////////////////////
  // Custom memory Sideband //
  ////////////////////////////
  /// The depth of the memory
  parameter int unsigned TbDpCommandMemoryDepth = 2**13; // 32k

  typedef struct packed {
    logic reserved;
  } tb_ram_impl_inp_t;

  typedef struct packed {
    logic reserved;
  } tb_ram_impl_oup_t;

  tb_ram_impl_inp_t tb_ram_impl_inp;
  tb_ram_impl_oup_t tb_ram_impl_oup;

  always_comb tb_ram_impl_inp = '0;


  initial begin : proc_preload_commands
    aic_dp_cmd_gen_pkg::dummy_dp_command_t preload_data;
    aic_dp_cmd_gen_pkg::dummy_dp_command_t memory_content[TbDpCommandMemoryDepth];

    for (int unsigned memory_address = 0; memory_address < TbDpCommandMemoryDepth; memory_address++) begin
      preload_data = '{
        index: 32'(memory_address),
        data:  32'($urandom())
      };
      $display("Depositing[%0d]: %p", memory_address, preload_data);
      memory_content[memory_address] = preload_data;
    end
    force u_aic_dp_cmd_gen_dut.u_cmdblock_desc_mem.gen_ram.u_tc_ram.memory_q = memory_content;
  end

  aic_dp_cmd_gen #(
    .AxiIdWidth          (TbAxiIdWidth),
    .AxiAddrWidth        (TbAxiAddrWidth),
    .AxiDataWidth        (TbAxiDataWidth),
    .AxiEndpointStart    ('h0),
    .AxiEndpointSize     ('h0),
    .DpCommandMemoryDepth(TbDpCommandMemoryDepth),
    .MaxOutstanding      (3),
    .dp_command_t        (aic_dp_cmd_gen_pkg::dummy_dp_command_t),
    .MemImplKey          ("HS_RVT"),
    .ram_impl_inp_t      (tb_ram_impl_inp_t),
    .ram_impl_oup_t      (tb_ram_impl_oup_t)
  ) u_aic_dp_cmd_gen_dut (
    .i_clk                  (tb_clk),
    .i_rst_n                (tb_rst_n),
    .i_flush                (tb_flush),
    .i_test_mode            (1'b0),
    .i_cmdb_command         (tb_cmdb_command),
    .i_cmdb_format          (tb_cmdb_format),
    .i_cmdb_config          (tb_cmdb_config),
    .i_cmdb_valid           (tb_cmdb_valid),
    .o_cmdb_ready           (tb_cmdb_ready),
    .o_cmdb_done            (tb_cmdb_done),
    .i_axi_s_aw_id          (tb_axi_s_aw_id),
    .i_axi_s_aw_addr        (tb_axi_s_aw_addr),
    .i_axi_s_aw_len         (tb_axi_s_aw_len),
    .i_axi_s_aw_size        (tb_axi_s_aw_size),
    .i_axi_s_aw_burst       (tb_axi_s_aw_burst),
    .i_axi_s_aw_valid       (tb_axi_s_aw_valid),
    .o_axi_s_aw_ready       (tb_axi_s_aw_ready),
    .i_axi_s_w_data         (tb_axi_s_w_data),
    .i_axi_s_w_strb         (tb_axi_s_w_strb),
    .i_axi_s_w_last         (tb_axi_s_w_last),
    .i_axi_s_w_valid        (tb_axi_s_w_valid),
    .o_axi_s_w_ready        (tb_axi_s_w_ready),
    .o_axi_s_b_id           (tb_axi_s_b_id),
    .o_axi_s_b_resp         (tb_axi_s_b_resp),
    .o_axi_s_b_valid        (tb_axi_s_b_valid),
    .i_axi_s_b_ready        (tb_axi_s_b_ready),
    .i_axi_s_ar_id          (tb_axi_s_ar_id),
    .i_axi_s_ar_addr        (tb_axi_s_ar_addr),
    .i_axi_s_ar_len         (tb_axi_s_ar_len),
    .i_axi_s_ar_size        (tb_axi_s_ar_size),
    .i_axi_s_ar_burst       (tb_axi_s_ar_burst),
    .i_axi_s_ar_valid       (tb_axi_s_ar_valid),
    .o_axi_s_ar_ready       (tb_axi_s_ar_ready),
    .o_axi_s_r_id           (tb_axi_s_r_id),
    .o_axi_s_r_data         (tb_axi_s_r_data),
    .o_axi_s_r_resp         (tb_axi_s_r_resp),
    .o_axi_s_r_last         (tb_axi_s_r_last),
    .o_axi_s_r_valid        (tb_axi_s_r_valid),
    .i_axi_s_r_ready        (tb_axi_s_r_ready),
    .o_dp_command_data      (tb_dp_command_data),
    .o_dp_command_metadata  (tb_dp_command_metadata),
    .o_dp_command_iterations(tb_dp_command_iterations),
    .o_dp_command_last      (tb_dp_command_last),
    .o_dp_command_valid     (tb_dp_command_valid),
    .i_dp_command_ready     (tb_dp_command_ready),
    .i_dp_done              (tb_dp_done),
    .o_errors               (tb_errors),
    .i_ram_impl             (tb_ram_impl_inp),
    .o_ram_impl             (tb_ram_impl_oup)
  );
endmodule
