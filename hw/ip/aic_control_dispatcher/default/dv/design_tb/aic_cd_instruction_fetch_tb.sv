// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Design sanity testbench
///
module aic_cd_instruction_fetch_tb;
  ////////////////////
  // DUT Parameters //
  ////////////////////
  parameter int unsigned TbNumRequests = 10;

  parameter int unsigned TbNumDestinationIds    = 17;
  parameter int unsigned TbNumPatchModeEntries  = 8;
  parameter int unsigned TbNumPatchTableEntries = 16;
  parameter int unsigned TbNumLocalTokens       = 4;
  parameter int unsigned TbNumGlobalTokens      = 4;

  parameter int unsigned       TbAxiIdWidth             = axe_axi_default_types_pkg::WIDTH_ID_4;
  parameter int unsigned       TbAxiAddrWidth           = axe_axi_default_types_pkg::WIDTH_ADDR_40;
  parameter int unsigned       TbAxiDataWidth           = axe_axi_default_types_pkg::WIDTH_DATA_64;
  parameter int unsigned       TbInstructionBufferDepth = 16;

  typedef axe_axi_default_types_pkg::axi_aw_4_40_4_t tb_axi_aw_t;
  typedef axe_axi_default_types_pkg::axi_w_64_8_4_t  tb_axi_w_t;
  typedef axe_axi_default_types_pkg::axi_b_4_4_t     tb_axi_b_t;
  typedef axe_axi_default_types_pkg::axi_ar_4_40_4_t tb_axi_ar_t;
  typedef axe_axi_default_types_pkg::axi_r_4_64_4_t  tb_axi_r_t;

  /////////////////////
  // Clock and Reset //
  /////////////////////
  parameter int unsigned TbResetCycles =        10;
  parameter int unsigned TbNumCycles   = 1_000_000;
  parameter int unsigned TbFreqMhz     =       900;

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

  ///////////////////////
  // Send some Stimuli //
  ///////////////////////
  aic_cd_pkg::aic_cd_command_t tb_command;
  logic                        tb_command_valid;
  logic                        tb_command_ready;

  initial begin : proc_requests
    automatic int unsigned random_offset;
    automatic int unsigned random_length;
    automatic int unsigned random_pointer;

    tb_command       = '0;
    tb_command_valid = 1'b0;

    @(posedge tb_rst_n);
    @(posedge tb_clk);
    for (int unsigned request_id = 0; request_id < TbNumRequests; request_id++) begin
      random_offset  = $urandom();
      random_length  = $urandom();
      random_pointer = $urandom();

      tb_command.view_struct <= '{
        control_offset:    aic_cd_pkg::control_offset_t'(random_offset),
        task_list_length:  aic_cd_pkg::task_list_word_length_t'(random_length),
        task_list_pointer: aic_cd_pkg::task_list_pointer_t'(random_pointer),
        default: '0
      };
      tb_command_valid <= 1'b1;
      do @(posedge tb_clk); while (!tb_command_ready);
    end
    tb_command_valid <= 1'b0;
    repeat (1000) @(posedge tb_clk);
    $display("All sanity commands done: Success!");
    $finish();
  end


  aic_cd_pkg::instruction_t    tb_instruction;
  aic_cd_pkg::control_offset_t tb_instruction_control_offset;
  logic                        tb_instruction_last;
  logic                        tb_instruction_valid;
  logic                        tb_instruction_ready;
  initial begin : proc_response
    tb_instruction_ready <= 1'b1;
  end


  ///////////////////////
  // Design Under Test //
  ///////////////////////
  tb_axi_ar_t tb_axi_ar;
  logic       tb_axi_ar_valid;
  logic       tb_axi_ar_ready;
  tb_axi_r_t  tb_axi_r;
  logic       tb_axi_r_valid;
  logic       tb_axi_r_ready;

  aic_cd_instruction_fetch #(
    .NumDestinationIds     (TbNumDestinationIds),
    .NumPatchModeEntries   (TbNumPatchModeEntries),
    .NumPatchTableEntries  (TbNumPatchTableEntries),
    .NumLocalTokens        (TbNumLocalTokens),
    .NumGlobalTokens       (TbNumGlobalTokens),
    .AxiIdWidth            (TbAxiIdWidth),
    .AxiIdInstructionFetch (TbAxiIdWidth'(0)),
    .AxiAddrWidth          (TbAxiAddrWidth),
    .InstructionBufferDepth(TbInstructionBufferDepth),
    .axi_ar_t              (tb_axi_ar_t),
    .axi_r_t               (tb_axi_r_t)
  ) u_aic_cd_instruction_fetch_dut (
    .i_clk                       (tb_clk),
    .i_rst_n                     (tb_rst_n),
    .i_task_list_offset          (TbAxiAddrWidth'(0)),
    .o_error_empty_task_list     (),
    .i_command                   (tb_command),
    .i_command_valid             (tb_command_valid),
    .o_command_ready             (tb_command_ready),
    .o_axi_m_ar                  (tb_axi_ar),
    .o_axi_m_ar_valid            (tb_axi_ar_valid),
    .i_axi_m_ar_ready            (tb_axi_ar_ready),
    .i_axi_m_r                   (tb_axi_r),
    .i_axi_m_r_valid             (tb_axi_r_valid),
    .o_axi_m_r_ready             (tb_axi_r_ready),
    .o_instruction               (tb_instruction),
    .o_instruction_control_offset(tb_instruction_control_offset),
    .o_instruction_last          (tb_instruction_last),
    .o_instruction_valid         (tb_instruction_valid),
    .i_instruction_ready         (tb_instruction_ready)
  );

  ///////////////////////////////////////////////////////////////////////
  // For now just connect an Error Subordinate to make responding easy //
  ///////////////////////////////////////////////////////////////////////
  localparam aic_cd_pkg::instruction_t DummyInstruction = aic_cd_pkg::command_instruction_t'{
    patch_mode:  aic_cd_pkg::patch_mode_t'(5),
    length:      aic_cd_pkg::command_byte_length_t'(16),
    patch_id_1:  aic_cd_pkg::patch_id_t'(1),
    patch_id_0:  aic_cd_pkg::patch_id_t'(4),
    command_ptr: aic_cd_pkg::command_pointer_t'(24'hABBA_12),
    dst_id:      aic_cd_pkg::D_DWPU,
    opcode:      aic_cd_pkg::OpcodeCommand,
    default:     '0
  };

  axe_axi_err_sub #(
    .AxiIdWidth  (TbAxiIdWidth),
    .Resp        (axi_pkg::RespOkay),
    .DataWidth   (TbAxiDataWidth),
    .ReadData    (TbAxiDataWidth'(DummyInstruction.view_vector)),
    .MaxTxn      (1000),
    .SupportAtops(1'b0),
    .axi_aw_t    (tb_axi_aw_t),
    .axi_w_t     (tb_axi_w_t),
    .axi_b_t     (tb_axi_b_t),
    .axi_ar_t    (tb_axi_ar_t),
    .axi_r_t     (tb_axi_r_t)
  ) u_axi_err_sub (
    .i_clk           (tb_clk),
    .i_rst_n         (tb_rst_n),
    .i_axi_s_aw      ('0),
    .i_axi_s_aw_valid(1'b0),
    .o_axi_s_aw_ready(/* not used */),
    .i_axi_s_w       ('0),
    .i_axi_s_w_valid (1'b0),
    .o_axi_s_w_ready (/* not used */),
    .o_axi_s_b       (/* not used */),
    .o_axi_s_b_valid (/* not used */),
    .i_axi_s_b_ready (1'b0),
    .i_axi_s_ar      (tb_axi_ar),
    .i_axi_s_ar_valid(tb_axi_ar_valid),
    .o_axi_s_ar_ready(tb_axi_ar_ready),
    .o_axi_s_r       (tb_axi_r),
    .o_axi_s_r_valid (tb_axi_r_valid),
    .i_axi_s_r_ready (tb_axi_r_ready)
  );
endmodule
