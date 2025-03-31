// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: MVM datapath. This DP consists of par2bser, imc + acc and out_buf. The DP expects a synchronized IFD0 and CMD stream at its inputs.
// Throughout the DP, each DP block ensures that the data stream and cmd stream remain in sync. This is exe_done using delay buffers and fifos inside these blocks.
// The fifos help to average out forwards stalls caused by cmd or ifd0 not valid, and/or backpressure stalls caused by DPU not ready.
// Further, the DP tracks incoming and outgoing transactions to determine its idle state. Only when idle, an incoming bypass cmd is processed.
//
// Owner: roel uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_DP_SV
`define MVM_DP_SV

module mvm_dp
  import aic_common_pkg::*;
  import imc_bank_pkg::*;
  import mvm_pkg::*;
#(
  parameter type aic_csr_hw2reg_t = imc_bist_pkg::aic_csr_hw2reg_t,
  parameter type aic_csr_reg2hw_t = imc_bist_pkg::aic_csr_reg2hw_t,
  parameter type aic_csr_reg2hw_imc_status_t = imc_bist_pkg::hw2reg_imc_bist_status_reg_t,
  parameter type nop_inj_rate_t = logic [6:0]
) (
  input wire i_clk,
  input wire i_rst_n,
  input logic jtag_tcki,
  input logic jtag_i_rst_n,

  // EXE CMD inputs IFD0
  input  mvm_exe_dp_cmd_t i_ifd0_exe_cmd_tdata,
  input  logic            i_ifd0_exe_cmd_tvalid,
  output logic            o_ifd0_exe_cmd_tready,

  // EXE CMD inputs IFD2
  input  mvm_exe_dp_cmd_t i_ifd2_exe_cmd_tdata,
  input  logic            i_ifd2_exe_cmd_tvalid,
  output logic            o_ifd2_exe_cmd_tready,

  output logic            o_exe_dp_done,
  // PRG CMD inputs
  input  mvm_prg_dp_cmd_t prg_cmd_tdata_i,
  input  logic          prg_cmd_tvalid_i,
  output logic          prg_cmd_tready_o,
  input  logic          prg_cmd_tlast_i,
  output logic          prg_done,

  // IFD0 AXI stream
  input  logic                          ifd0_tvalid_i,
  output logic                          ifd0_tready_o,
  input  logic [PW_LEN-1:0][DATA_W-1:0] ifd0_tdata_i,
  input  logic                          ifd0_tlast_i,

  // IFD2 AXI stream
  input  logic                          ifd2_tvalid_i,
  output logic                          ifd2_tready_o,
  input  logic [PW_LEN-1:0][DATA_W-1:0] ifd2_tdata_i,
  input  logic                          ifd2_tlast_i,

  // IFDW AXI stream
  input  logic                                 ifdw_tvalid_i,
  output logic                                 ifdw_tready_o,
  input  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] ifdw_tdata_i,
  input  logic                                 ifdw_tlast_i,

  // DPU AXI stream
  output logic                                  dpu_tvalid_o,
  input  logic                                  dpu_tready_i,
  output logic [AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0] dpu_tdata_o,
  //output logic [AIC_PWORD_I26_AXIS_TSTRB_WIDTH-1:0] dpu_tstrb_o,
  output logic                                  dpu_tlast_o,

  // Util limit signals
  input logic            [MVM_UTIL_INTERFACE_WIDTH-1:0] util_limit_value_i,
  input logic                                           util_limit_enable_i,
  input logic  [MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH-1:0] util_average_nominator_i,
  input  logic                                    [2:0] i_util_col_upscaling_factor,
  input  logic                                    [2:0] i_util_row_upscaling_factor,
  output logic           [MVM_UTIL_INTERFACE_WIDTH-1:0] util_average_o,

  // NOP Injection
  input  nop_inj_rate_t                            i_mvm_nop_inj_rate_value,
  input  logic                                     i_mvm_nop_inj_rate_enable,

  // CSR signals
  input logic csr_signed_weights_i,
  input logic csr_signed_inputs_i,
  input logic csr_power_smooth_dummy_ops_i,
  input logic csr_disable_imc_acc_clock_gating_i,
  input logic [MVM_IMC_TM_CSR_DW-1:0] csr_imc_tm_i,
  input mvm_ramp_up_ctrl_pkg::ramp_up_ctrl_t i_ramp_budget_ctrl,

  // Status signals
  output mvmexe_csr_reg_pkg::mvmexe_csr_hw2reg_dp_status_reg_t exe_dp_status_o,
  output mvmprg_csr_reg_pkg::mvmprg_csr_hw2reg_dp_status_reg_t prg_dp_status_o,

  // ERR/IRQ signals
  output logic err_ifd0_dpcmd_unaligned_tlast_o,
  output logic err_ifd2_dpcmd_unaligned_tlast_o,
  output logic err_ifdw_dpcmd_unaligned_tlast_o,
  output logic err_bypass_when_dp_not_idle_o,
  output logic err_concurrent_exe_prg_on_ws_o,
  output logic o_err_not_enough_budget,
  output logic o_warning_util_limit_trigger_nop,
  // DFT signals
  input logic test_mode_i,
  input logic scan_en,
  // IMC BIST
  input  aic_csr_reg2hw_t imc_bist_tdr2hw_i,
  output aic_csr_hw2reg_t imc_bist_hw2tdr_o,
  input  aic_csr_reg2hw_t imc_bist_csr2hw_i,
  output aic_csr_hw2reg_t imc_bist_hw2csr_o
);
  // verilog_lint: waive-start line-length
  localparam int unsigned SignExtendLen = MVM_OUT_DATA_W - DATA_W;

  // Combine DPU, CMD and IFD0 ready and valid sig into ctrl_ready/valid for DP
  logic ifd0_exe_dp_tready, ifd0_exe_dp_tvalid;
  logic ifd2_exe_dp_tready;
  logic                      exe_dp_idle;
  // logic out_dp_cmd_tvalid, out_dp_cmd_tready;
  // out_dp_cmd                      out_dp_cmd_tdata;


  // Structure input data stream in PW arrays and apply strb.
  localparam int unsigned MIRRORING_GRANULARITY = 16; // Highest weight precision is 16 bit
  logic [PW_LEN-1:0][        DATA_W-1:0] weight_pw ;
  logic [PW_LEN-1:0][MVM_OUT_DATA_W-1:0] output_pw ;
  // always_comb begin
  //   // Assign ifdw_tdata_i to weight_pw in such a way that no physical signal crossings are introduced
  //   // weight_pw physical ordening is 31..0 - 32..64 due to mirroring of imc_banks in layout
  //   foreach (weight_pw[i]) begin
  //     // Cross signals to match mirroring, this is ok since the outputs are getting the same treatment
  //     if (i < IMC_NB_COLS_PER_BANK)
  //       weight_pw[(IMC_NB_COLS_PER_BANK-1)-i] = ifdw_tdata_i[i*DATA_W+:DATA_W];
  //     else weight_pw[i] = ifdw_tdata_i[i*DATA_W+:DATA_W];
  //   end
  // end

  // Assign ifdw_tdata_i to weight_pw in such a way that minimal physical signal crossings are introduced
  // weight_pw physical ordening is 30,31,28,29..0,1 - 32..64 due to mirroring of imc_banks in layout
  assign weight_pw[PW_LEN  -1:PW_LEN/2] = ifdw_tdata_i[(PW_LEN*DATA_W-1):(PW_LEN/2*DATA_W)];
  assign weight_pw[PW_LEN/2-1:       0] = {<<MIRRORING_GRANULARITY{ifdw_tdata_i[(PW_LEN/2*DATA_W-1):0]}};

  /////////////
  // IFD0 & EXE DP CMD r/v combining
  logic ifd0_exe_dp_tvalid_int;
  logic ifd0_exe_cmd_tready_int;
  logic ifd0_tready_int;
  //assign ifd0_exe_dp_tvalid_int = i_ifd0_exe_cmd_tvalid & ifd0_tvalid_i;
  assign ifd0_tready_int = i_ifd0_exe_cmd_tvalid & i_ifd0_exe_cmd_tdata.par2bser_dp_cmd_sig.inp_buf_we & ifd0_exe_dp_tready;
  // exe_cmd_tready should block when ifd0 not valid and exe_cmd specifies inp buf write_enable
  always_comb begin
    if (i_ifd0_exe_cmd_tdata.par2bser_dp_cmd_sig.inp_buf_we) begin
      ifd0_exe_cmd_tready_int = ifd0_tvalid_i & ifd0_exe_dp_tready;
      ifd0_exe_dp_tvalid_int  = i_ifd0_exe_cmd_tvalid & ifd0_tvalid_i;
    end else begin
      ifd0_exe_cmd_tready_int = ifd0_exe_dp_tready;
      ifd0_exe_dp_tvalid_int  = i_ifd0_exe_cmd_tvalid;
    end
  end

  /////////////
  // IFD0 & EXE DP CMD r/v combining
  logic ifd2_exe_dp_tvalid;
  logic ifd2_exe_cmd_tready_int;
  logic ifd2_tready_int;
  assign ifd2_tready_int = i_ifd2_exe_cmd_tvalid & i_ifd2_exe_cmd_tdata.par2bser_dp_cmd_sig.inp_buf_we & ifd2_exe_dp_tready;
  // exe_cmd_tready should block when ifd0 not valid and exe_cmd specifies inp buf write_enable
  always_comb begin
    if (i_ifd2_exe_cmd_tdata.par2bser_dp_cmd_sig.inp_buf_we) begin
      if (i_ifd2_exe_cmd_tdata.dp_ctrl.input_precision == inp_int16) begin
        // In int16, deinterleaver moves data from ifd0-stream to ifd2-par2bser
        ifd2_exe_cmd_tready_int = ifd0_tvalid_i & ifd2_exe_dp_tready;
      end else begin
        // In int8, we are consuming data from ifd2 stream
        ifd2_exe_cmd_tready_int = ifd2_tvalid_i & ifd2_exe_dp_tready;
      end
      ifd2_exe_dp_tvalid      = i_ifd2_exe_cmd_tvalid & ifd2_tvalid_i;
    end else begin
      ifd2_exe_cmd_tready_int = ifd2_exe_dp_tready;
      ifd2_exe_dp_tvalid      = i_ifd2_exe_cmd_tvalid;
    end
  end

  /////////////
  // IFDW & PRG DP CMD r/v combining
  logic prg_dp_tvalid, prg_dp_tready;
  assign prg_dp_tvalid = prg_cmd_tvalid_i && ifdw_tvalid_i;
  assign ifdw_tready_o = prg_cmd_tvalid_i && prg_dp_tready;
  assign prg_cmd_tready_o = ifdw_tvalid_i && prg_dp_tready;

  /////////////
  // DPU r/v
  logic dpu_tvalid_int, dpu_tlast_int;
  logic dpu_tvalid_32, dpu_tvalid_64;
  compute_out_ctrl_t dpu_ctrl_32, dpu_ctrl_64;
  logic dpu_fifos_valid;
  logic dpu_fifos_last;
  logic dpu_fifos_interleave_required;
  logic interleaver_ready;
  assign dpu_fifos_valid = dpu_tvalid_32 & dpu_tvalid_64;
  assign dpu_fifos_last = dpu_fifos_valid & (dpu_ctrl_32.last & dpu_ctrl_64.last);
  assign dpu_fifos_interleave_required = dpu_fifos_valid & (dpu_ctrl_32.interleave_required & dpu_ctrl_64.interleave_required);

  /////////////
  // Done gen
  assign o_exe_dp_done = dpu_tlast_o && dpu_tready_i && dpu_tvalid_o;
  assign prg_done = ifdw_tlast_i && ifdw_tready_o && ifdw_tvalid_i;

  /////////////
  // Bypass muxing
  assign exe_bypass_on = exe_dp_idle && i_ifd0_exe_cmd_tdata.bypass_enable && i_ifd0_exe_cmd_tvalid;
  assign ifd0_exe_dp_tvalid = !i_ifd0_exe_cmd_tdata.bypass_enable & ifd0_exe_dp_tvalid_int;
  assign o_ifd0_exe_cmd_tready  = i_ifd0_exe_cmd_tdata.bypass_enable ? (exe_bypass_on & dpu_tlast_o & dpu_tready_i & dpu_tvalid_o) : ifd0_exe_cmd_tready_int;
  assign o_ifd2_exe_cmd_tready  = i_ifd0_exe_cmd_tdata.bypass_enable ? 1'b0 : ifd2_exe_cmd_tready_int;
  assign ifd0_tready_o = i_ifd0_exe_cmd_tdata.bypass_enable ? (exe_bypass_on & dpu_tready_i) : ifd0_tready_int;
  assign ifd2_tready_o = !i_ifd2_exe_cmd_tdata.bypass_enable & ifd2_tready_int;
  assign dpu_tvalid_o = exe_bypass_on ? ifd0_tvalid_i : dpu_tvalid_int;
  assign dpu_tlast_o = exe_bypass_on ? ifd0_tlast_i : dpu_tlast_int;
  // Connect DPU strb (and sign extend) depending on bypass mode
  //logic [PW_LEN-1:0] mvm_dp_strb;
  always_comb begin
    if (exe_bypass_on) begin
      // Connect ifd0 to dpu with sign extension
      foreach (ifd0_tdata_i[i]) begin
        dpu_tdata_o[i*MVM_OUT_DATA_W+:MVM_OUT_DATA_W] = {
          {SignExtendLen{ifd0_tdata_i[i][DATA_W-1]}}, ifd0_tdata_i[i]
        };
      end
    end else begin
      // Assign output_pw to dpu_tdata_o in such a way that no physical signal crossings are introduced
      // output_pw physical ordening is 31..0 - 32..64 due to mirroring of imc_banks in layout
      // foreach (output_pw[i]) begin
      //   // Cross signals to match mirroring, this is ok since the input weights are getting the same treatment
      //   if (i < IMC_NB_COLS_PER_BANK)
      //     dpu_tdata_o[i*MVM_OUT_DATA_W+:MVM_OUT_DATA_W] = output_pw[(IMC_NB_COLS_PER_BANK-1)-i];
      //   else dpu_tdata_o[i*MVM_OUT_DATA_W+:MVM_OUT_DATA_W] = output_pw[i];
      // end

      // Assign output_pw to dpu_tdata_o in such a way that minimal physical signal crossings are introduced
      // output_pw physical ordening is 30,31,29,28..0,1 - 32..64 due to mirroring of imc_banks in layout
      dpu_tdata_o[  (PW_LEN*MVM_OUT_DATA_W-1):(PW_LEN/2*MVM_OUT_DATA_W)] = output_pw[PW_LEN-1:PW_LEN/2];
      dpu_tdata_o[(PW_LEN/2*MVM_OUT_DATA_W-1):                        0] = {<<(MIRRORING_GRANULARITY/DATA_W*MVM_OUT_DATA_W){output_pw[PW_LEN/2-1:0]}};
    end
  end

  /////////////
  // MVM-DP idle tracker
  // Keep track of ongoing DP transfers (required for safe bypass context switching)
  logic [3:0] nb_ongoing_trans;
  logic input_trans_busy;
  logic exe_dp_active;
  // DP is idle when no trans are going on
  assign exe_dp_idle   = nb_ongoing_trans == 0;
  assign exe_dp_active = !exe_dp_idle;
  always_ff @(posedge i_clk, negedge i_rst_n) begin : dp_idle_tracker
    if (!i_rst_n) begin
      nb_ongoing_trans <= 0;
      input_trans_busy <= 1'b0;
    end else if (!exe_bypass_on) begin
      // When tlast is seen on the input cmd, the current running input transaction is finished
      if (input_trans_busy & ((ifd0_exe_dp_tvalid & ifd0_exe_dp_tready & i_ifd0_exe_cmd_tdata.out_dp_cmd_sig.tlast)
                           |  (ifd2_exe_dp_tvalid & ifd2_exe_dp_tready & i_ifd2_exe_cmd_tdata.out_dp_cmd_sig.tlast))) begin
        input_trans_busy <= 1'b0;
      end
      // When tvalid and tready when no input trans is busy, a new input trans is started
      else
      if (!input_trans_busy & ifd0_exe_dp_tvalid & ifd0_exe_dp_tready) begin
        // Check that at the output there is not a trans finished. If not, add 1 to the ongoing DP trans
        input_trans_busy <= 1'b1;
        if (!(dpu_tlast_int & dpu_tready_i & dpu_tvalid_int))
          nb_ongoing_trans <= nb_ongoing_trans + 1;
      end
      // Monitor the output for finishing trans
      else
      if (dpu_tlast_int & dpu_tready_i & dpu_tvalid_int) nb_ongoing_trans <= nb_ongoing_trans - 1;
    end
  end

  logic imc_acc_pipe_ready;
  // imc_acc pipeline is ready to receive data when dpu_axis is ready or when there is no valid data pending.
  //assign imc_acc_pipe_ready = dpu_tready_i || (!dpu_tvalid_int);
  assign imc_acc_pipe_ready = interleaver_ready || (!dpu_fifos_valid);

  ///////////////
  // INT16: Deinterleaver
  logic ifd0di_exe_dp_tvalid_int;
  logic ifd0di_exe_dp_tready_int;
  logic [PW_LEN-1:0][DATA_W-1:0] ifd0di_tdata_int;
  mvm_exe_dp_cmd_t ifd0_exe_cmd_tdata_int;
  logic ifd0di_exe_dp_tvalid;
  logic ifd0di_exe_dp_tready;
  logic [PW_LEN-1:0][DATA_W-1:0] ifd0di_tdata_i;
  mvm_exe_dp_cmd_t ifd2_exe_cmd_tdata_int;
  logic ifd2di_exe_dp_tvalid_int;
  logic ifd2di_exe_dp_tready_int;
  logic [PW_LEN-1:0][DATA_W-1:0] ifd2di_tdata_int;
  logic ifd2di_exe_dp_tvalid;
  logic ifd2di_exe_dp_tready;
  logic [PW_LEN-1:0][DATA_W-1:0] ifd2di_tdata_i;
  logic enable_deinterleaver;

  assign enable_deinterleaver = i_ifd0_exe_cmd_tdata.dp_ctrl.input_precision == inp_int16;

  mvm_int16_deinterleaver #(
    .DATA_W(DATA_W),
    .PW_LEN(PW_LEN)
  ) u_mvm_int16_deinterleave (
    .i_clk,
    .i_rst_n,

    .i_enable(enable_deinterleaver),

    // Input IFD0 - parallel interleaved highs and lows
    .i_ifd0_tvalid(ifd0_exe_dp_tvalid),
    .o_ifd0_tready(ifd0_exe_dp_tready),
    .i_ifd0_pw_data(ifd0_tdata_i),

    // Input IFD2 - for passthrough if disabled
    .i_ifd2_tvalid(ifd2_exe_dp_tvalid),
    .o_ifd2_tready(ifd2_exe_dp_tready),
    .i_ifd2_pw_data(ifd2_tdata_i),

    // Output IFD0 - low bytes
    .o_ifd0_tvalid(ifd0di_exe_dp_tvalid_int),
    .i_ifd0_tready(ifd0di_exe_dp_tready_int),
    .o_ifd0_pw_data(ifd0di_tdata_int),

    // Output IFD2 - high bytes
    .o_ifd2_tvalid(ifd2di_exe_dp_tvalid_int),
    .i_ifd2_tready(ifd2di_exe_dp_tready_int),
    .o_ifd2_pw_data(ifd2di_tdata_int)
  );

  localparam int unsigned LP_DATA_WD = PW_LEN*DATA_W + $bits(mvm_exe_dp_cmd_t);

  cc_stream_spill_reg #(
    .data_t(logic[LP_DATA_WD-1:0]),
    .Bypass(1'b0)
  ) u_mvm_ifd0_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({ifd0di_tdata_int, i_ifd0_exe_cmd_tdata}),
    .i_valid(ifd0di_exe_dp_tvalid_int),
    .o_ready(ifd0di_exe_dp_tready_int),
    .o_data ({ifd0di_tdata_i, ifd0_exe_cmd_tdata_int}),
    .o_valid(ifd0di_exe_dp_tvalid),
    .i_ready(ifd0di_exe_dp_tready)
  );

  cc_stream_spill_reg #(
    .data_t(logic[LP_DATA_WD-1:0]),
    .Bypass(1'b0)
  ) u_mvm_ifd2_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({ifd2di_tdata_int, i_ifd2_exe_cmd_tdata}),
    .i_valid(ifd2di_exe_dp_tvalid_int),
    .o_ready(ifd2di_exe_dp_tready_int),
    .o_data ({ifd2di_tdata_i, ifd2_exe_cmd_tdata_int}),
    .o_valid(ifd2di_exe_dp_tvalid),
    .i_ready(ifd2di_exe_dp_tready)
  );

  ///////////////
  // Fast NOP Injector
  logic fast_nop_inj;

  mvm_nop_inj # (
    .nop_inj_rate_t(nop_inj_rate_t)
  ) u_mvm_nop_inj (
    .i_clk,
    .i_rst_n,
    .i_nop_inj_rate  (i_mvm_nop_inj_rate_value),
    .i_nop_inj_enable(i_mvm_nop_inj_rate_enable),
    .o_inj_nop       (fast_nop_inj)
  );

  ///////////////
  // Utilization control
  logic                     [MVM_UTIL_WIDTH-1:0] ifd0_current_util;
  logic                                          ifd0_current_util_valid;
  logic                     [MVM_UTIL_WIDTH-1:0] ifd2_current_util;
  logic                                          ifd2_current_util_valid;
  logic                                          util_limit_trigger_nop;

  mvm_par2bser_util_ctrl u_mvm_par2bser_util_ctrl
  (
    .i_clk,
    .i_rst_n,

    // Current Utilization
    .i_current_util      (ifd2_current_util + ifd0_current_util),
    .i_current_util_valid(ifd2_current_util_valid | ifd0_current_util_valid),

    // Util limiting
    .i_util_limit_value  (util_limit_value_i),
    .i_util_limit_enable (util_limit_enable_i),

    // Exponential average
    .i_util_average_nominator(util_average_nominator_i),
    .o_util_average          (util_average_o),

    .o_util_limit_trigger_nop(util_limit_trigger_nop)
  );

  always_comb o_warning_util_limit_trigger_nop = util_limit_trigger_nop;
  ///////////////
  // Ramp Up controller Unit
  mvm_ramp_up_ctrl_pkg::mvm_rows_t   ifd0_nb_active_rows;
  mvm_ramp_up_ctrl_pkg::mvm_cols_t   ifd0_nb_active_cols;
  mvm_ramp_up_ctrl_pkg::mvm_rows_t   ifd2_nb_active_rows;
  mvm_ramp_up_ctrl_pkg::mvm_cols_t   ifd2_nb_active_cols;
  mvm_ramp_up_ctrl_pkg::mvm_rows_t   ifd0_nb_active_rows_filtered;
  mvm_ramp_up_ctrl_pkg::mvm_cols_t   ifd0_nb_active_cols_filtered;
  mvm_ramp_up_ctrl_pkg::mvm_rows_t   ifd2_nb_active_rows_filtered;
  mvm_ramp_up_ctrl_pkg::mvm_cols_t   ifd2_nb_active_cols_filtered;
  logic                              nop_trigger;

  mvm_ramp_up_ctrl u_mvm_ramp_up_ctrl (
    .i_clk,
    .i_rst_n,
    .i_nb_active_cols       (ifd0_nb_active_cols_filtered + ifd2_nb_active_cols_filtered),
    .i_nb_active_rows       (ifd0_nb_active_rows_filtered + ifd2_nb_active_rows_filtered),
    .i_ramp_budget_ctrl,
    .i_ext_trigger_nop      (util_limit_trigger_nop || fast_nop_inj),
    .o_trigger_nop          (nop_trigger),
    .o_err_not_enough_budget
  );
  ///////////////
  // PAR2BSER IFD0
  imc_acc_dp_cmd_t ifd0_imc_acc_dp_cmd_tdata;
  imc_acc_dp_cmd_t ifd0p2b_imc_acc_dp_cmd_tdata;
  logic ifd0_imc_acc_dp_cmd_tvalid, ifd0_imc_acc_stall;
  logic [IMC_NB_ROWS-1:0] ifd0_c_in_ser;
  logic [IMC_NB_ROWS-1:0] ifd0p2b_c_in_ser;
  logic ifd0_serial_conversion_valid;
  logic ifd0p2b_serial_conversion_valid;
  logic ifd0p2b_imc_acc_dp_cmd_tvalid;
  logic ifd0p2b_imc_acc_pipe_ready;
  logic align_stream_0;
  mvm_par2bser #(
    .DATA_W(DATA_W),
    .PW_LEN(PW_LEN),
    .UIN(IMC_NB_ROWS),
    .GATE_GRANULARITY(IMC_BLOCK_GATING_GRANULARITY)
  ) inst_mvm_par2bser (
    .i_clk                       (i_clk),
    .i_rst_n                      (i_rst_n),
    // Incoming PWs
    .inp_buf_pw_i                (ifd0di_tdata_i),
    // Incoming cmds
    .s_cmd_data_i                (ifd0_exe_cmd_tdata_int),
    .s_tvalid_i                  (ifd0di_exe_dp_tvalid),
    .s_tready_o                  (ifd0di_exe_dp_tready),
    // Outgoing cmds
    .m_cmd_data_o                (ifd0p2b_imc_acc_dp_cmd_tdata),
    .m_tvalid_o                  (ifd0p2b_imc_acc_dp_cmd_tvalid),
    .m_tready_i                  (ifd0p2b_imc_acc_pipe_ready && align_stream_0),
    // Serial output vector
    .imc_acc_stall_o             (ifd0_imc_acc_stall),
    .par2bser_uin_o              (ifd0p2b_c_in_ser),
    // Status signals
    .serial_conversion_running_o (ifd0p2b_serial_conversion_valid),
    // Util limit
    .i_util_row_upscaling_factor (i_util_row_upscaling_factor),
    .i_util_col_upscaling_factor (i_util_col_upscaling_factor),
    .csr_power_smooth_dummy_ops_i(csr_power_smooth_dummy_ops_i),
    .i_util_limit_trigger_nop    (nop_trigger),
    // Current Utilization
    .o_current_util              (ifd0_current_util),
    .o_current_util_valid        (ifd0_current_util_valid),
    // Ramp up control
    .o_nb_active_rows            (ifd0_nb_active_rows),
    .o_nb_active_cols            (ifd0_nb_active_cols)
  );

  ///////////////
  // PAR2BSER IFD2
  imc_acc_dp_cmd_t ifd2_imc_acc_dp_cmd_tdata;
  imc_acc_dp_cmd_t ifd2p2b_imc_acc_dp_cmd_tdata;
  logic ifd2_imc_acc_dp_cmd_tvalid, ifd2_imc_acc_stall;
  logic [IMC_NB_ROWS-1:0] ifd2_c_in_ser;
  logic [IMC_NB_ROWS-1:0] ifd2p2b_c_in_ser;
  logic ifd2_serial_conversion_valid;
  logic ifd2p2b_serial_conversion_valid;
  logic ifd2p2b_imc_acc_dp_cmd_tvalid;
  logic ifd2p2b_imc_acc_pipe_ready;
  logic align_stream_2;
  mvm_par2bser #(
    .DATA_W(DATA_W),
    .PW_LEN(PW_LEN),
    .UIN(IMC_NB_ROWS),
    .GATE_GRANULARITY(IMC_BLOCK_GATING_GRANULARITY)
  ) inst2_mvm_par2bser (
    .i_clk                       (i_clk),
    .i_rst_n                     (i_rst_n),
    // Incoming PWs
    .inp_buf_pw_i                (ifd2di_tdata_i),
    // Incoming cmds
    .s_cmd_data_i                (ifd2_exe_cmd_tdata_int),
    .s_tvalid_i                  (ifd2di_exe_dp_tvalid),
    .s_tready_o                  (ifd2di_exe_dp_tready),
    // Outgoing cmds
    .m_cmd_data_o                (ifd2p2b_imc_acc_dp_cmd_tdata),
    .m_tvalid_o                  (ifd2p2b_imc_acc_dp_cmd_tvalid),
    .m_tready_i                  (ifd2p2b_imc_acc_pipe_ready && align_stream_2),
    // Serial output vector
    .imc_acc_stall_o             (ifd2_imc_acc_stall),
    .par2bser_uin_o              (ifd2p2b_c_in_ser),
    // Status signals
    .serial_conversion_running_o (ifd2p2b_serial_conversion_valid),
    // Util limit
    .i_util_row_upscaling_factor (i_util_row_upscaling_factor),
    .i_util_col_upscaling_factor (i_util_col_upscaling_factor),
    .csr_power_smooth_dummy_ops_i(csr_power_smooth_dummy_ops_i),
    .i_util_limit_trigger_nop    (nop_trigger),
    // Current Utilization
    .o_current_util              (ifd2_current_util),
    .o_current_util_valid        (ifd2_current_util_valid),
    // Ramp up control
    .o_nb_active_rows            (ifd2_nb_active_rows),
    .o_nb_active_cols            (ifd2_nb_active_cols)
  );


  always_comb align_stream_2 = ifd2p2b_imc_acc_dp_cmd_tvalid && ifd2p2b_imc_acc_dp_cmd_tdata.dibw_en ?
                               ifd0p2b_imc_acc_dp_cmd_tvalid && ifd0p2b_imc_acc_dp_cmd_tdata.dibw_en :
                               1'b1;


  always_comb align_stream_0 = ifd0p2b_imc_acc_dp_cmd_tvalid && ifd0p2b_imc_acc_dp_cmd_tdata.dibw_en ?
                               ifd2p2b_imc_acc_dp_cmd_tvalid && ifd2p2b_imc_acc_dp_cmd_tdata.dibw_en :
                               1'b1;

  ///////////////
  // Ramp up filtering column and row usage

  always_comb begin: filtering_non_valid_states_comb_proc
    if(ifd0p2b_imc_acc_pipe_ready) begin
      ifd0_nb_active_rows_filtered = ifd0_nb_active_rows;
      ifd0_nb_active_cols_filtered = ifd0_nb_active_cols;
    end else begin
      ifd0_nb_active_rows_filtered = mvm_ramp_up_ctrl_pkg::mvm_rows_t'(0);
      ifd0_nb_active_cols_filtered = mvm_ramp_up_ctrl_pkg::mvm_cols_t'(0);
    end
  end

  always_comb begin: filtering_non_valid_states_ifd2_comb_proc
    if(ifd2p2b_imc_acc_pipe_ready) begin
      ifd2_nb_active_rows_filtered = ifd2_nb_active_rows;
      ifd2_nb_active_cols_filtered = ifd2_nb_active_cols;
    end else begin
      ifd2_nb_active_rows_filtered = mvm_ramp_up_ctrl_pkg::mvm_rows_t'(0);
      ifd2_nb_active_cols_filtered = mvm_ramp_up_ctrl_pkg::mvm_cols_t'(0);
    end
  end
  ///////////////
  // INT16: Par2bser drainer
  logic imc_parbser0_spill_ready;
  mvm_int16_par2bser_drainer #(
    .DATA_W(DATA_W),
    .PW_LEN(PW_LEN),
    .UIN(IMC_NB_ROWS)
  ) u_mvm_int16_par2bser_drainer (
    .i_clk,
    .i_rst_n,

    .i_enable(enable_deinterleaver),

    // Serial Input IFD0 - low byte stream
    .i_sifd0_cmd_tvalid(ifd0p2b_imc_acc_dp_cmd_tvalid && align_stream_0),
    .o_sifd0_cmd_tready(ifd0p2b_imc_acc_pipe_ready),
    .i_sifd0_cmd_tdata(ifd0p2b_imc_acc_dp_cmd_tdata),
    .i_sifd0_uin_valid(ifd0p2b_serial_conversion_valid && align_stream_0),
    .i_sifd0_uin(ifd0p2b_c_in_ser),

    // Serial Input IFD2 - high byte stream
    .i_sifd2_cmd_tvalid(ifd2p2b_imc_acc_dp_cmd_tvalid && align_stream_2),
    .o_sifd2_cmd_tready(ifd2p2b_imc_acc_pipe_ready),
    .i_sifd2_cmd_tdata(ifd2p2b_imc_acc_dp_cmd_tdata),
    .i_sifd2_uin_valid(ifd2p2b_serial_conversion_valid && align_stream_2),
    .i_sifd2_uin(ifd2p2b_c_in_ser),

    // Serial Output IFD0 - serial interleaved highs and lows
    .o_sifd0_cmd_tvalid(ifd0_imc_acc_dp_cmd_tvalid),
    .i_sifd0_cmd_tready(imc_parbser0_spill_ready),
    .o_sifd0_cmd_tdata(ifd0_imc_acc_dp_cmd_tdata),
    .o_sifd0_uin_valid(ifd0_serial_conversion_valid),
    .o_sifd0_uin(ifd0_c_in_ser),

    // Serial Output IFD2 - for passthrough if disabled
    .o_sifd2_cmd_tvalid(ifd2_imc_acc_dp_cmd_tvalid),
    .i_sifd2_cmd_tready(imc_parbser2_spill_ready),
    .o_sifd2_cmd_tdata(ifd2_imc_acc_dp_cmd_tdata),
    .o_sifd2_uin_valid(ifd2_serial_conversion_valid),
    .o_sifd2_uin(ifd2_c_in_ser)
  );

  localparam int unsigned LP_PAR2BSER_DW = $bits(imc_acc_dp_cmd_t) + IMC_NB_ROWS;
  imc_acc_dp_cmd_t        ifd0_imc_acc_dp_cmd_tdata_d;
  logic [IMC_NB_ROWS-1:0] ifd0_c_in_ser_d;
  logic ifd0_serial_conversion_valid_d;
  logic ifd0_imc_acc_stall_d;

  cc_stream_spill_reg #(
    .data_t(logic[LP_PAR2BSER_DW-1:0]),
    .Bypass(1'b0)
  ) u_mvm_par2bser0_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({ifd0_imc_acc_dp_cmd_tdata, ifd0_c_in_ser}),
    .i_valid(ifd0_serial_conversion_valid),
    .o_ready(imc_parbser0_spill_ready),
    .o_data ({ifd0_imc_acc_dp_cmd_tdata_d,  ifd0_c_in_ser_d}),
    .o_valid(ifd0_serial_conversion_valid_d),
    .i_ready(imc_acc_pipe_ready)
  );

  imc_acc_dp_cmd_t        ifd2_imc_acc_dp_cmd_tdata_d;
  logic [IMC_NB_ROWS-1:0] ifd2_c_in_ser_d;
  logic ifd2_serial_conversion_valid_d;
  logic ifd2_imc_acc_stall_d;

  cc_stream_spill_reg #(
    .data_t(logic[LP_PAR2BSER_DW-1:0]),
    .Bypass(1'b0)
  ) u_mvm_par2bser2_spill_reg (
    .i_clk ,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data ({ifd2_imc_acc_dp_cmd_tdata, ifd2_c_in_ser}),
    .i_valid(ifd2_serial_conversion_valid),
    .o_ready(imc_parbser2_spill_ready),
    .o_data ({ifd2_imc_acc_dp_cmd_tdata_d,  ifd2_c_in_ser_d}),
    .o_valid(ifd2_serial_conversion_valid_d),
    .i_ready(imc_acc_pipe_ready)
  );

  always_comb ifd0_imc_acc_stall_d = !imc_acc_pipe_ready;
  always_comb ifd2_imc_acc_stall_d = !imc_acc_pipe_ready;

  logic compute_output_32_valid;
  compute_out_ctrl_t compute_output_32_ctrl;
  logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] compute_output_32;
  logic compute_output_64_valid;
  compute_out_ctrl_t compute_output_64_ctrl;
  logic [IMC_NB_COLS_PER_BANK-1:0][MVM_OUT_DATA_W-1:0] compute_output_64;

  //////////
  // IMC + ACC
  logic [MVM_TOUT-1:0][MVM_OUT_DATA_W-1:0] c_out_acc;
  //logic [MVM_TOUT-1 : 0] acc_strb_buf;
  mvm_imc_acc #(
    .aic_csr_hw2reg_t(aic_csr_hw2reg_t),
    .aic_csr_reg2hw_t(aic_csr_reg2hw_t),
    .aic_csr_reg2hw_imc_status_t(aic_csr_reg2hw_imc_status_t)
  ) inst_mvm_imc_acc (
    .i_clk                             (i_clk),
    .i_rst_n                           (i_rst_n),
    .jtag_tcki                         (jtag_tcki),
    .jtag_i_rst_n                      (jtag_i_rst_n),
    // Incoming IMC ACC OUT ctrl stream
    .ifd0_imc_acc_dp_cmd_tdata         (ifd0_imc_acc_dp_cmd_tdata_d),
    .ifd2_imc_acc_dp_cmd_tdata         (ifd2_imc_acc_dp_cmd_tdata_d),
    // Serial input bits
    .ifd0_imc_acc_stall_i              (ifd0_imc_acc_stall_d),
    .ifd0_serial_conversion_valid_i    (ifd0_serial_conversion_valid_d),
    .ifd0_c_in_ser                     (ifd0_c_in_ser_d),
    .ifd2_imc_acc_stall_i              (ifd2_imc_acc_stall_d),
    .ifd2_serial_conversion_valid_i    (ifd2_serial_conversion_valid_d),
    .ifd2_c_in_ser                     (ifd2_c_in_ser_d),
    // Incoming programming ctrl stream
    .prg_cmd_tvalid                    (prg_dp_tvalid),
    .prg_cmd_tdata                     (prg_cmd_tdata_i),
    .prg_cmd_tready                    (prg_dp_tready),
    // Weight input PWs
    .weight_pw                         (weight_pw),
    // output results
    .compute_output_32_valid           (compute_output_32_valid),
    .compute_output_32_ctrl            (compute_output_32_ctrl),
    .compute_output_32                 (compute_output_32),
    .compute_output_64_valid           (compute_output_64_valid),
    .compute_output_64_ctrl            (compute_output_64_ctrl),
    .compute_output_64                 (compute_output_64),

    // CSR signals
    .csr_signed_weights_i              (csr_signed_weights_i),
    .csr_signed_inputs_i               (csr_signed_inputs_i),
    .csr_power_smooth_dummy_ops_i      (csr_power_smooth_dummy_ops_i),
    .csr_disable_imc_acc_clock_gating_i(csr_disable_imc_acc_clock_gating_i),

    // Error signal
    .err_concurrent_exe_prg_on_ws_o    (err_concurrent_exe_prg_on_ws_o),
    // DFT signals
    .test_mode_i                       (test_mode_i),
    .scan_en                           (scan_en),
    // IMC BIST
    .imc_bist_tdr2hw_i                 (imc_bist_tdr2hw_i),
    .imc_bist_hw2tdr_o                 (imc_bist_hw2tdr_o),
    .imc_bist_csr2hw_i                 (imc_bist_csr2hw_i),
    .imc_bist_hw2csr_o                 (imc_bist_hw2csr_o)
  );

  logic fifo_32_empty, fifo_64_empty;
  assign dpu_tvalid_32 = ~fifo_32_empty;
  assign dpu_tvalid_64 = ~fifo_64_empty;
  logic [PW_LEN-1:0][MVM_OUT_DATA_W-1:0] fifos_output_pw, int_output_pw;

  // Flatten and restructure 2D arrays to pass through fifo.
  for (genvar g = 0; unsigned'(g) < PW_LEN; g++) begin : g_pw
    if (g < (PW_LEN / 2)) begin : g_lower
      sync_fifo #(
        .FIFO_DEPTH(MVM_NB_IMC_BANKS),
        .data_t(logic [MVM_OUT_DATA_W-1:0]),
        .MEM_MACRO_USE(0),
        .MEM_MACRO_TYPE(0),
        .ALMOST_EMPTY_THR(1),
        .ALMOST_FULL_THR(1)
      ) inst_output_fifo_32 (
        .i_clk         (i_clk),
        .i_rst_n       (i_rst_n),
        .rd_req_i      (interleaver_ready & dpu_fifos_valid),
        .rd_data_o     (fifos_output_pw[g]),
        .empty_o       (), // ASO-UNUSED_OUTPUT: Control signal not used
        .almost_empty_o(), // ASO-UNUSED_OUTPUT: Control signal not used
        .wr_req_i      (compute_output_32_valid),
        .wr_data_i     (compute_output_32[g]),
        .full_o        (), // ASO-UNUSED_OUTPUT: Control signal not used
        .almost_full_o ()  // ASO-UNUSED_OUTPUT: Control signal not used
      );
    end else begin : g_upper
      sync_fifo #(
        .FIFO_DEPTH(MVM_NB_IMC_BANKS),
        .data_t(logic [MVM_OUT_DATA_W-1:0]),
        .MEM_MACRO_USE(0),
        .MEM_MACRO_TYPE(0),
        .ALMOST_EMPTY_THR(1),
        .ALMOST_FULL_THR(1)
      ) inst_output_fifo_64 (
        .i_clk         (i_clk),
        .i_rst_n       (i_rst_n),
        .rd_req_i      (interleaver_ready & dpu_fifos_valid),
        .rd_data_o     (fifos_output_pw[g]),
        .empty_o       (), // ASO-UNUSED_OUTPUT: Control signal not used
        .almost_empty_o(), // ASO-UNUSED_OUTPUT: Control signal not used
        .wr_req_i      (compute_output_64_valid),
        .wr_data_i     (compute_output_64[g-(PW_LEN/2)]),
        .full_o        (), // ASO-UNUSED_OUTPUT: Control signal not used
        .almost_full_o ()  // ASO-UNUSED_OUTPUT: Control signal not used
      );
    end
  end

  sync_fifo #(
    .FIFO_DEPTH(MVM_NB_IMC_BANKS),
    .data_t(compute_out_ctrl_t),
    .MEM_MACRO_USE(0),
    .MEM_MACRO_TYPE(0),
    .ALMOST_EMPTY_THR(1),
    .ALMOST_FULL_THR(1)
  ) inst_output_last_fifo_32 (
    .i_clk         (i_clk),
    .i_rst_n       (i_rst_n),
    .rd_req_i      (interleaver_ready & dpu_fifos_valid),
    .rd_data_o     (dpu_ctrl_32),
    .empty_o       (fifo_32_empty),
    .almost_empty_o(), // ASO-UNUSED_OUTPUT: Control signal not used
    .wr_req_i      (compute_output_32_valid),
    .wr_data_i     (compute_output_32_ctrl),
    .full_o        (), // ASO-UNUSED_OUTPUT: Control signal not used
    .almost_full_o ()  // ASO-UNUSED_OUTPUT: Control signal not used
  );

  sync_fifo #(
    .FIFO_DEPTH(MVM_NB_IMC_BANKS),
    .data_t(compute_out_ctrl_t),
    .MEM_MACRO_USE(0),
    .MEM_MACRO_TYPE(0),
    .ALMOST_EMPTY_THR(1),
    .ALMOST_FULL_THR(1)
  ) inst_output_last_fifo_64 (
    .i_clk         (i_clk),
    .i_rst_n       (i_rst_n),
    .rd_req_i      (interleaver_ready & dpu_fifos_valid),
    .rd_data_o     (dpu_ctrl_64),
    .empty_o       (fifo_64_empty),
    .almost_empty_o(), // ASO-UNUSED_OUTPUT: Control signal not used
    .wr_req_i      (compute_output_64_valid),
    .wr_data_i     (compute_output_64_ctrl),
    .full_o        (), // ASO-UNUSED_OUTPUT: Control signal not used
    .almost_full_o ()  // ASO-UNUSED_OUTPUT: Control signal not used
  );

  ///////////////
  // INT16: Interleaver
  mvm_int16_interleaver #(
    .DATA_W(MVM_OUT_DATA_W),
    .PW_LEN(PW_LEN)
  ) u_mvm_int16_interleaver (
    .i_clk,
    .i_rst_n,

    .i_enable(dpu_fifos_interleave_required),

    .i_pw_data_valid(dpu_fifos_valid),
    .o_pw_data_ready(interleaver_ready),
    .i_pw_data(fifos_output_pw),
    .i_pw_last(dpu_fifos_last),

    .o_pw_data_valid(dpu_tvalid_int),
    .i_pw_data_ready(dpu_tready_i),
    .o_pw_data(int_output_pw),
    .o_pw_last(dpu_tlast_int)
  );

  always_comb begin : imc_tm_mux
    for (int i = 0; i < PW_LEN; i++) begin
      case (csr_imc_tm_i)
        MVM_IMC_TM_OFF: output_pw[i] = int_output_pw[i];
        MVM_IMC_TM0:
        output_pw[i] = {{SignExtendLen{int_output_pw[i][7]}}, int_output_pw[i][7:0]};
        MVM_IMC_TM1:
        output_pw[i] = {{SignExtendLen{int_output_pw[i][15]}}, int_output_pw[i][15:8]};
        MVM_IMC_TM2:
        output_pw[i] = {{SignExtendLen{int_output_pw[i][23]}}, int_output_pw[i][23:16]};
        MVM_IMC_TM3:
        output_pw[i] = {
          {24{int_output_pw[i][MVM_OUT_DATA_W-1]}}, int_output_pw[i][MVM_OUT_DATA_W-1:24]
        };
        default: output_pw[i] = int_output_pw[i];
      endcase
    end
  end


  //////////
  // IRQ
  assign err_ifd0_dpcmd_unaligned_tlast_o = !(i_ifd0_exe_cmd_tdata.dp_ctrl.double_bw_en && i_ifd0_exe_cmd_tdata.dp_ctrl.double_bw_mode==advanced) &&
                                            (ifd0_tvalid_i && ifd0_tlast_i && ifd0_tready_o) != (i_ifd0_exe_cmd_tvalid && i_ifd0_exe_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict && o_ifd0_exe_cmd_tready);
  assign err_ifd2_dpcmd_unaligned_tlast_o = (ifd2_tvalid_i && ifd2_tlast_i && ifd2_tready_o) != (i_ifd2_exe_cmd_tvalid && i_ifd2_exe_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict && o_ifd2_exe_cmd_tready);
  assign err_ifdw_dpcmd_unaligned_tlast_o = (ifdw_tvalid_i && ifdw_tlast_i && ifdw_tready_o) != (prg_cmd_tvalid_i && prg_cmd_tlast_i && prg_cmd_tready_o);
  assign err_bypass_when_dp_not_idle_o = exe_bypass_on && exe_dp_active;

  //////////
  // State observation

  // We can't easily know if the not-present command would be back-pressured or not.
  logic cmd0_stalled;
  assign cmd0_stalled = ~i_ifd0_exe_cmd_tvalid;

  assign exe_dp_status_o = '{
          in0_vld: '{d: ifd0_tvalid_i},
          in0_rdy: '{d: ifd0_tready_o},
          in0_lst: '{d: ifd0_tlast_i},
          in0_stl: '{d: ifd0_tready_o & ~ifd0_tvalid_i},
          out_vld: '{d: dpu_tvalid_o},
          out_rdy: '{d: dpu_tready_i},
          out_lst: '{d: dpu_tlast_o},
          out_stl: '{d: dpu_tvalid_o & ~dpu_tready_i},
          dpcmd0_vld: '{d: i_ifd0_exe_cmd_tvalid},
          dpcmd0_rdy: '{d: o_ifd0_exe_cmd_tready},
          dpcmd0_lst: '{d: i_ifd0_exe_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict},
          dpcmd0_stl: '{d: cmd0_stalled},
          imc_acc_compute_cmd: '{d: ifd0_imc_acc_dp_cmd_tdata.imc_cmd_sig},
          imc_acc_out_cmd: '{d: ifd0_imc_acc_dp_cmd_tdata.out_dp_cmd_sig},
          imc_acc_comp_rdy: '{d: 0},
          imc_acc_comp_vld: '{d: ifd0_imc_acc_dp_cmd_tvalid},
          imc_acc_out_rdy: '{d: 1},
          imc_acc_out_vld: '{d: 0},
          input_trans_busy: '{d: input_trans_busy},
          bypass_en: '{d: i_ifd0_exe_cmd_tdata.bypass_enable}
      };
  assign prg_dp_status_o = '{
          in1_vld: '{d: ifdw_tvalid_i},
          in1_rdy: '{d: ifdw_tready_o},
          in1_lst: '{d: ifdw_tlast_i},
          in1_stl: '{d: ifdw_tready_o & ~ifdw_tvalid_i},
          dpcmd1_vld: '{d: prg_cmd_tvalid_i},
          dpcmd1_rdy: '{d: prg_cmd_tready_o},
          dpcmd1_lst: '{d: prg_cmd_tlast_i},
          dpcmd1_stl: '{d: ifdw_tvalid_i & ~prg_cmd_tvalid_i},
          imc_acc_prg_rdy: '{d: prg_dp_tready},
          imc_acc_prg_vld: '{d: prg_dp_tvalid},
          imc_acc_prg_row: '{d: prg_cmd_tdata_i.imc_prg_row},
          imc_acc_prg_wset: '{d: prg_cmd_tdata_i.imc_prg_weight_set}
      };


  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
  // Check if both par2bser are synced
  property sync_par2bser;
    @(posedge i_clk) disable iff(!i_rst_n) (ifd2_serial_conversion_valid && ifd0_serial_conversion_valid)
      |-> (ifd2_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_shift_pos == ifd0_imc_acc_dp_cmd_tdata.acc_dp_cmd_sig.acc_shift_pos);
  endproperty
  // TLAST of IFD0 and EXE DP CMD stream should match!!
  property synchronized_tlast_IFD0_CMD;
    @(posedge i_clk) disable iff(!i_rst_n) (ifd0_tvalid_i && ifd0_tlast_i && ifd0_tready_o && !(i_ifd0_exe_cmd_tdata.dp_ctrl.double_bw_en && i_ifd0_exe_cmd_tdata.dp_ctrl.double_bw_mode==advanced)) |-> (i_ifd0_exe_cmd_tvalid && i_ifd0_exe_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict && o_ifd0_exe_cmd_tready);
  endproperty
  // TLAST of IFD2 and EXE DP CMD stream should match!!
  property synchronized_tlast_IFD2_CMD;
    @(posedge i_clk) disable iff(!i_rst_n) (ifd2_tvalid_i && ifd2_tlast_i && ifd2_tready_o) |-> (i_ifd2_exe_cmd_tvalid && i_ifd2_exe_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict && o_ifd2_exe_cmd_tready);
  endproperty
  property synchronized_tlast_CMD_IFD0;
    @(posedge i_clk) disable iff(!i_rst_n) (i_ifd0_exe_cmd_tvalid && i_ifd0_exe_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict && o_ifd0_exe_cmd_tready) |-> (ifd0_tvalid_i && ifd0_tlast_i && ifd0_tready_o);
  endproperty
  property synchronized_tlast_CMD_IFD2;
    // Check only in int8 mode. In int16 mode, the ifd2 stream is generated internally.
    @(posedge i_clk) disable iff(!i_rst_n) (i_ifd2_exe_cmd_tvalid && i_ifd2_exe_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict && o_ifd2_exe_cmd_tready && i_ifd2_exe_cmd_tdata.dp_ctrl.input_precision==inp_int8) |-> (ifd2_tvalid_i && ifd2_tlast_i && ifd2_tready_o);
  endproperty
  // TLAST of IFDW and PRG DP CMD stream should match!!
  property synchronized_tlast_IFDW_CMD;
    @(posedge i_clk) disable iff(!i_rst_n) (ifdw_tvalid_i && ifdw_tlast_i && ifdw_tready_o) |-> (prg_cmd_tvalid_i && prg_cmd_tlast_i && prg_cmd_tready_o);
  endproperty
  property synchronized_tlast_CMD_IFDW;
    @(posedge i_clk) disable iff(!i_rst_n) (prg_cmd_tvalid_i && prg_cmd_tlast_i && prg_cmd_tready_o) |-> (ifdw_tvalid_i && ifdw_tlast_i && ifdw_tready_o);
  endproperty

  // When bypass on, nb_ongoing_trans must be 0 (i.e., dp must be idle)
  property dp_idle_when_bypass_on;
    @(posedge i_clk) disable iff (!i_rst_n) (exe_bypass_on) |-> (exe_dp_idle);
  endproperty

  property bypass_on_till_exe_done;
    @(posedge i_clk) disable iff (!i_rst_n) $rose(
        exe_bypass_on
    ) |-> exe_bypass_on throughout o_exe_dp_done [-> 1];
  endproperty

  // Property check can never be satisfied, but we want assert as soon as err_concurrent_exe_prg_on_ws_o is high
  property concurrent_exe_prg_on_ws;
    @(posedge i_clk) disable iff (!i_rst_n) not err_concurrent_exe_prg_on_ws_o;
  endproperty

  property not_enough_budget;
    @(posedge i_clk) disable iff (!i_rst_n) not o_err_not_enough_budget;
  endproperty

  assert property (sync_par2bser)
  else $error("par2bser are not synced");

  assert property (synchronized_tlast_IFD0_CMD)
  else $error("tlast IFD0 and CMD stream not in sync!");

  assert property (synchronized_tlast_IFD2_CMD)
  else $error("tlast IFD2 and CMD stream not in sync!");

  assert property (synchronized_tlast_CMD_IFD0)
  else $error("tlast CMD and IFD0 stream not in sync!");

  assert property (synchronized_tlast_CMD_IFD2)
  else $error("tlast CMD and IFD2 stream not in sync!");

  assert property (synchronized_tlast_IFDW_CMD)
  else $error("tlast IFDW and CMD stream not in sync!");

  assert property (synchronized_tlast_CMD_IFDW)
  else $error("tlast CMD and IFDW stream not in sync!");

  assert property (dp_idle_when_bypass_on)
  else $error("dp not idle while bypass on!");

  assert property (bypass_on_till_exe_done)
  else $error("Bypass_on dropped before exe_done!");

  assert property (concurrent_exe_prg_on_ws)
  else $error("concurrent exe and prg access to the same ws.");

  assert property (not_enough_budget)
  else $error("The budget clip set is not enough to process the vector in the MVM.");
`endif  // ASSERTIONS_ON
  //synopsys translate_on
  // verilog_lint: waive-stop line-length
endmodule



`endif  // MVM_SV
