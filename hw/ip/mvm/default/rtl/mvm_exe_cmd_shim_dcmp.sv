// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef MVM_EXE_CMD_SHIM_DCMP_SV
`define MVM_EXE_CMD_SHIM_DCMP_SV

module mvm_exe_cmd_shim_dcmp
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  #(
    parameter bit P_PROPAGATE_LAST = 1'b0
  )(
  input wire  i_clk,
  input logic i_rst_n,

  // DP general command
  input  mvm_exe_qcmd_t                 i_dp_command_data,
  input  aic_dp_cmd_gen_pkg::metadata_t i_dp_command_metadata,
  input  logic                          i_dp_command_last,
  input  logic                          i_dp_command_valid,
  output logic                          o_dp_command_ready,
  input  logic                          i_inst_last,

  /// Pulse from the datapath indicating that all datapath commands have been executed
  ///
  // DP-CMD stream IFD0
  output mvm_exe_dp_cmd_t o_exe_dp_cmd_tdata,
  output logic            o_exe_dp_cmd_tvalid,
  input  logic            i_exe_dp_cmd_tready
);
  ///////////////////
  // Parameters
  localparam int unsigned InpGatingExpansion = PW_LEN / MVM_INP_GATING_GRAN;
  localparam int unsigned OupGatingExpansion = (MVM_NB_IMC_BANKS - MVM_NR_OUTPUT_PW) / MVM_NR_OUTPUT_PW + 1;
  localparam int unsigned InputRegWidth = $bits(mvm_exe_qcmd_t) + $bits(aic_dp_cmd_gen_pkg::metadata_t) + 1;

  //////////////////
  // Signals

  // dp_cmds_cnt/req must match max nb bits of inp/oup_size
  logic [$bits(i_dp_command_data.inp_size + i_dp_command_data.oup_size)-1:0] dp_cmds_cnt;
  logic [$bits(i_dp_command_data.inp_size + i_dp_command_data.oup_size)-1:0] dp_cmds_req;
  logic [$bits(i_dp_command_data.inp_size + i_dp_command_data.oup_size)-1:0] dp_cmds_out;
  logic dp_cmds_end;

  mvm_exe_qcmd_t                 dp_command_data;
  aic_dp_cmd_gen_pkg::metadata_t dp_command_metadata;
  logic                          dp_command_last;
  logic                          dp_command_valid;
  logic                          dp_command_ready;
  logic                          dp_cmd_last;

  exe_cmd_dp_ctrl_field_t               dp_command_ctrl;
  logic                                 dp_command_int16_beat_count;
  logic                                 dp_command_int16_stall;

  //////////////////
  // RTL
  cc_stream_reg #(
    .data_t(logic[InputRegWidth-1:0])
  ) u_dp_cmd_reg (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_data    ({i_dp_command_last, i_dp_command_data, i_dp_command_metadata}),
    .i_valid   (i_dp_command_valid),
    .o_ready   (o_dp_command_ready),
    .o_data    ({dp_command_last, dp_command_data, dp_command_metadata}),
    .o_valid   (dp_command_valid),
    .i_ready   (dp_command_ready)
  );

  if(P_PROPAGATE_LAST) begin : g_propagate_last_instruction_info
    logic dp_inst_last;
    logic dp_inst_advanced_mode;

    always_comb dp_inst_advanced_mode = dp_command_ctrl.double_bw_en && (dp_command_ctrl.double_bw_mode == advanced);

    always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_sticky_bit_for_instr_last_proc
      if (!i_rst_n)                                                     dp_inst_last <= '0;
      else if (dp_command_valid && i_exe_dp_cmd_tready && dp_inst_last) dp_inst_last <= '0;
      else if (dp_command_valid && i_inst_last && !dp_cmds_end)         dp_inst_last <= '1;
    end

    always_comb dp_cmd_last = dp_command_last || (dp_inst_advanced_mode && (dp_inst_last || i_inst_last));
  end else begin : g_not_used
    always_comb dp_cmd_last = dp_command_last;
  end

  always_comb dp_command_ctrl = exe_cmd_dp_ctrl_field_t'(dp_command_metadata.extra);

  always_ff @(posedge i_clk, negedge i_rst_n) begin : int16_command_counter
    if(!i_rst_n) begin
      dp_command_int16_beat_count <= 1'b0;
    end else begin
      if(dp_command_valid && i_exe_dp_cmd_tready && dp_command_ctrl.input_precision == inp_int16) begin
        dp_command_int16_beat_count <= ~dp_command_int16_beat_count;
      end
    end
  end

  // To keep datapath aligned to command path, int16 gets dp_command beats repeated in pairs
  always_comb dp_command_int16_stall = (dp_command_ctrl.input_precision == inp_int16 && !dp_command_int16_beat_count);
  always_comb dp_command_ready       = (dp_cmds_end && i_exe_dp_cmd_tready && !dp_command_int16_stall);

  always_comb dp_cmds_req = (dp_command_data.inp_size > dp_command_data.oup_size) ? dp_command_data.inp_size : dp_command_data.oup_size;
  always_comb dp_cmds_end = dp_cmds_cnt == dp_cmds_req;
  always_comb dp_cmds_out = dp_cmds_req - dp_cmds_cnt;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_cmd_counters_proc
    if (!i_rst_n) begin
      dp_cmds_cnt   <= 0;
    end else begin
      if (dp_command_valid && i_exe_dp_cmd_tready && !dp_command_int16_stall) begin
        if (dp_cmds_end) begin
          dp_cmds_cnt <= 0;
        end else begin
          dp_cmds_cnt <= dp_cmds_cnt + 1;
        end
      end
    end
  end

  always_comb begin : exe_cmd_2_exe_dp_cmd_ifd0
    // INP CMD signals
    o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.inp_buf_we = dp_command_data.inp_size >= dp_cmds_cnt;
    o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.inp_buf_wr_addr = dp_command_data.inp_offset + dp_cmds_cnt;

    // Predict the tlast flag of the ifd0 stream to check the sync between dp_cmd gen and ifd0
    // This flags matches the o_exe_dp_cmd_tdata.out_dp_cmd_sig.tlast (set below) when inp_size >= oup_size
    // But not when inp_size < oup_size since then there are fewer ifd0 trans than dp_cmd trans
    o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict = ((dp_command_data.inp_size == dp_cmds_cnt) && dp_cmd_last)
                                                              || (dp_command_metadata.format ==  aic_dp_cmd_gen_pkg::Bypass);

    // N-hot encoding of inp_gating based on inp_offset and inp_size with expansion
    // to account for different gating granularity between cmd and dp
    for (int i = 0; i < MVM_NR_INPUT_PW; i++) begin
      if (i < dp_command_data.inp_offset)
        o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.inp_gating[i*InpGatingExpansion +: InpGatingExpansion] = {InpGatingExpansion{1'b0}};
      else if ((i - dp_command_data.inp_offset) <= dp_command_data.inp_size)
        o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.inp_gating[i*InpGatingExpansion +: InpGatingExpansion] = {InpGatingExpansion{1'b1}};
      else
        o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.inp_gating[i*InpGatingExpansion +: InpGatingExpansion] = {InpGatingExpansion{1'b0}};
    end
    // N-hot encoding of oup_gating based on oup_offset and oup_size with expansion
    // to account for different gating granularity between cmd and dp
    for (int i = 0; i < MVM_NR_OUTPUT_PW; i++) begin
      if (i < dp_command_data.oup_offset)
        o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.oup_gating[i*OupGatingExpansion +: OupGatingExpansion] = {OupGatingExpansion{1'b0}};
      else if ((i - dp_command_data.oup_offset) <= dp_command_data.oup_size)
        o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.oup_gating[i*OupGatingExpansion +: OupGatingExpansion] = {OupGatingExpansion{1'b1}};
      else
        o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.oup_gating[i*OupGatingExpansion +: OupGatingExpansion] = {OupGatingExpansion{1'b0}};
    end

    o_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.par2bser_we = dp_cmds_end;

    // IMC CMD signals
    o_exe_dp_cmd_tdata.imc_cmd_sig.imc_compute_gate_clock = dp_command_metadata.format ==  aic_dp_cmd_gen_pkg::Bypass;
    o_exe_dp_cmd_tdata.imc_cmd_sig.imc_compute_weight_set = dp_command_data.ws;

    // OUP CMD signals
    o_exe_dp_cmd_tdata.out_dp_cmd_sig.tlast = (dp_cmd_last && dp_cmds_end) || (dp_command_metadata.format ==  aic_dp_cmd_gen_pkg::Bypass);

    o_exe_dp_cmd_tdata.dp_ctrl = dp_command_metadata.extra;

    o_exe_dp_cmd_tvalid = dp_command_valid || (dp_command_metadata.format ==  aic_dp_cmd_gen_pkg::Bypass);

    // BYPASS only supported by IFD0
    o_exe_dp_cmd_tdata.bypass_enable = (dp_command_metadata.format ==  aic_dp_cmd_gen_pkg::Bypass);

  end

endmodule


`endif  // MVM_EXE_CMD_SHIM_DCMP_SV
