// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef MVM_EXE_CMD_SHIM_SV
`define MVM_EXE_CMD_SHIM_SV

module mvm_exe_cmd_shim
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  (
  input wire  i_clk,
  input logic i_rst_n,

  // DP general command
  input  mvm_exe_qcmd_t                        i_dp_command_data,
  input  aic_dp_cmd_gen_pkg::metadata_t        i_dp_command_metadata,
  input  aic_dp_cmd_gen_pkg::loop_iterations_t i_dp_command_iterations,
  input  logic                                 i_dp_command_last,
  input  logic                                 i_dp_command_valid,
  output logic                                 o_dp_command_ready,
  output logic                                 o_dp_done,

  /// Pulse from the datapath indicating that all datapath commands have been executed
  ///
  // DP-CMD stream IFD0
  output mvm_exe_dp_cmd_t o_ifd0_exe_dp_cmd_tdata,
  output logic            o_ifd0_exe_dp_cmd_tvalid,
  input  logic            i_ifd0_exe_dp_cmd_tready,
  output mvm_exe_dp_cmd_t o_ifd2_exe_dp_cmd_tdata,
  output logic            o_ifd2_exe_dp_cmd_tvalid,
  input  logic            i_ifd2_exe_dp_cmd_tready,

  input  logic            i_exe_dp_done,
  // Err signals
  output logic err_exe_inp_offset_size_overflow,
  output logic err_exe_oup_offset_size_overflow,
  output logic err_exe_advance_mode_even_inst
);
  //////////////////////
  // Signals
  mvm_exe_qcmd_t                 ifd0_dp_command_data;
  aic_dp_cmd_gen_pkg::metadata_t ifd0_dp_command_metadata;
  logic                          ifd0_dp_command_last;
  logic                          ifd0_dp_command_valid;
  logic                          ifd0_dp_command_ready;

  mvm_exe_qcmd_t                 ifd2_dp_command_data;
  aic_dp_cmd_gen_pkg::metadata_t ifd2_dp_command_metadata;
  logic                          ifd2_dp_command_last;
  logic                          ifd2_dp_command_valid;
  logic                          ifd2_dp_command_ready;

  logic                          enable_ifd0;
  logic                          enable_ifd2;
  logic                          advance_mode;
  logic                          simple_mode;
  logic                          select_ifd;

  exe_cmd_dp_ctrl_field_t        dp_ctrl;

  /////////////////////
  // RTL

  always_comb o_dp_done = i_exe_dp_done;

  // Detect overflows caused by infeasible offset and size combinations
  always_comb err_exe_inp_offset_size_overflow = i_dp_command_valid && ((i_dp_command_data.inp_offset + i_dp_command_data.inp_size) > MVM_NR_INPUT_PW-1);
  always_comb err_exe_oup_offset_size_overflow = i_dp_command_valid && ((i_dp_command_data.oup_offset + i_dp_command_data.oup_size) > MVM_NR_OUTPUT_PW-1);
  always_comb err_exe_advance_mode_even_inst = !advance_mode && select_ifd;

  always_comb o_dp_command_ready = select_ifd ? ifd2_dp_command_ready : ifd0_dp_command_ready;

  always_comb dp_ctrl = i_dp_command_metadata.extra;

  always_comb advance_mode = (i_dp_command_metadata.format != aic_dp_cmd_gen_pkg::Bypass) && dp_ctrl.double_bw_en && (dp_ctrl.double_bw_mode == advanced);
  always_comb simple_mode  = (i_dp_command_metadata.format != aic_dp_cmd_gen_pkg::Bypass) && dp_ctrl.double_bw_en && (dp_ctrl.double_bw_mode == simple);

  always_ff @(posedge i_clk, negedge i_rst_n) begin : select_ifd_seq_proc
    if(!i_rst_n)                                                      select_ifd <= 1'b0;
    else if(i_dp_command_valid && o_dp_command_ready && advance_mode) select_ifd <= !select_ifd;
  end

  always_comb enable_ifd0 = !select_ifd;
  always_comb enable_ifd2 = (i_dp_command_metadata.format != aic_dp_cmd_gen_pkg::Bypass)
                         && (simple_mode || dp_ctrl.input_precision == inp_int16 || select_ifd);

  always_comb begin : exe_dp_cmd_ifd0
    ifd0_dp_command_valid      = enable_ifd0 ? i_dp_command_valid : 1'b0;
    ifd0_dp_command_data       = i_dp_command_data;
    ifd0_dp_command_metadata   = i_dp_command_metadata;
    ifd0_dp_command_last       = i_dp_command_last;
  end

  always_comb begin : exe_dp_cmd_ifd2
    ifd2_dp_command_valid = enable_ifd2 ? i_dp_command_valid : 1'b0;
    ifd2_dp_command_data = i_dp_command_data;
    if (dp_ctrl.double_bw_en && dp_ctrl.double_bw_mode == simple) begin
      ifd2_dp_command_data.oup_offset = i_dp_command_data.oup_offset + (MVM_NR_OUTPUT_PW/2);
    end
    ifd2_dp_command_metadata   = i_dp_command_metadata;
    ifd2_dp_command_last       = i_dp_command_last;
  end

  mvm_exe_cmd_shim_dcmp #(
    .P_PROPAGATE_LAST(1'b1)
  ) u_exe_cmd_ifd0 (
    .i_clk,
    .i_rst_n,
    .i_dp_command_data      (ifd0_dp_command_data      ),
    .i_dp_command_metadata  (ifd0_dp_command_metadata  ),
    .i_dp_command_last      (ifd0_dp_command_last      ),
    .i_dp_command_valid     (ifd0_dp_command_valid     ),
    .o_dp_command_ready     (ifd0_dp_command_ready     ),
    .i_inst_last            (ifd2_dp_command_last      ),
    .o_exe_dp_cmd_tdata     (o_ifd0_exe_dp_cmd_tdata   ),
    .o_exe_dp_cmd_tvalid    (o_ifd0_exe_dp_cmd_tvalid  ),
    .i_exe_dp_cmd_tready    (i_ifd0_exe_dp_cmd_tready  )
  );

  mvm_exe_cmd_shim_dcmp #(
    .P_PROPAGATE_LAST(1'b0)
  ) u_exe_cmd_ifd2 (
    .i_clk,
    .i_rst_n,
    .i_dp_command_data      (ifd2_dp_command_data      ),
    .i_dp_command_metadata  (ifd2_dp_command_metadata  ),
    .i_dp_command_last      (ifd2_dp_command_last      ),
    .i_dp_command_valid     (ifd2_dp_command_valid     ),
    .o_dp_command_ready     (ifd2_dp_command_ready     ),
    .i_inst_last            (1'b0                      ),
    .o_exe_dp_cmd_tdata     (o_ifd2_exe_dp_cmd_tdata   ),
    .o_exe_dp_cmd_tvalid    (o_ifd2_exe_dp_cmd_tvalid  ),
    .i_exe_dp_cmd_tready    (i_ifd2_exe_dp_cmd_tready  )
  );

  /////////////
  // Assertions
`ifdef ASSERTIONS_ON

  property exe_inp_offset_size_overflow;
    @(posedge i_clk) disable iff (!i_rst_n) not err_exe_inp_offset_size_overflow;
  endproperty
  property exe_oup_offset_size_overflow;
    @(posedge i_clk) disable iff (!i_rst_n) not err_exe_oup_offset_size_overflow;
  endproperty
  property exe_advance_mode_even_inst;
    @(posedge i_clk) disable iff (!i_rst_n) not err_exe_advance_mode_even_inst;
  endproperty

  assert property (exe_inp_offset_size_overflow)
  else
    $error(
        "Input offset and size add up to a value larger than NR_INPUT_PWs which causes an unsupported overlfow");
  assert property (exe_oup_offset_size_overflow)
  else
    $error(
        "Output offset and size add up to a value larger than NR_OUTPUT_PWs which causes an unsupported overlfow");
  assert property (exe_advance_mode_even_inst)
  else
    $error(
        "Number of instruction for the advance mode should be even number");

`endif  // ASSERTIONS_ON



endmodule


`endif  // MVM_EXE_CMD_SHIM_SV
