// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: This block translates upto 8 PWs (consisting of PW_LEN bytes each) at a time into a serial bit stream.
// First PWs are loaded into one of two buffer sets. The position of a PW with a buffer is controlled trough inp_buf_wr_addr.
// Once a set contains the necessary PWs, par2bser_we can be used to trigger the start of the serial output stream.
// When this bit is set, the buffer sets switch places and an internal counter runs the serialization from msb (7) to lsb (0).
// During the active period of the counter, m_tvalid_o is asserted to indicate that the output vector contains valid bits.
// Internally, the CMD stream is passed through a FIFO to keep it synchronized with output data flow.
// Finally, while a par2bser conversion is running, the other buffer set can be loaded concurrently to allow for uninterrupted output streams
// Owner: roel uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_PAR2BSER_SV
`define MVM_PAR2BSER_SV

module mvm_par2bser
  import imc_bank_pkg::*;
  import mvm_pkg::*;
#(
  parameter int unsigned DATA_W = 8,
  parameter int unsigned PW_LEN = 64,
  parameter int unsigned UIN = 512,
  parameter int unsigned GATE_GRANULARITY = 32
) (
  input wire i_clk,
  input wire i_rst_n,
  // Incoming PWs
  input logic [PW_LEN - 1:0][DATA_W - 1 : 0] inp_buf_pw_i,
  // Incoming ctrl stream
  input mvm_exe_dp_cmd_t s_cmd_data_i,
  input logic s_tvalid_i,
  output logic s_tready_o,
  // Outgoing ctrl stream
  output imc_acc_dp_cmd_t m_cmd_data_o,
  output logic m_tvalid_o,
  input logic m_tready_i,
  // Outgoing serial data vector
  output logic imc_acc_stall_o,
  output logic [UIN - 1 : 0] par2bser_uin_o,
  // Status signal
  output logic serial_conversion_running_o,

  // Util limiting
  input logic csr_power_smooth_dummy_ops_i,
  input logic i_util_limit_trigger_nop,

  input logic [2:0] i_util_row_upscaling_factor,
  input logic [2:0] i_util_col_upscaling_factor,

  // Current Utilization
  output logic [MVM_UTIL_WIDTH-1:0] o_current_util,
  output logic                      o_current_util_valid,

  // Active rows/cols used by ramp up controller
  output logic [$clog2(MVM_INP_GATING_DW):0] o_nb_active_rows,
  output logic [$clog2(MVM_OUP_GATING_DW):0] o_nb_active_cols
);
  // verilog_lint: waive-start line-length
  localparam int unsigned NumGates = PW_LEN / GATE_GRANULARITY;  // 64/32=2
  localparam int unsigned NumPwords = UIN / PW_LEN;  // 512/64=8


  // Send out stall cycles if the downstream is not ready
  assign imc_acc_stall_o = !m_tready_i;

  logic [2:0] serial_idx;
  // Assign some ctrl signals to par2bser control values
  assign m_cmd_data_o.acc_dp_cmd_sig.acc_output_enable     = (serial_idx == 0 & serial_conversion_running_o) ? m_cmd_data_o.acc_dp_cmd_sig.oup_gating : '0;
  assign m_cmd_data_o.acc_dp_cmd_sig.acc_clear = (serial_idx == 7 & serial_conversion_running_o);
  assign m_cmd_data_o.acc_dp_cmd_sig.acc_shift_pos = {1'b0, serial_idx};

  // Set that is currently being filled by the input PWs
  logic active_set;
  // Set that is currently being used for the par2bser output
  logic stable_set;
  // Full width bit vectors beloning to each set
  logic [UIN-1:0][DATA_W-1:0] full_vector_set0;
  logic [UIN-1:0][DATA_W-1:0] full_vector_set1;

  // Gate trigger signals with s_tvalid
  logic par2bser_we_int, inp_buf_we_int;
  assign par2bser_we_int = s_cmd_data_i.par2bser_dp_cmd_sig.par2bser_we & s_tvalid_i;
  assign inp_buf_we_int  = s_cmd_data_i.par2bser_dp_cmd_sig.inp_buf_we & s_tvalid_i;

  // create buffer sets


  // Set 0
  for (genvar i = 0; i < NumPwords; i = i + 1) begin : g_par2bser_buffer_set0
    logic [PW_LEN-1:0][DATA_W-1:0] output_wire;
    logic inp_buf_we;
    assign inp_buf_we = (active_set == 0) && (s_cmd_data_i.par2bser_dp_cmd_sig.inp_buf_wr_addr == i) && (inp_buf_we_int);
    mvm_inp_buf_reg #(
      .DATA_W(DATA_W),
      .PW_LEN(PW_LEN),
      .GATE_GRANULARITY(GATE_GRANULARITY)
    ) mvm_inp_buf_reg_inst (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .inp_buf_pw_i(inp_buf_pw_i),
      .inp_buf_we_i(inp_buf_we),
      .inp_buf_group_enable_i(s_cmd_data_i.par2bser_dp_cmd_sig.inp_gating[(i+1)*NumGates-1:i*NumGates]),
      .inp_buf_oup_o(output_wire)
    );
    assign full_vector_set0[i*(PW_LEN)+:PW_LEN] = output_wire;
  end

  // Set 1
  for (genvar i = 0; i < NumPwords; i = i + 1) begin : g_par2bser_buffer_set1
    logic [PW_LEN-1:0][DATA_W-1:0] output_wire;
    logic inp_buf_we;
    assign inp_buf_we = (active_set == 1) && (s_cmd_data_i.par2bser_dp_cmd_sig.inp_buf_wr_addr == i) && (inp_buf_we_int);
    mvm_inp_buf_reg #(
      .DATA_W(DATA_W),
      .PW_LEN(PW_LEN),
      .GATE_GRANULARITY(GATE_GRANULARITY)
    ) mvm_inp_buf_reg_inst (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .inp_buf_pw_i(inp_buf_pw_i),
      .inp_buf_we_i(inp_buf_we),
      .inp_buf_group_enable_i(s_cmd_data_i.par2bser_dp_cmd_sig.inp_gating[(i+1)*NumGates-1:i*NumGates]),
      .inp_buf_oup_o(output_wire)
    );
    assign full_vector_set1[i*(PW_LEN)+:PW_LEN] = output_wire;
  end

  ///////////////
  // Check Busy status
  logic [1:0] set_busy;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : set_busy_seq_proc
    if (!i_rst_n) set_busy <= '0;
    else foreach(set_busy[set])
      if (!set_busy[set] && inp_buf_we_int && (set == active_set))     set_busy[set] <= '1;
      else if(set_busy[set] && par2bser_we_int && (set == stable_set)) set_busy[set] <= '1;
  end

  /////////////////
  // par2bser "FSM"
  // Sort of state machine (without real state definition) that handles the conversion from par2bser
  // State is encoded implicitly in the serial_idx counter value
  logic serial_conversion_running_q;
  assign serial_conversion_running_o = serial_conversion_running_q & (~i_util_limit_trigger_nop);
  assign m_tvalid_o = serial_conversion_running_o && set_busy[stable_set];

  always_ff @(posedge i_clk, negedge i_rst_n) begin : stable_set_seq_proc
    if (!i_rst_n)                                       stable_set <= '1;
    else if (s_tvalid_i & s_tready_o & par2bser_we_int) stable_set <= !stable_set;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin : par2bser_fsm
    if (!i_rst_n) begin
      serial_idx <= 0;
      serial_conversion_running_q <= 1'b0;
      active_set <= 0;
      m_cmd_data_o.acc_dp_cmd_sig.oup_gating <= 16'h0000;
      m_cmd_data_o.acc_dp_cmd_sig.inp_gating <= 16'h0000;
      m_cmd_data_o.imc_cmd_sig.imc_compute_weight_set <= '0;
      m_cmd_data_o.imc_cmd_sig.imc_compute_gate_clock <= 1'b1;
      m_cmd_data_o.out_dp_cmd_sig.tlast <= 1'b0;
      m_cmd_data_o.dibw_en <= 1'b0;
      m_cmd_data_o.adv_mode_en <= simple;
      m_cmd_data_o.acc_dp_cmd_sig.acc_input_precision <= '0;
      m_cmd_data_o.acc_dp_cmd_sig.acc_weight_precision <= '0;
    end else if (m_tready_i && (!i_util_limit_trigger_nop)) begin
      // Start new par2bser conversion on par2bser_we_int, but only when previous conversion has finished (i.e. serial_idx==0)
      if (par2bser_we_int & (serial_idx == 0)) begin
        active_set <= ~active_set;
        serial_idx <= 7;
        serial_conversion_running_q <= 1'b1;
        // Sample some ctrl values that should remain stable over the serial conversion
        m_cmd_data_o.out_dp_cmd_sig.tlast <= s_cmd_data_i.out_dp_cmd_sig.tlast;
        m_cmd_data_o.acc_dp_cmd_sig.oup_gating <= s_cmd_data_i.par2bser_dp_cmd_sig.oup_gating;
        m_cmd_data_o.acc_dp_cmd_sig.inp_gating <= s_cmd_data_i.par2bser_dp_cmd_sig.inp_gating;
        m_cmd_data_o.imc_cmd_sig.imc_compute_gate_clock <= s_cmd_data_i.imc_cmd_sig.imc_compute_gate_clock;
        m_cmd_data_o.imc_cmd_sig.imc_compute_weight_set <= s_cmd_data_i.imc_cmd_sig.imc_compute_weight_set;
        m_cmd_data_o.dibw_en <= s_cmd_data_i.dp_ctrl.double_bw_en;
        m_cmd_data_o.adv_mode_en <= s_cmd_data_i.dp_ctrl.double_bw_mode;
        m_cmd_data_o.acc_dp_cmd_sig.acc_input_precision <= s_cmd_data_i.dp_ctrl.input_precision;
        m_cmd_data_o.acc_dp_cmd_sig.acc_weight_precision <= s_cmd_data_i.dp_ctrl.weight_precision;
      end else if (serial_idx > 0) begin
        serial_idx <= serial_idx - 1;
      end else begin
        serial_conversion_running_q <= 1'b0;
        m_cmd_data_o.out_dp_cmd_sig.tlast <= 1'b0;
        m_cmd_data_o.imc_cmd_sig.imc_compute_gate_clock <= 1'b1;
        m_cmd_data_o.acc_dp_cmd_sig.oup_gating <= 16'h0000;
        m_cmd_data_o.dibw_en <= 1'b0;
        m_cmd_data_o.adv_mode_en <= simple;
      end
    end
  end

  // Output ready generation.
  always_comb begin : ready_generation
    // Only when a serial conversion has to start, ready can be blocked by the backpressure from downstream or the nop trigger
    if (par2bser_we_int) begin
      if (m_tready_i && (serial_idx == 0) && (!i_util_limit_trigger_nop)) s_tready_o = 1;
      else s_tready_o = 0;
    end else s_tready_o = 1;
  end

  // Output muxes controlled by serial_idx and stable_set
  for (genvar i = 0; i < UIN; i++) begin : gen_out_muxes
    always_comb begin
      // Gate serial output line based on input gating pattern.
      if (m_cmd_data_o.acc_dp_cmd_sig.inp_gating[i/GATE_GRANULARITY]) begin
        par2bser_uin_o[i] = stable_set ? full_vector_set1[i][serial_idx] : full_vector_set0[i][serial_idx];
      end else begin
        par2bser_uin_o[i] = 0;
      end
    end
  end

  logic [$clog2(MVM_INP_GATING_DW):0] nb_active_rows;
  logic [$clog2(MVM_OUP_GATING_DW):0] nb_active_cols;
  // Count the n-hot bits of the inp/oup_gating to determine the number of active rows and cols
  always_comb begin
    nb_active_rows = '0;
    nb_active_cols = '0;
    foreach (m_cmd_data_o.acc_dp_cmd_sig.inp_gating[i])
      nb_active_rows += m_cmd_data_o.acc_dp_cmd_sig.inp_gating[i];
    foreach (m_cmd_data_o.acc_dp_cmd_sig.oup_gating[i])
      nb_active_cols += m_cmd_data_o.acc_dp_cmd_sig.oup_gating[i];
  end


  always_comb o_nb_active_rows = nb_active_rows;
  always_comb o_nb_active_cols = nb_active_cols;

  // Compute util value. This is at the resolution of the imc_banks and their block gating granularity, i.e., at 16x16 matrix
  // The higher resolution is required to deal with dummy power ops in the pipeline.
  always_comb begin
    o_current_util = '0;
    // If we do power dummy cycles in the mvm pipeline this impacts the util number
    // Only halve of the unused imc_banks will not be used. So we have to take this into account when computing the util value
    if (csr_power_smooth_dummy_ops_i) begin
      // Avoid problems when someone would somehow manage to run an operation with 0 active cols (currently the cmd gen does not allow this, but you never know in the future)
      if (nb_active_cols != '0)
        o_current_util = nb_active_rows*(nb_active_cols+((MVM_NB_IMC_BANKS-nb_active_cols)>>1)) +
                         nb_active_rows*i_util_row_upscaling_factor +
                         (nb_active_cols+((MVM_NB_IMC_BANKS-nb_active_cols)>>1))*i_util_col_upscaling_factor;
    end else begin
      // Spyglass does not figure out he has to add the bitwidths of the two operands in the multiplication...
      o_current_util = (nb_active_rows * nb_active_cols) +
                       (nb_active_rows * i_util_row_upscaling_factor) +
                       (nb_active_cols * i_util_col_upscaling_factor) ;
    end
  end

  always_comb o_current_util_valid = serial_conversion_running_o & (~imc_acc_stall_o);

`ifdef ASSERTIONS_ON
  property active_cols_is_even;
    @(posedge i_clk) disable iff (!i_rst_n) ##1 (nb_active_cols % 2 == 0);
  endproperty

  active_cols_is_even_assertion :
  assert property (active_cols_is_even)
  else $error("Number of active imc_banks / MVM columns is not even!");
`endif  //ASSERTIONS_ON
// verilog_lint: waive-stop line-length
endmodule

`endif  // MVM_PAR2BSER_SV
