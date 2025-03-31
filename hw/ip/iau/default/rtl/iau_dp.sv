// (C) Copyright Axelera AI 2022
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Datapath of IAU decodes and executes instructions from the DPcmd AXI stream.
// Contains eight internal accumulation registers and exposes input and output AXI streams
// via stream registers. Supports Repeat For Stream (RFS) instructions. If the RFS flag is
// set for an instruction, it is repeated until the input stream signals TLAST. Bypass mode
// is supported via an RFS mv instruction from the input stream to the output stream.
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef IAU_DP_SV
`define IAU_DP_SV

// verilog_lint: waive-start line-length
module iau_dp
  import iau_pkg::*;
#(
  localparam int unsigned InWordDw = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE,
  localparam int unsigned OutWordDw = aic_common_pkg::AIC_PWORD_I32_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE,
  localparam int unsigned PWordSize = aic_common_pkg::AIC_PWORD_SIZE,
  localparam int unsigned IW = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH,
  localparam int unsigned OW = aic_common_pkg::AIC_PWORD_I32_AXIS_TDATA_WIDTH,
  localparam int unsigned DW = OutWordDw
) (
  input wire i_clk,
  input wire i_rst_n,
  input logic i_scan_en,

  // CSR configuration
  input logic csr_signed_operation_i,
  input logic csr_saturated_add_i,

  // DPcmd AXI stream
  input  logic      dpcmd_tvalid_i,
  input  iau_dp_cmd_t dpcmd_tdata_i,
  input  logic      dpcmd_tvector_mode_i,
  input  logic      dpcmd_tlast_i,
  output logic      dpcmd_tready_o,

  // DP done
  output logic dp_done_o,

  // Input AXI stream
  input  logic          in_tvalid_i,
  input  logic [PWordSize-1:0] [InWordDw-1:0] in_tdata_i,
  //input  logic [ISW-1:0] in_tstrb_i,
  input  logic          in_tlast_i,
  output logic          in_tready_o,

  // Output AXI stream
  output logic          out_tvalid_o,
  output logic [PWordSize-1:0] [OutWordDw-1:0] out_tdata_o,
  //output logic [OSW-1:0] out_tstrb_o,
  output logic          out_tlast_o,
  input  logic          out_tready_i,

  // Status observation
  output iau_csr_reg_pkg::iau_csr_hw2reg_dp_status_reg_t dp_status_o,

  // Error and IRQ signals
  output logic err_act_in_stream_o,
  output logic err_act_out_stream_o,
  output logic err_early_tlast_stream_in_o,
  output logic err_early_tlast_stream_out_o,
  output logic err_illegal_rfs_instr_o
);

  // Decode instruction
  opcode_e                       instr_opcode;
  logic                          instr_rfs;
  logic                          instr_dst_used;
  logic                          instr_dst_stream;
  logic                          instr_dst_stream_last;
  logic    [           2:0]      instr_dst_acc_reg;
  logic    [           1:0]      instr_src_used;
  logic    [           1:0]      instr_src_stream;
  logic    [           1:0][2:0] instr_src_acc_reg;
  logic    [           1:0]      instr_src_peek;

  // Input Handshake
  logic [PWordSize-1:0][InWordDw-1:0]      in_tdata_array;

  // Sign Extension
  localparam int unsigned ExtendLen = DW - InWordDw;

  logic in_stream_last;
  logic in_stream_vld;

  // Select operands
  logic op_a_vld;
  logic op_b_vld;

  // Output buffer
  logic [PWordSize-1:0][DW-1:0] out_buf_data_q;
  logic out_buf_vld_d, out_buf_vld_q;
  logic out_buf_last_d, out_buf_last_q;
  logic out_buf_rdy;

  // Execute instruction
  logic dst_rdy;
  logic instr_stalled;
  logic exe_instr;

  // Error detection and status
  logic act_in_stream;
  logic act_out_stream;
  logic stalled_in_stream, stalled_cmd_stream;
  logic act_flag_in_stream_d, act_flag_in_stream_q;
  logic act_flag_out_stream_d, act_flag_out_stream_q;
  logic exe_last_instr;
  logic illegal_rfs_instr;
  logic no_stream_in_act_flag_d, no_stream_in_act_flag_q;
  logic no_stream_out_act_flag_d, no_stream_out_act_flag_q;

  /////////////
  // Decode instruction
  always_comb begin : comb_decode_instr
    instr_opcode          = dpcmd_tdata_i.opcode;
    instr_rfs             = dpcmd_tdata_i.rfs;
    instr_dst_stream      = dpcmd_tdata_i.dst[3];
    instr_dst_stream_last = dpcmd_tdata_i.dst[0];
    instr_dst_acc_reg     = dpcmd_tdata_i.dst[2:0];
    instr_src_stream[0]   = dpcmd_tdata_i.src0[3];
    instr_src_acc_reg[0]  = dpcmd_tdata_i.src0[2:0];
    instr_src_stream[1]   = dpcmd_tdata_i.src1[3];
    instr_src_acc_reg[1]  = dpcmd_tdata_i.src1[2:0];
    instr_src_peek[0]     = dpcmd_tdata_i.src0[3] & dpcmd_tdata_i.src0[0];
    instr_src_peek[1]     = dpcmd_tdata_i.src1[3] & dpcmd_tdata_i.src1[0];

    // In RFS instructions pass the TLAST of input stream to output stream for bypass mode
    if (instr_rfs == 1'b1) begin
      instr_dst_stream_last = in_stream_last;
    end

    // Indicate whether destination or operands are used
    unique case (instr_opcode)
      OP_NOP: begin
        instr_dst_used    = 1'b0;
        instr_src_used[0] = 1'b0;
        instr_src_used[1] = 1'b0;
      end
      OP_MV: begin
        instr_dst_used    = 1'b1;
        instr_src_used[0] = 1'b1;
        instr_src_used[1] = 1'b0;
      end
      OP_MAX: begin
        instr_dst_used    = 1'b1;
        instr_src_used[0] = 1'b1;
        instr_src_used[1] = 1'b1;
      end
      OP_MIN: begin
        instr_dst_used    = 1'b1;
        instr_src_used[0] = 1'b1;
        instr_src_used[1] = 1'b1;
      end
      OP_ADD, OP_SUB: begin
        instr_dst_used    = 1'b1;
        instr_src_used[0] = 1'b1;
        instr_src_used[1] = 1'b1;
      end
      default: begin
        instr_dst_used    = 1'b0;
        instr_src_used[0] = 1'b0;
        instr_src_used[1] = 1'b0;
      end
    endcase
  end : comb_decode_instr

  /////////////
  // Illegal RFS instruction
  assign illegal_rfs_instr = instr_rfs & ~(|instr_src_stream);

  /////////////
  // Input Handshake
  always_comb in_tdata_array = in_tdata_i;
  assign in_tready_o = exe_instr & |(instr_src_used & instr_src_stream & ~instr_src_peek);

  /////////////
  // Per-pixel ALU datapath
  localparam logic [PWordSize-1:0] PixelIsMsb = {(PWordSize/2){2'b10}};
  iau_alu_ctrl_t [PWordSize-1:0] i16_ctrl_in, i16_ctrl_out;

  // wire up the alu control between the lsb and msb elements:
  always_comb for (int unsigned i=0; i<(PWordSize/2); i++) begin
    i16_ctrl_in[i*2]   = i16_ctrl_out[i*2+1];
    i16_ctrl_in[i*2+1] = i16_ctrl_out[i*2];
  end

  iau_pixel_dp #(
    .InWordDw(InWordDw),
    .PWordSize(PWordSize),
    .DW(DW)
  ) u_pixel_dp [PWordSize-1:0] (
    .i_clk,
    .i_rst_n,

    // static signals
    .i_pixel_is_msb(PixelIsMsb),

    // Global signals
    .csr_signed_operation_i,
    .csr_saturated_add_i,
    .instr_opcode,
    .vector_mode(dpcmd_tvector_mode_i),
    .instr_src_stream,
    .instr_src_acc_reg,
    .instr_dst_used,
    .instr_dst_stream,
    .instr_dst_acc_reg,
    .exe_instr,

    // Datapath
    .i_pixel_data(in_tdata_array),
    .o_pixel_data(out_buf_data_q),
    .i_i16_ctrl(i16_ctrl_in), // alu control signals in from previous element (only valid if pixel_is_msb)
    .o_i16_ctrl(i16_ctrl_out) // alu control signals out for next element (only valid if not pixel_is_msb)
  );

  assign in_stream_last = in_tvalid_i ? in_tlast_i : 1'b0;
  assign in_stream_vld  = in_tvalid_i;

  // Accumulation registers are always valid
  assign op_a_vld = instr_src_stream[0] ? in_stream_vld : 1'b1;
  assign op_b_vld = instr_src_stream[1] ? in_stream_vld : 1'b1;

  /////////////
  // Output buffer
  always_comb begin : comb_out_buf
    out_buf_vld_d  = out_buf_vld_q;
    out_buf_last_d = out_buf_last_q;

    // Consume valid output
    if (out_tready_i == 1'b1) begin
      out_buf_vld_d = 1'b0;
    end

    // Update output buffer
    if (exe_instr & instr_dst_used == 1'b1) begin
      if (instr_dst_stream == 1'b1) begin
        out_buf_last_d = instr_dst_stream_last;
        out_buf_vld_d  = 1'b1; // ASO-MULTI_ASSIGN : Set has higher priority than clear.
      end
    end
  end : comb_out_buf

  logic out_vector_mode_q;
  always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_out_buf
    if (i_rst_n == 1'b0) begin
      out_buf_vld_q  <= '0;
      out_buf_last_q <= '0;
      out_vector_mode_q <= '0;
    end else begin
      out_buf_vld_q  <= out_buf_vld_d;
      out_buf_last_q <= out_buf_last_d;
      out_vector_mode_q <= dpcmd_tvector_mode_i;
    end
  end : seq_out_buf

  // Output buffer can be consumed and filled at the same time
  // TODO: Might cause timing issues due to out_tready_i (needed for throughput)
  assign out_buf_rdy  = out_tready_i ? 1'b1 : ~out_buf_vld_q;

  // Output AXI stream
  assign out_tvalid_o = out_buf_vld_q;
  //assign out_tstrb_o  = '1;
  assign out_tlast_o  = out_buf_last_q;
  always_comb begin
    out_tdata_o = out_buf_data_q;
    if (out_vector_mode_q) begin // rewire elements:
      for (int unsigned i=0; i<PWordSize/2; i++) begin
        {out_tdata_o[2*i+1], out_tdata_o[2*i]} = {((2*DW)-IAU_DPU_I16_DW)'(0),
                                                    out_buf_data_q[2*i+1][IAU_DPU_I16_DW-InWordDw-1:0],
                                                    out_buf_data_q[2*i][InWordDw-1:0]};
      end
    end
  end
  /////////////
  // Execute instruction

  // Accumulation registers are always ready
  assign dst_rdy = instr_dst_stream ? out_buf_rdy : 1'b1;

  // Instruction not stalled if used operands valid and used destination ready or an illegal rfs instruction was detected
  assign instr_stalled = (instr_src_used[0] & ~op_a_vld) |
      (instr_src_used[1] & ~op_b_vld) | (instr_dst_used & ~dst_rdy) |
      illegal_rfs_instr;

  // Accept DPcmd if instruction not stalled and if RFS set also require last input
  // (RFS instructions are repeated until the input stream signals TLAST)
  assign dpcmd_tready_o = instr_rfs ? ((~instr_stalled) & in_stream_last) : ~instr_stalled;

  // Execute instruction if valid and instruction not stalled
  assign exe_instr = dpcmd_tvalid_i && ~instr_stalled;

  /////////////
  // Error detection and status

  // Input stream is truly stalled if we want to read it (no downstream stall) but there is no valid
  // data available
  assign stalled_in_stream = dpcmd_tvalid_i & |(instr_src_used & instr_src_stream) &
                             ~(instr_dst_used & ~dst_rdy) & ~in_stream_vld;
  // IAU can accept commands every cycle and there is no way of determining if the not-present
  // instruction would stall. We err on the side of false-positives when signalling this.
  assign stalled_cmd_stream = ~dpcmd_tvalid_i;

  // Sets a data stream to active once it has been used and resets to inactive upon its TLAST
  always_comb begin : comb_act_streams
    act_in_stream  = act_flag_in_stream_q;
    act_out_stream = act_flag_out_stream_q;

    if (exe_instr == 1'b1) begin
      if (|(instr_src_used & instr_src_stream) == 1'b1) begin
        act_in_stream = in_stream_last ? 1'b0 : 1'b1;
      end
      if (instr_dst_used & instr_dst_stream == 1'b1) begin
        act_out_stream = instr_dst_stream_last ? 1'b0 : 1'b1;
      end
    end
  end : comb_act_streams

  assign act_flag_in_stream_d  = act_in_stream;
  assign act_flag_out_stream_d = act_out_stream;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_act_streams
    if (i_rst_n == 1'b0) begin
      act_flag_in_stream_q  <= '0;
      act_flag_out_stream_q <= '0;
    end else begin
      act_flag_in_stream_q  <= act_flag_in_stream_d;
      act_flag_out_stream_q <= act_flag_out_stream_d;
    end
  end : seq_act_streams

  always_comb begin : comb_no_stream_act
    no_stream_in_act_flag_d  = no_stream_in_act_flag_q;
    no_stream_out_act_flag_d = no_stream_out_act_flag_q;

    if (exe_instr & in_stream_last & |(instr_src_used & instr_src_stream)) begin
      no_stream_in_act_flag_d = 1'b1;
    end

    if (exe_instr & instr_dst_stream_last & instr_dst_used & instr_dst_stream) begin
      no_stream_out_act_flag_d = 1'b1;
    end

    if (exe_instr & dpcmd_tlast_i) begin
      no_stream_in_act_flag_d  = 1'b0; // ASO-MULTI_ASSIGN : Clear has higher priority than set.
      no_stream_out_act_flag_d = 1'b0; // ASO-MULTI_ASSIGN : Clear has higher priority than set.
    end
  end : comb_no_stream_act

  always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_no_stream_act
    if (~i_rst_n) begin
      no_stream_in_act_flag_q  <= '0;
      no_stream_out_act_flag_q <= '0;
    end else begin
      no_stream_in_act_flag_q  <= no_stream_in_act_flag_d;
      no_stream_out_act_flag_q <= no_stream_out_act_flag_d;
    end
  end : seq_no_stream_act

  // With RFS the DPcmd stream TLAST could be constantly set, thus the program can not be checked
  // (RFS instructions are always a valid program and do not actually need to be checked)
  assign err_act_in_stream_o = instr_rfs ? 1'b0 : exe_instr & dpcmd_tlast_i & act_in_stream;
  assign err_act_out_stream_o = instr_rfs ? 1'b0 : exe_instr & dpcmd_tlast_i & act_out_stream;
  assign err_early_tlast_stream_in_o = instr_rfs ? 1'b0 : exe_instr & |(instr_src_used & instr_src_stream) & no_stream_in_act_flag_q;
  assign err_early_tlast_stream_out_o = instr_rfs ? 1'b0 : exe_instr & instr_dst_stream & instr_dst_used & no_stream_out_act_flag_q;
  assign err_illegal_rfs_instr_o = illegal_rfs_instr;

  // Signal done if last DPcmd has been executed and if RFS set also require last input
  // Note: Done is signalled after executing last instruction and not after last output
  assign exe_last_instr = exe_instr & dpcmd_tlast_i;
  assign dp_done_o = instr_rfs ? exe_last_instr & in_stream_last : exe_last_instr;

  /////////////
  // Status observation
  assign dp_status_o = '{
          in0_vld: '{d: in_tvalid_i},
          in0_rdy: '{d: in_tready_o},
          in0_lst: '{d: in_tlast_i},
          in0_stl: '{d: stalled_in_stream},
          out_vld: '{d: out_buf_vld_d},
          out_rdy: '{d: out_buf_rdy},
          out_lst: '{d: out_buf_last_d},
          out_stl: '{d: out_buf_vld_d & ~out_buf_rdy},
          dpcmd0_vld: '{d: dpcmd_tvalid_i},
          dpcmd0_rdy: '{d: dpcmd_tready_o},
          dpcmd0_lst: '{d: dpcmd_tlast_i},
          dpcmd0_stl: '{d: stalled_cmd_stream},
          current_op: '{d: instr_opcode},
          op_flag_rfs: '{d: instr_rfs},
          instr_stalled: '{d: instr_stalled}
      };

  /////////////
  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON

  // No streams should be active at the end of a program (last instruction)
  property no_act_in_stream_at_end;
    @(posedge i_clk) disable iff (!i_rst_n) (not err_act_in_stream_o);
  endproperty
  property no_act_out_stream_at_end;
    @(posedge i_clk) disable iff (!i_rst_n) (not err_act_out_stream_o);
  endproperty

  assert property (no_act_in_stream_at_end)
  else $error("At the end of program input stream still active!");

  assert property (no_act_out_stream_at_end)
  else $error("At the end of program output stream still active!");

`endif  // ASSERTIONS_ON
  //synopsys translate_on

endmodule
// verilog_lint: waive-stop line-length

`endif  // IAU_DP_SV
