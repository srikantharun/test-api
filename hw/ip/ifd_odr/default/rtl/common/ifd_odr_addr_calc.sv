// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Calculate the address
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_ADDR_CALC_SV_
`define _IFD_ODR_ADDR_CALC_SV_

module ifd_odr_addr_calc
  import ifd_odr_pkg::*;
#(
  parameter int unsigned MEM_COORD_ADDR_W = 32,
  parameter int unsigned ABS_BUFF_W = 32
) (
  input wire i_clk,
  input wire i_rst_n,

  input logic pipe_en,

  input logic [      MEM_COORD_ADDR_W-1:0] addr_a,
  input logic [      MEM_COORD_ADDR_W-1:0] addr_b,
  input logic [      MEM_COORD_ADDR_W-1:0] addr_c,
  input logic [      MEM_COORD_ADDR_W-1:0] addr_d,
  input logic [      IFD_ODR_AG_MEM_OFFSET_DW-1:0] mem_offset,
  input logic [        IFD_ODR_AG_MEM_BASE_DW-1:0] mem_base,
  input logic [       IFD_ODR_AG_MEM_BSIZE_DW-1:0] mem_bsize,
  input logic [IFD_ODR_AG_RING_BUFFER_SIZE_DW-1:0] ring_buff_size,

  output logic [IFD_ODR_AG_MEM_BASE_DW-1 : 0] addr,
  output logic err_addr_out_of_range
);

  localparam int unsigned CoordAddrAdds = ((MEM_COORD_ADDR_W < IFD_ODR_AG_MEM_OFFSET_DW) ?
      IFD_ODR_AG_MEM_OFFSET_DW : MEM_COORD_ADDR_W) + 2;

  logic [CoordAddrAdds-1:0] coord_addr_adds;
  logic [ABS_BUFF_W-1:0] abs_offset;
  reg [ABS_BUFF_W-1:0] abs_offset_q;
  logic [ABS_BUFF_W-1:0] abs_offset_rb;

  reg [MEM_COORD_ADDR_W-1:0] addr_a_q;
  reg [MEM_COORD_ADDR_W-1:0] addr_b_q;
  reg [MEM_COORD_ADDR_W-1:0] addr_c_q;
  reg [MEM_COORD_ADDR_W-1:0] addr_d_q;

  // check if address is under base, or offset is larger then bsize:
  logic err_addr_under;
  logic err_off_above;
  logic addr_err;
  logic addr_err_q;

  logic [IFD_ODR_AG_MEM_BASE_DW-1:0] addr_res;
  reg [IFD_ODR_AG_MEM_BASE_DW-1:0] addr_res_q;

  // LHS requires wide range to fullfill proper addition:
  //spyglass disable_block W164b
  assign coord_addr_adds = addr_a_q + addr_b_q + addr_c_q + addr_d_q + mem_offset;
  //spyglass enable_block W164b
  assign abs_offset = coord_addr_adds[ABS_BUFF_W-1:0];  // truncate

  ifd_odr_ring_buffer #(
    .ADDR_W(ABS_BUFF_W),
    .RB_AW(IFD_ODR_AG_RING_BUFFER_SIZE_DW),
    .ADDR_GR_BYTES(IFD_ODR_PWORD64_LEN),
    .RB_GR_BYTES(IFD_ODR_AG_RING_BUFFER_SIZE_GRANULARITY),
    .RB_FLOPS(IFD_ODR_AG_RING_BUFFER_FLOPS)
  ) u_ring_buffer (
    .i_clk(i_clk),

    .pipe_en(pipe_en),

    .addr_in(abs_offset),
    .ring_buff_size(ring_buff_size),

    .addr_out(abs_offset_rb)
  );

  assign addr_res = abs_offset_rb + mem_base;

  assign err_addr_under = addr_res < mem_base;
  assign err_off_above = abs_offset_rb > ABS_BUFF_W'(mem_bsize);
  assign addr_err = (err_addr_under | err_off_above) & |mem_bsize;  // only check if bsize != 0

  // Pipe registers:
  // requires reset:
  always_ff @(posedge i_clk or negedge i_rst_n) begin : pipe_regs_rst
    if (i_rst_n == 1'b0) begin
      // error out of range is control (captured by IRQ), so needs to reset
      addr_err_q <= '0;
    end else begin
      if (pipe_en) begin
        addr_err_q <= addr_err;
      end
    end
  end

  // no reset required, as it's data that doesn't drive ctrl
  // spyglass disable_block STARC05-3.3.1.4b
  // spyglass disable_block STARC-2.3.4.3
  always_ff @(posedge i_clk) begin : pipe_regs
    if (pipe_en) begin
      addr_res_q <= addr_res;

      addr_a_q   <= addr_a;
      addr_b_q   <= addr_b;
      addr_c_q   <= addr_c;
      addr_d_q   <= addr_d;
    end
  end
  // spyglass enable_block STARC-2.3.4.3
  // spyglass enable_block STARC05-3.3.1.4b
  assign addr = addr_res_q;
  assign err_addr_out_of_range = addr_err_q;

endmodule

`endif  // _IFD_ODR_ADDR_CALC_SV_
