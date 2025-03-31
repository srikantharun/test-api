// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: RVVI Dump Interface
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef __CVA6V_RVVI_DUMP_IF_SV__
`define __CVA6V_RVVI_DUMP_IF_SV__


interface cva6v_rvvi_dump_if   #(
  parameter integer XLEN = 64,
  parameter integer FLEN = 32,
  parameter integer VLEN = 4096,
  parameter integer CSR_NUM = 4096
)(
  input  logic                clk_i,
  input  logic                rst_ni
);

  logic              valid;
  logic[63:0]        order;
  logic[63:0]        insn;
  logic              trap;
  logic              debug_mode;
  logic[XLEN-1:0]    pc_rdata;
  logic[XLEN-1:0]    x_wdata[32];
  logic[31:0]        x_wb;
  logic[FLEN-1:0]    f_wdata[32];
  logic[31:0]        f_wb;
  logic[VLEN-1:0]    v_wdata[32];
  logic[31:0]        v_wb;
  logic[XLEN-1:0]    csr[4096];
  logic[CSR_NUM-1:0] csr_wb;
  logic              lrsc_cancel;
  logic[XLEN-1:0]    pc_wdata;
  logic              intr;
  logic              halt;
  logic[1:0]         ixl;
  logic[1:0]         mode;

endinterface



`endif // __CVA6V_RVVI_DUMP_IF_SV__
