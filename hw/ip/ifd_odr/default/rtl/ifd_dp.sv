// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of IFD data path
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_DP_SV_
`define _IFD_DP_SV_

module ifd_dp #(
  parameter int unsigned FIFO_DEPTH = 8,
  parameter int unsigned PWORD64_LEN = 64,
  parameter int unsigned PWORD32_LEN = 32,
  parameter int unsigned EL_DW = 16,
  parameter int unsigned EL8_DW = 8,
  parameter int unsigned AW = 36,
  parameter int unsigned DW = (PWORD32_LEN * EL_DW),
  parameter int unsigned RD_RESP_DEPTH = 2
) (
  input wire i_clk,
  input wire i_rst_n,

  // DPcmd:
  input  logic [       AW-1:0] dpc_addr,
  input  logic                 dpc_pad,
  input  logic [PWORD64_LEN-1:0] dpc_msk,
  input  logic                 dpc_format,
  input  logic                 dpc_config,
  input  logic                 dpc_last,
  input  logic                 dpc_vld,
  output logic                 dpc_rdy,
  // part of command, but should only be set once per iteration (until last):
  input  logic [    EL_DW-1:0] dpc_pad_val,
  input  logic [    EL_DW-1:0] dpc_intra_pad_val,

  // MMIO:
  // req:
  output logic [AW-1:0] mm_addr,
  output logic          mm_valid,
  input  logic          mm_ready,

  // resp:
  input logic [DW-1:0] mm_rdata,
  input logic          mm_ack,
  output logic         mm_resp_ready,

  //AXIS:
  output logic              axis_m_valid,
  input  logic              axis_m_ready,
  output logic [    DW-1:0] axis_m_data,
  output logic              axis_m_last,

  // status and opt config
  output logic last_rcvd,

  // Error conditions
  output logic o_err_illegal_data_conv,

  // State observation
  output ifd_csr_reg_pkg::ifd_csr_hw2reg_dp_status_reg_t dp_status
);

  import ifd_odr_pkg::*;

  localparam int unsigned ReqFifoDw = PWORD64_LEN + 4 + 2*EL_DW;

  logic                   rd_fifo_rreq;
  logic [         DW-1:0] rd_fifo_rdata;
  logic                   rd_fifo_rempty;
  logic                   rd_fifo_full;

  logic [         DW-1:0] axis_m_data_sel;

  logic                   req_fifo_rreq;
  logic [ReqFifoDw-1:0] req_fifo_rdata;
  logic                   req_fifo_rempty;
  logic                   req_fifo_wreq;
  logic [ReqFifoDw-1:0] req_fifo_wdata;
  logic                   req_fifo_wfull;

  logic [  PWORD64_LEN-1:0] req_q_msk;
  logic [  PWORD64_LEN-1:0] req_q_msk_mxd;
  logic                   req_q_pad;
  logic                   req_q_last;
  reg   [      EL_DW-1:0] req_q_pad_val;
  reg   [      EL_DW-1:0] req_q_intra_pad_val;
  logic                   rd_and_req_vld;

  logic                   last_snd;
  reg                     last_snd_q;

  logic                   req_q_format;
  logic                   req_q_config;

  state_cast_ifd_e        p_state, n_state;
  logic [DW-1 : 0]        rd_fifo_rdata_1sthalf_sign_ext;
  logic [DW-1 : 0]        rd_fifo_rdata_2ndhalf_sign_ext;
  logic [DW - 1 : 0]      pword32_intra_pad;

  // Casting error
  always_comb
    o_err_illegal_data_conv = dpc_vld && dpc_format && !dpc_config;

  // last_rcvd asserts for 1 cycle after sending out last item
  assign last_rcvd = last_snd_q;
  always_ff @(posedge i_clk, negedge i_rst_n) begin : last_reg
    if (i_rst_n == 'b0) begin
      last_snd_q <= 1'b0;
    end else begin
      if (last_snd_q | last_snd) last_snd_q <= last_snd;
    end
  end

  assign last_snd = axis_m_last && axis_m_ready && axis_m_valid;

  ////////////////////////////
  // Request gen:
  assign req_fifo_wdata = {dpc_format, dpc_config, dpc_intra_pad_val, dpc_pad_val, dpc_last, dpc_pad, dpc_msk};

  always_comb begin : req_gen
    mm_valid = 'b0;
    mm_addr = 'b0;  // default to 0, reduces toggling during padding

    req_fifo_wreq = 'b0;

    dpc_rdy = ~req_fifo_wfull;

    // there is a DPcmd and req fifo can accept:
    // Stall if illegal data conversion request comes
    if((dpc_vld == 1'b1) && (req_fifo_wfull == 1'b0) && !o_err_illegal_data_conv) begin
      if (dpc_pad == 1'b1) begin  // request requires padding
        req_fifo_wreq = 1'b1;
        dpc_rdy       = 1'b1;
      end else begin  // connect MMIO interface to DPcmd
        mm_valid = 1'b1;
        mm_addr  = dpc_addr;
        if (mm_ready == 1'b1) begin
          req_fifo_wreq = 1'b1;
          dpc_rdy       = 1'b1;
        end else dpc_rdy = 1'b0;
      end
    end
  end
  ////////////////////////////

  ////////////////////////////
  // Stream gen:
  // default assignements of the last from the request fifo
  assign {req_q_format, req_q_config, req_q_intra_pad_val, req_q_pad_val, req_q_last, req_q_pad, req_q_msk} = req_fifo_rdata;

  // Masking with intra pad val for each format and vector conditions
  //  Format    Vector    Casting     Masking
  //  ------    ------    -------     -------
  //    0         0       i8 -> i8    msk[63:0], each bit masks each byte of PWORD64 data.
  //                                  Only intra_pad_val[7:0] part to be used for masking in this mode.
  //    0         1       i8 -> i16   msk[63:32] => msk_upper[63:0], msk[31:0] => msk_lower[63:0]
  //                                  pword64i8 => {pword32i16_upper, pword32i16_lower}
  //                                  each consecutive 2 bits of msk_upper and msk_lower is the same
  //                                  e.g. msk_upper[0] == msk_upper[1] and msk_upper[2] == msk_upper[3]
  //                                  to be able to mask each element of pword32i16 byte by byte
  //                                  msk_upper[0] ? pword32i16_upper[7:0] : intra_pad_val[7:0] and
  //                                  msk_upper[1] ? pword32i16_upper[15:8] : intra_pad_val[15:8]
  //    1         1       i16->i16    Same approach with "01" but with no need to split msk as upper and lower
  //                                  because msk is already generated to have each consecutive 2 bits to be the same
  //                                  in the address generator block.
  //    1         0       IRQ needs to be raised in this condition!

  // Intra-word padding value concatenated 32 times to be used for muxing.
  assign pword32_intra_pad = {PWORD32_LEN{req_q_intra_pad_val}};

  always_comb begin
    for(int unsigned idx = 0; idx < PWORD64_LEN; idx++) begin
      if(req_q_msk_mxd[idx])
        // No intra-word padding
        axis_m_data[EL8_DW * idx +: EL8_DW] = axis_m_data_sel[EL8_DW * idx +: EL8_DW];
      else if(!req_q_config)
        // Intra-word padding with int8 format, lower half of intra pad val used.
        axis_m_data[EL8_DW * idx +: EL8_DW] = req_q_intra_pad_val[EL8_DW - 1 : 0];
      else
        // Intra-word padding with int16 format
        axis_m_data[EL8_DW * idx +: EL8_DW] = pword32_intra_pad[EL8_DW * idx +: EL8_DW];
    end
  end

  ////////////////////////////

  ////////////////////////////////////////////////////
  //      Int16 Casting FSM Implementation          //
  ////////////////////////////////////////////////////

  // FSM State Register
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if(!i_rst_n)
      p_state <= ST_PASSTH_IFD;
    else
      p_state <= n_state;
  end

  // FSM Next state
  always_comb begin
    n_state = ST_PASSTH_IFD;
    unique case(p_state)
      // No casting or lower half of casting condition
      ST_PASSTH_IFD : if((!req_q_format && req_q_config) &&
                        ((!req_fifo_rempty && req_q_pad) || rd_and_req_vld)
                        && axis_m_ready)
                        n_state = ST_CAST_IFD;
                      else
                          n_state = ST_PASSTH_IFD;
      // Upper half of the casting condition
      ST_CAST_IFD : if(axis_m_ready)
                          n_state = ST_PASSTH_IFD;
                        else
                          n_state = ST_CAST_IFD;
      default     : n_state = ST_PASSTH_IFD;
    endcase
  end

  // FSM Output logic
  always_comb begin
    axis_m_valid      = 1'b0;
    axis_m_data_sel   = '0;
    req_fifo_rreq     = 1'b0;
    rd_fifo_rreq      = 1'b0;
    axis_m_last       = 1'b0;
    req_q_msk_mxd     = req_q_msk;
    unique case(p_state)
      ST_PASSTH_IFD : begin
                        if(req_q_pad) begin
                            if(!req_q_config)
                              axis_m_data_sel = {PWORD64_LEN{req_q_pad_val[EL8_DW - 1 : 0]}};
                            else
                              axis_m_data_sel = {PWORD32_LEN{req_q_pad_val}};

                            if(!req_fifo_rempty)
                              if((!req_q_format && req_q_config)) begin
                                axis_m_valid  = 1'b1;
                                axis_m_last   = 1'b0;
                                req_q_msk_mxd = msk_conv(req_q_msk[PWORD32_LEN - 1 : 0]);
                              end
                              else begin
                                req_fifo_rreq = axis_m_ready;
                                axis_m_valid  = 1'b1;
                                axis_m_last   = req_q_last;
                              end
                        end
                        else begin
                          if(rd_and_req_vld )
                            if (!req_q_format && req_q_config) begin
                              axis_m_valid    = 1'b1;
                              axis_m_data_sel = rd_fifo_rdata_1sthalf_sign_ext;
                              axis_m_last     = 1'b0;
                              req_q_msk_mxd   = msk_conv(req_q_msk[PWORD32_LEN - 1 : 0]);
                            end
                            else begin
                              axis_m_valid    = 1'b1;
                              axis_m_data_sel = rd_fifo_rdata;
                              req_fifo_rreq   = axis_m_ready;
                              rd_fifo_rreq    = axis_m_ready;
                              axis_m_last     = req_q_last;
                            end
                        end
                      end
      ST_CAST_IFD   : begin
                        axis_m_last   = req_q_last;
                        req_q_msk_mxd = msk_conv(req_q_msk[PWORD64_LEN - 1 : PWORD32_LEN]);
                        if(req_q_pad) begin
                              axis_m_data_sel = {PWORD32_LEN{req_q_pad_val}};

                            if(!req_fifo_rempty) begin
                                req_fifo_rreq = axis_m_ready;
                                axis_m_valid  = 1'b1;
                            end
                        end
                        else begin
                          if(rd_and_req_vld) begin
                              axis_m_valid    = 1'b1;
                              axis_m_data_sel = rd_fifo_rdata_2ndhalf_sign_ext;
                              req_fifo_rreq   = axis_m_ready;
                              rd_fifo_rreq    = axis_m_ready;
                          end
                        end
                      end
      default       : begin
                        axis_m_valid      = 1'b0;
                        axis_m_data_sel   = '0;
                        req_fifo_rreq     = 1'b0;
                        rd_fifo_rreq      = 1'b0;
                        axis_m_last       = 1'b0;
                        req_q_msk_mxd     = req_q_msk;
                      end
    endcase
  end

  // Read and Request FIFOs are valid
  assign rd_and_req_vld = (~req_fifo_rempty) & (~rd_fifo_rempty);

  ////////////////////////////////////////////////////
  //      Int16 Casting Data Manipulation           //
  ////////////////////////////////////////////////////

    // Signed extend first half of the rd_fifo_rdata
    always_comb
        rd_fifo_rdata_1sthalf_sign_ext = cast_int16(rd_fifo_rdata[DW/2-1 : 0]);

    // Signed extend second half of the rd_fifo_rdata
    always_comb
        rd_fifo_rdata_2ndhalf_sign_ext = cast_int16(rd_fifo_rdata[DW-1 : DW/2]);

  ////////////////////////////
  // used FIFO's:
  sync_fifo #(
    .FIFO_DEPTH(RD_RESP_DEPTH),
    .data_t(logic[DW-1:0]),
    .MEM_MACRO_USE(0),
    .MEM_MACRO_TYPE(0),
    .ALMOST_EMPTY_THR(0),  // don't care
    .ALMOST_FULL_THR(1)  // don't care
  ) u_read_fifo (
    .i_clk (i_clk),
    .i_rst_n(i_rst_n),

    .rd_req_i(rd_fifo_rreq),
    .rd_data_o(rd_fifo_rdata),
    .empty_o(rd_fifo_rempty),
    .almost_empty_o(), // ASO-UNUSED_OUTPUT: not used

    .wr_req_i(mm_ack & ~rd_fifo_full),
    .wr_data_i(mm_rdata),
    .full_o(rd_fifo_full),
    .almost_full_o()  // ASO-UNUSED_OUTPUT: not used
  );
  always_comb mm_resp_ready = ~rd_fifo_full;

  sync_fifo #(
    .FIFO_DEPTH(FIFO_DEPTH),
    .data_t(logic[ReqFifoDw-1:0]),
    .MEM_MACRO_USE(0),
    .MEM_MACRO_TYPE(0),
    .ALMOST_EMPTY_THR(0),  // don't care
    .ALMOST_FULL_THR(1)  // don't care
  ) u_req_fifo (
    .i_clk (i_clk),
    .i_rst_n(i_rst_n),

    .rd_req_i(req_fifo_rreq),
    .rd_data_o(req_fifo_rdata),
    .empty_o(req_fifo_rempty),
    .almost_empty_o(), // ASO-UNUSED_OUTPUT: not used

    .wr_req_i(req_fifo_wreq),
    .wr_data_i(req_fifo_wdata),
    .full_o(req_fifo_wfull),
    .almost_full_o()  // ASO-UNUSED_OUTPUT: not used
  );
  ////////////////////////////

  ////////////////////////////
  // State observation
  assign dp_status = '{
          out_vld: '{d: axis_m_valid},
          out_rdy: '{d: axis_m_ready},
          out_lst: '{d: axis_m_last},
          out_stl: '{d: axis_m_valid & ~axis_m_ready},
          dpcmd0_vld: '{d: dpc_vld},
          dpcmd0_rdy: '{d: dpc_rdy},
          dpcmd0_lst: '{d: dpc_last},
          dpcmd0_stl: '{d: dpc_rdy & ~dpc_vld},
          mm_req_vld: '{d: mm_valid},
          mm_req_rdy: '{d: mm_ready},
          mm_resp_ack: '{d: mm_ack},
          default: '0
      };
  ////////////////////////////

endmodule

`endif  // _IFD_DP_SV_
