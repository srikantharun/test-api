// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of ODR data path
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _ODR_DP_SV_
`define _ODR_DP_SV_

module odr_dp #(
  parameter int unsigned FIFO_DEPTH = 8,
  parameter int unsigned WR_BUF_DEPTH = 2,
  parameter int unsigned PWORD64_LEN = 64,
  parameter int unsigned PWORD32_LEN = 32,
  parameter int unsigned EL_DW = 16,
  parameter int unsigned EL8_DW = 8,
  parameter int unsigned AW = 36,
  parameter int unsigned DW = (PWORD32_LEN * EL_DW)
) (
  input wire i_clk,
  input wire i_rst_n,

  // DPcmd:
  input  logic [       AW-1:0] dpc_addr,
  input  logic                 dpc_drop,
  input  logic [    EL_DW-1:0] dpc_drop_val, // ASO-UNUSED_INPUT: drop_val is not used, intra_drop_val only
  input  logic [    EL_DW-1:0] dpc_intra_drop_val,
  input  logic [PWORD64_LEN-1:0] dpc_msk,
  input  logic                 dpc_format,
  input  logic                 dpc_config,
  input  logic                 dpc_last,
  input  logic                 dpc_vld,
  output logic                 dpc_rdy,

  // MMIO:
  // req:
  output logic [AW-1:0] mm_addr,
  output logic [DW-1:0] mm_wdata,
  output logic          mm_valid,
  input  logic          mm_ready,

  // resp:
  input logic          mm_ack,
  output logic         mm_resp_ready,

  //AXIS:
  input  logic              axis_s_valid,
  output logic              axis_s_ready,
  input  logic [    DW-1:0] axis_s_data,
  input  logic              axis_s_last,

  // status and errors
  output logic last_written,
  output logic err_unexp_last_low,
  output logic err_unexp_last_high,
  output logic o_err_illegal_data_conv,
  output logic o_err_odd_num_int8_casting,

  // State observation
  output odr_csr_reg_pkg::odr_csr_hw2reg_dp_status_reg_t dp_status
);

  import ifd_odr_pkg::*;

  localparam int unsigned ReqFifoDw = 2;

  logic                   wr_fifo_rreq;
  logic                   wr_fifo_rreq_int;
  logic [         DW-1:0] wr_fifo_rdata;
  logic                   wr_fifo_rempty;
  logic                   wr_fifo_full;

  logic                   req_fifo_rreq;
  logic [ReqFifoDw-1:0]  req_fifo_rdata;
  logic                   req_fifo_rempty;
  logic                   req_fifo_wreq;
  logic                   req_fifo_wreq_int;
  logic [ReqFifoDw-1:0]  req_fifo_wdata;
  logic                   req_fifo_wfull;

  logic                   resp_fifo_rreq;
  logic                   resp_fifo_rempty;
  logic                   resp_fifo_full;

  logic                   req_q_drop;
  logic                   req_q_last;

  logic [     (DW/8)-1:0] ext_mask;
  logic [     (DW/8)-1:0] int_mask;

  logic                   wr_fifo_last;
  logic [         DW-1:0] wr_fifo_wdata;

  logic                   last_wr_resp;
  reg                     last_wr_resp_q;

  // Int8 casting implementation signals.
  state_cast_odr_e        p_state, n_state;
  logic [DW-1:0]          mm_wdata_int;
  logic                   mm_valid_int;
  logic                   en_store_for_cast;
  half_pword64i8_t        half_pw64i8, lower_half_pw64i8_q;
  pword64i8_t             casted_pw64i8;
  logic                   dpc_rdy_int;
  logic [DW-1:0]          pword32_intra_drop;
  logic [PWORD64_LEN-1:0] dpc_msk_int;

  // last_rcvd asserts for 1 cycle after receiving last item wresp
  assign {req_q_last, req_q_drop} = req_fifo_rdata;
  assign last_wr_resp = req_q_last & req_fifo_rreq;

  assign last_written = last_wr_resp_q;
  always_ff @(posedge i_clk, negedge i_rst_n) begin : last_reg
    if (i_rst_n == 'b0) begin
      last_wr_resp_q <= 1'b0;
    end else begin
      if (last_wr_resp_q | last_wr_resp) last_wr_resp_q <= last_wr_resp;
    end
  end

  ////////////////////////////
  // Request gen:
  assign req_fifo_wdata = {dpc_last, dpc_drop};

  always_comb begin : req_gen
    mm_valid_int  = 'b0;
    mm_addr       = '0;  // default to 0, reduces toggling during dropping

    req_fifo_wreq_int = 1'b0;
    wr_fifo_rreq_int  = 1'b0;

    dpc_rdy_int = ~wr_fifo_rempty;

    // there is a DPcmd, and there is write data
    // Stall if illegal data conversion request comes
    if ((dpc_vld == 1'b1) && (wr_fifo_rempty == 1'b0) && !o_err_illegal_data_conv) begin
      if (dpc_drop == 1'b1) begin  // request requires dropping
        // if last item, put in req fifo to make sure last will be flagged:
        if(dpc_last == 1'b1) begin
          if (req_fifo_wfull == 1'b0) begin  // but can only be done when fifo is not full
            req_fifo_wreq_int = 1'b1;
            wr_fifo_rreq_int  = 1'b1;
            dpc_rdy_int       = 1'b1;
          end else begin
            dpc_rdy_int = 1'b0;
          end
        end else begin
          wr_fifo_rreq_int  = 1'b1;
          dpc_rdy_int       = 1'b1;
        end
      end else if (req_fifo_wfull == 1'b0) begin  // connect MMIO interface, if req FIFO is not full
        mm_valid_int  = 1'b1;
        mm_addr       = dpc_addr;
        if (mm_ready == 1'b1) begin
          req_fifo_wreq_int = 1'b1;
          wr_fifo_rreq_int  = 1'b1;
          dpc_rdy_int       = 1'b1;
        end else dpc_rdy_int = 1'b0;
      end
    end
  end
  ////////////////////////////

  ////////////////////////////
  // Stream gen:
  // accept AXI stream slave until fifo is full
  assign axis_s_ready   = ~wr_fifo_full;
  // accept response FIFO when there is something in the req fifo and it's not drop:
  assign resp_fifo_rreq = (~req_fifo_rempty) & (~req_q_drop) & (~resp_fifo_rempty);
  // accept request fifo when there is something in the response FIFO,
  // or when the request is last and dropped:
  assign req_fifo_rreq  = (~resp_fifo_rempty) | (req_q_last & req_q_drop & (~req_fifo_rempty));

  // Intra-word drop value concatenated 32 times to be used for muxing.
  assign pword32_intra_drop = {PWORD32_LEN{dpc_intra_drop_val}};

  always_comb begin
    for(int unsigned idx = 0; idx < PWORD64_LEN; idx++) begin
      if(dpc_msk_int[idx])
        // No intra-word drop
        mm_wdata_int[EL8_DW * idx +: EL8_DW] = wr_fifo_rdata[EL8_DW * idx +: EL8_DW];
      else if(!dpc_config)
        // Intra-word drop with int8 format, lower half of intra drop val used.
        mm_wdata_int[EL8_DW * idx +: EL8_DW] = dpc_intra_drop_val[EL8_DW - 1 : 0];
      else
        // Intra-word drop with int16 format
        mm_wdata_int[EL8_DW * idx +: EL8_DW] = pword32_intra_drop[EL8_DW * idx +: EL8_DW];
    end
  end


  ////////////////////////////

  ////////////////////////////
  // error checking:
  assign err_unexp_last_high = wr_fifo_last & (~dpc_last) & wr_fifo_rreq;
  assign err_unexp_last_low = (~wr_fifo_last) & (dpc_last && !en_store_for_cast) & wr_fifo_rreq;

  ////////////////////////////

  ////////////////////////////////////////////////////
  //        Int16 Casting Implementation            //
  ////////////////////////////////////////////////////

  // Casting error
  always_comb
    o_err_illegal_data_conv = dpc_vld && !dpc_config && dpc_format;

  // FSM State Register
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if(!i_rst_n)
      p_state <= ST_PASSTH_ODR;
    else
      p_state <= n_state;
  end

  // FSM Next state
  always_comb begin
    n_state = ST_PASSTH_ODR;
    unique case(p_state)
      // No casting or collect lower half of pword64
      ST_PASSTH_ODR : if((dpc_vld && (dpc_config && !dpc_format)) &&
                          (!wr_fifo_rempty && !req_fifo_wfull) && !wr_fifo_last)
                        n_state = ST_CAST_ODR;
                      else
                        n_state = ST_PASSTH_ODR;
      // Collect the upper half of pword64 and send
      // No need to wait mm_ready if data needs to be dropped.
      ST_CAST_ODR   : if(mm_ready || dpc_drop)
                        n_state = ST_PASSTH_ODR;
                      else
                        n_state = ST_CAST_ODR;
      default       : n_state = ST_PASSTH_ODR;
    endcase
  end

  // FSM Output logic
  always_comb begin
    en_store_for_cast           = 1'b0;
    mm_valid                    = 1'b0;
    mm_wdata                    = mm_wdata_int;
    dpc_rdy                     = dpc_rdy_int;
    req_fifo_wreq               = req_fifo_wreq_int;
    o_err_odd_num_int8_casting  = 1'b0;
    wr_fifo_rreq                = wr_fifo_rreq_int;
    dpc_msk_int                 = dpc_msk;

    unique case(p_state)
      ST_PASSTH_ODR : begin
                        if((dpc_vld && (dpc_config && !dpc_format)) &&
                           (!wr_fifo_rempty && !req_fifo_wfull)) begin
                          en_store_for_cast           = 1'b1;
                          dpc_rdy                     = 1'b0;
                          req_fifo_wreq               = 1'b0;
                          o_err_odd_num_int8_casting  = wr_fifo_last;
                          wr_fifo_rreq                = 1'b1;
                          dpc_msk_int                 = msk_conv(dpc_msk[PWORD32_LEN - 1 : 0]);
                        end
                        else begin
                          mm_valid      = mm_valid_int;
                          dpc_rdy       = dpc_rdy_int;
                          req_fifo_wreq = req_fifo_wreq_int;
                        end
                      end
      ST_CAST_ODR   : begin
                        if(dpc_drop)
                          mm_valid      = 1'b0;
                        else
                          mm_valid      = mm_valid_int;

                        dpc_msk_int   = msk_conv(dpc_msk[PWORD64_LEN - 1 : PWORD32_LEN]);
                        mm_wdata      = casted_pw64i8;
                        dpc_rdy       = dpc_rdy_int;
                        req_fifo_wreq = req_fifo_wreq_int;
                      end
      default       : begin
                        en_store_for_cast           = 1'b0;
                        mm_valid                    = 1'b0;
                        mm_wdata                    = mm_wdata_int;
                        dpc_rdy                     = dpc_rdy_int;
                        req_fifo_wreq               = req_fifo_wreq_int;
                        o_err_odd_num_int8_casting  = 1'b0;
                        wr_fifo_rreq                = wr_fifo_rreq_int;
                      end
    endcase
  end

  // Data storing and casting operation
  always_ff @(posedge i_clk, negedge i_rst_n)
  begin
      if(!i_rst_n)
          lower_half_pw64i8_q  <= '0;
      else if (en_store_for_cast)
          lower_half_pw64i8_q  <= half_pw64i8;
  end

  always_comb begin
    half_pw64i8   = cast_int8(mm_wdata_int);
    casted_pw64i8 = {half_pw64i8, lower_half_pw64i8_q};
  end

  ////////////////////////////
  // used FIFO's:
  if (WR_BUF_DEPTH > 0) begin: g_wr_buf
    sync_fifo #(
      .FIFO_DEPTH(WR_BUF_DEPTH),
      .data_t(logic[DW + 1-1:0]),
      .MEM_MACRO_USE(0),
      .MEM_MACRO_TYPE(0),
      .ALMOST_EMPTY_THR(0),  // don't care
      .ALMOST_FULL_THR(0)  // don't care
    ) u_wr_buf_fifo (
      .i_clk (i_clk),
      .i_rst_n(i_rst_n),

      .rd_req_i(wr_fifo_rreq),
      .rd_data_o({wr_fifo_last, wr_fifo_rdata}),
      .empty_o(wr_fifo_rempty),
      .almost_empty_o(), // ASO-UNUSED_OUTPUT: not used

      .wr_req_i(axis_s_valid),
      .wr_data_i({axis_s_last, axis_s_data}),
      .full_o(wr_fifo_full),
      .almost_full_o()  // ASO-UNUSED_OUTPUT: not used
    );
    // disable FIFO assertions as they are not wanted:
    // normal to have rd_req high while empty, for example
    // don't care bout almost_*_thr settings as not used
`ifdef ASSERTIONS_ON
    initial begin
      $assertkill(0, u_wr_buf_fifo);
    end
`endif
  end else begin : g_no_wr_buf
    assign wr_fifo_rempty = ~axis_s_valid;
    assign wr_fifo_full = ~wr_fifo_rreq;
    assign {wr_fifo_last, wr_fifo_rdata} = {axis_s_last, axis_s_data};
  end

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
    .almost_full_o() // ASO-UNUSED_OUTPUT: not used
  );

  sync_fifo #(
    .FIFO_DEPTH(2),
    .data_t(logic),
    .MEM_MACRO_USE(0),
    .MEM_MACRO_TYPE(0),
    .ALMOST_EMPTY_THR(0),  // don't care
    .ALMOST_FULL_THR(1)  // don't care
  ) u_wr_resp_fifo (
    .i_clk (i_clk),
    .i_rst_n(i_rst_n),

    .rd_req_i(resp_fifo_rreq),
    .rd_data_o(), // ASO-UNUSED_OUTPUT: not used
    .empty_o(resp_fifo_rempty),
    .almost_empty_o(), // ASO-UNUSED_OUTPUT: not used

    .wr_req_i(mm_ack & ~resp_fifo_full),
    .wr_data_i(1'b0),
    .full_o(resp_fifo_full),
    .almost_full_o() // ASO-UNUSED_OUTPUT: not used
  );
  always_comb mm_resp_ready = ~resp_fifo_full;
  ////////////////////////////

  ////////////////////////////
  // State observation

  // Input stream is stalled if we SHALL read data (and are not backpressured) but there is no data.
  // We cannot know if the non-present command would drop, we err on the side of false-positives.
  // We cannot know if the MMIO interface would stall, we err on the side of false-positives.
  logic in_stream_stalled;
  assign in_stream_stalled = dpc_vld & wr_fifo_rempty & (dpc_drop & ~dpc_last | ~req_fifo_wfull);

  assign dp_status = '{
          in0_vld: '{d: ~wr_fifo_rempty},
          in0_rdy: '{d: wr_fifo_rreq},
          in0_lst: '{d: wr_fifo_last},
          in0_stl: '{d: in_stream_stalled},
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

`endif  // _ODR_DP_SV_
