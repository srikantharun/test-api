// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA
// Owner: Matt Morris <matt.morris@axelera.ai>


module dma_axi_wr_port_mux
  import dma_pkg::*;
  import axi_pkg::*;
  import dma_mmu_reg_pkg::*;
#(
    parameter int unsigned NUM_CHNLS = 4,
    parameter type dma_axi_data_t  = logic [511-1:0],
    parameter type dma_axi_strb_t  = logic [ 63-1:0],
    parameter type dma_axi_addr_t  = logic [ 35-1:0],
    parameter type dma_axi_id_t    = logic [  3-1:0]
)
(
    input  wire                  i_clk,
    input  wire                  i_rst_n,

    input  logic [NUM_CHNLS-1:0] i_xfer_req,
    output logic [NUM_CHNLS-1:0] o_xfer_gnt,
    input  dma_wr_xfer_t         i_xfer      [NUM_CHNLS],

    output logic [NUM_CHNLS-1:0] o_resp_req,
    input  logic [NUM_CHNLS-1:0] i_resp_gnt,
    output dma_wr_resp_t         o_resp,

    output logic           o_axi_m_awvalid,
    output dma_axi_addr_t  o_axi_m_awaddr,
    output dma_axi_id_t    o_axi_m_awid,
    output axi_len_t       o_axi_m_awlen,
    output axi_size_e      o_axi_m_awsize,
    output axi_burst_e     o_axi_m_awburst,
    output logic           o_axi_m_awlock,
    output axi_cache_e     o_axi_m_awcache,
    output axi_prot_t      o_axi_m_awprot,
    input  logic           i_axi_m_awready,

    output logic           o_axi_m_wvalid,
    output logic           o_axi_m_wlast,
    output dma_axi_data_t  o_axi_m_wdata,
    output dma_axi_strb_t  o_axi_m_wstrb,
    input  logic           i_axi_m_wready,

    input  logic           i_axi_m_bvalid,
    input  dma_axi_id_t    i_axi_m_bid,
    input  axi_resp_e      i_axi_m_bresp,
    output logic           o_axi_m_bready
);

typedef logic [$clog2(NUM_CHNLS)-1:0] chnl_idx_t;
typedef logic [NUM_CHNLS-1:0] chnl_onehot_t;

chnl_idx_t arb_idx;
logic      arb_val;
dma_wr_xfer_t xfer;
logic          pop;
logic          aw_ack_q;
logic          w_ack_q;
logic          ready;
logic          valid;



dma_port_arb #( .N_REQ (NUM_CHNLS))
u_arb
(
  .i_clk,
  .i_rst_n,
  .i_req (i_xfer_req),
  .o_gnt (o_xfer_gnt),
  .i_last(xfer.last),
  .o_val (arb_val),
  .o_idx (arb_idx),
  .i_ack (arb_gnt)
);

  always_comb xfer = i_xfer[arb_idx];

typedef struct packed {
  chnl_idx_t chnl;
  dma_wr_xfer_t xfer;
} dma_axi_wr_req_t;

dma_axi_wr_req_t axi_xfer;
dma_axi_wr_req_t xfer_to_axi;

always_comb begin
  axi_xfer = '{ chnl : arb_idx,
                xfer : xfer };
end

cc_stream_spill_reg #(
  .data_t    ( dma_axi_wr_req_t ),
  .Bypass    ( 1'b0 ),
  .CutFirst  ( 1'b1 )
) u_req_retime (
  /// Clock, positive edge triggered
  .i_clk,
  // doc async
  /// Asynchronous reset, active low
  .i_rst_n,
  // doc sync i_clk
  /// Synchronously flush the registers
  .i_flush (1'b0 ),
  /// Input stream payload data
  .i_data  (axi_xfer),
  /// Input stream is valid
  .i_valid (arb_val),
  /// Input stream is ready
  .o_ready (arb_gnt),
  /// Output stream payload data
  .o_data  (xfer_to_axi),
  /// Output stream payload is valid
  .o_valid (valid),
  /// Ouptu stream is ready
  .i_ready (ready)
);

always_comb pop = valid & ready;
logic valid_dly_q;
always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    aw_ack_q <= 1'b0;
    w_ack_q  <= 1'b0;
    valid_dly_q <= 1'b0;
  end
  else begin
    valid_dly_q <= valid;
    if (o_axi_m_awvalid && i_axi_m_awready) begin
      aw_ack_q <= o_axi_m_wvalid && !i_axi_m_wready;
    end
    else if (i_axi_m_wready) begin
      aw_ack_q <= 1'b0;
    end
    if (o_axi_m_wvalid && i_axi_m_wready) begin
      w_ack_q <= o_axi_m_awvalid && !i_axi_m_awready;
    end
    else if (i_axi_m_awready) begin
      w_ack_q <= 1'b0;
    end
    //if (pop || !valid_dly_q) begin
      //if (xfer_to_axi.xfer.first)
        //aw_ack_q <= i_axi_m_awready;
      //else
        //aw_ack_q <= 1'b1;
      //w_ack_q <= i_axi_m_wready;
    //end
    //else begin
      //w_ack_q <= w_ack_q | i_axi_m_wready;
      //aw_ack_q <= aw_ack_q | i_axi_m_awready;
    //end
  end

  always_comb ready = &({w_ack_q,aw_ack_q} | {(!o_axi_m_wvalid || i_axi_m_wready), (!o_axi_m_awvalid || i_axi_m_awready)});



  always_comb o_axi_m_awvalid = valid && xfer_to_axi.xfer.first && !aw_ack_q;
  always_comb o_axi_m_awaddr  = xfer_to_axi.xfer.addr;
  always_comb o_axi_m_awburst = |xfer_to_axi.xfer.len ? BurstIncr : BurstFixed;
  always_comb o_axi_m_awcache = axi_cache_e'('0);
  always_comb o_axi_m_awid    = {xfer_to_axi.xfer.tid, xfer_to_axi.chnl};
  always_comb o_axi_m_awlen   = axi_len_t'(xfer_to_axi.xfer.len);
  always_comb o_axi_m_awlock  = '0;
  always_comb o_axi_m_awprot  = 'd2;
  always_comb o_axi_m_awsize  = axi_size_e'(xfer_to_axi.xfer.size);
  always_comb o_axi_m_wvalid  = valid && !w_ack_q;
  always_comb o_axi_m_wlast   = xfer_to_axi.xfer.last;
  always_comb o_axi_m_wdata   = xfer_to_axi.xfer.data;
  always_comb o_axi_m_wstrb   = xfer_to_axi.xfer.be;

typedef struct packed {
  chnl_idx_t chnl;
  dma_wr_resp_t resp;
} dma_axi_bresp_t;

dma_axi_bresp_t axi_resp;
dma_axi_bresp_t resp_data;
always_comb axi_resp = '{ chnl : chnl_idx_t'(i_axi_m_bid),
                          resp : '{ tid  : i_axi_m_bid >> $bits(chnl_idx_t) }};

cc_stream_spill_reg #(
  .data_t    ( dma_axi_bresp_t ),
  .Bypass    ( 1'b0 ),
  .CutFirst  ( 1'b1 )
) u_rsp_retime (
  /// Clock, positive edge triggered
  .i_clk,
  // doc async
  /// Asynchronous reset, active low
  .i_rst_n,
  // doc sync i_clk
  /// Synchronously flush the registers
  .i_flush (1'b0 ),
  /// Input stream payload data
  .i_data  (axi_resp),
  /// Input stream is valid
  .i_valid (i_axi_m_bvalid),
  /// Input stream is ready
  .o_ready (o_axi_m_bready),
  /// Output stream payload data
  .o_data  (resp_data),
  /// Output stream payload is valid
  .o_valid (resp_vld),
  /// Ouptu stream is ready
  .i_ready (i_resp_gnt[resp_data.chnl])
);


  always_comb o_resp = resp_data.resp;
  always_comb o_resp_req = chnl_onehot_t'(resp_vld) << resp_data.chnl;

  ////////////////
  // Assertions //
  ////////////////

  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON

  assert property (@(posedge i_clk) disable iff (!i_rst_n) (o_axi_m_awvalid && !i_axi_m_awready) |=> $stable({o_axi_m_awvalid,
                                                                                                              o_axi_m_awaddr,
                                                                                                              o_axi_m_awburst,
                                                                                                              o_axi_m_awcache,
                                                                                                              o_axi_m_awid,
                                                                                                              o_axi_m_awlen,
                                                                                                              o_axi_m_awlock,
                                                                                                              o_axi_m_awprot,
                                                                                                              o_axi_m_awsize}))
    else $error("AW channel is not stable when awvalid is high and awready is low");

  assert property (@(posedge i_clk) disable iff (!i_rst_n) (o_axi_m_wvalid && !i_axi_m_wready) |=> $stable({o_axi_m_wvalid,
                                                                                                            o_axi_m_wlast,
                                                                                                            o_axi_m_wdata,
                                                                                                            o_axi_m_wstrb}))
    else $error("W channel is not stable when wvalid is high and wready is low");

  `endif
  `endif

endmodule
