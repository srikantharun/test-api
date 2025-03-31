// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA
// Owner: Matt Morris <matt.morris@axelera.ai>


module dma_axi_rd_port_mux
  import dma_pkg::*;
  import axi_pkg::*;
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
    input  dma_rd_xfer_t         i_xfer      [NUM_CHNLS],

    output logic [NUM_CHNLS-1:0] o_resp_req,
    input  logic [NUM_CHNLS-1:0] i_resp_gnt,
    output dma_rd_resp_t         o_resp,

    output logic           o_axi_m_arvalid,
    output dma_axi_addr_t  o_axi_m_araddr,
    output dma_axi_id_t    o_axi_m_arid,
    output axi_len_t       o_axi_m_arlen,
    output axi_size_e      o_axi_m_arsize,
    output axi_burst_e     o_axi_m_arburst,
    output logic           o_axi_m_arlock,
    output axi_cache_e     o_axi_m_arcache,
    output axi_prot_t      o_axi_m_arprot,
    input  logic           i_axi_m_arready,

    input  logic           i_axi_m_rvalid,
    input  logic           i_axi_m_rlast,
    input  dma_axi_id_t    i_axi_m_rid,
    input  dma_axi_data_t  i_axi_m_rdata,
    input  axi_resp_e      i_axi_m_rresp,
    output logic           o_axi_m_rready

);

dma_rd_xfer_t xfer_q;
logic         xfer_val_q;
dma_axi_data_t rdata_q;
dma_axi_id_t   rid_q;
logic          rdata_val_q;
typedef logic [$clog2(NUM_CHNLS)-1:0] chnl_idx_t;
typedef logic [NUM_CHNLS-1:0] chnl_onehot_t;

chnl_idx_t arb_idx;
logic      arb_val;
dma_rd_xfer_t xfer;

dma_port_arb #( .N_REQ (NUM_CHNLS))
u_arb
(
  .i_clk,
  .i_rst_n,
  .i_req (i_xfer_req),
  .o_gnt (o_xfer_gnt),
  .i_last(1'b1),
  .o_val (arb_val),
  .o_idx (arb_idx),
  .i_ack (arb_gnt)
);


always_comb xfer = i_xfer[arb_idx];
typedef struct packed {
  chnl_idx_t chnl;
  dma_rd_xfer_t xfer;
} dma_axi_rd_req_t;

dma_axi_rd_req_t axi_xfer;
dma_axi_rd_req_t xfer_to_axi;

always_comb begin
  axi_xfer = '{ chnl : arb_idx,
                       xfer : xfer };
end

cc_stream_spill_reg #(
  .data_t    ( dma_axi_rd_req_t ),
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
  .o_valid (o_axi_m_arvalid),
  /// Ouptu stream is ready
  .i_ready (i_axi_m_arready)
);

always_comb o_axi_m_araddr  = xfer_to_axi.xfer.addr;
always_comb o_axi_m_arburst = |xfer_to_axi.xfer.len ? BurstIncr : BurstFixed;
always_comb o_axi_m_arcache = axi_cache_e'('0);
always_comb o_axi_m_arid    = {xfer_to_axi.xfer.tid, xfer_to_axi.chnl};
always_comb o_axi_m_arlen   = axi_len_t'(xfer_to_axi.xfer.len);
always_comb o_axi_m_arlock  = '0;
always_comb o_axi_m_arprot  = 'd2;
always_comb o_axi_m_arsize  = axi_size_e'(xfer_to_axi.xfer.size);

typedef struct packed {
  chnl_idx_t chnl;
  dma_rd_resp_t resp;
} dma_axi_resp_t;

dma_axi_resp_t axi_resp;
dma_axi_resp_t resp_data;
always_comb axi_resp = '{ chnl : chnl_idx_t'(i_axi_m_rid),
                          resp : '{ tid  : i_axi_m_rid >> $bits(chnl_idx_t),
                                    data : i_axi_m_rdata,
                                    last : i_axi_m_rlast }};
cc_stream_spill_reg #(
  .data_t    ( dma_axi_resp_t ),
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
  .i_valid (i_axi_m_rvalid),
  /// Input stream is ready
  .o_ready (o_axi_m_rready),
  /// Output stream payload data
  .o_data  (resp_data),
  /// Output stream payload is valid
  .o_valid (resp_vld),
  /// Ouptu stream is ready
  .i_ready (i_resp_gnt[resp_data.chnl])
);


  always_comb o_resp = resp_data.resp;
  always_comb o_resp_req = chnl_onehot_t'(resp_vld) << resp_data.chnl;

endmodule
