// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

module axe_apb_demux_sva #(
  // numbe of APB masters
  parameter int  unsigned NB_APBOUT         = 3,
  // width definition for APB address bus
  parameter int  unsigned PAW               = 16,
  // width definition for APB data bus
  parameter int  unsigned PDW               = 32,
  // width definition for APB strobe bus
  parameter int  unsigned PSTRBW            = 4,
  // width definition for APB subordinate index
  parameter int  unsigned IDXW              = 2,
  // index of the default subordinate (0 to NB_APBOUT-1)
  parameter int  unsigned DEFAULT_SUB_IDX   = 2,
  // APB types
  parameter type  paddr_t                   = logic [PAW       -1:0],
  parameter type  pdata_t                   = logic [PDW       -1:0],
  parameter type  pstrb_t                   = logic [PSTRBW    -1:0],
  parameter type  idx_t                     = logic [IDXW      -1:0]
)(
  // Clock, positive edge triggered
  input  wire                         i_clk,
  // Asynchronous reset, active low
  input  wire                         i_rst_n,
  // APB subordinate interface (input interface)
  input  paddr_t                      i_apb_s_paddr,
  input  pdata_t                      i_apb_s_pwdata,
  input  logic                        i_apb_s_pwrite,
  input  logic                        i_apb_s_psel,
  input  logic                        i_apb_s_penable,
  input  pstrb_t                      i_apb_s_pstrb,
  input  axe_apb_pkg::apb_prot_t      i_apb_s_pprot,
  // APB master interfaces (output interfaces)
  input  logic                        i_apb_m_pready[NB_APBOUT],
  input  pdata_t                      i_apb_m_prdata[NB_APBOUT],
  input  logic                        i_apb_m_pslverr[NB_APBOUT],
  // Selected subordinate from address decoder
  input  idx_t                        i_sub_idx_from_dec
);

  assume_decoder_idx_stable : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    $stable(i_apb_s_paddr) |-> $stable(i_sub_idx_from_dec)
  );

endmodule
