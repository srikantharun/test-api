// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L2 RAM. By default 4096 x 128 SRAM is used
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_RAM_SV
`define L2_RAM_SV

module l2_ram
import l2_pkg::*;
import l2_cfg_pkg::*;
  (
    // Clock signal
    input  wire                                             i_clk,
    input  wire                                             i_rst_n,
    // RAM interface signals
    input  l2_ram_req_t                                     i_ram_req,
    output l2_ram_rsp_t                                     o_ram_rsp,

    // SRAM configuration
    input  axe_tcl_sram_pkg::impl_inp_t [L2_NUM_SRAMS-1:0]  i_impl,
    output axe_tcl_sram_pkg::impl_oup_t [L2_NUM_SRAMS-1:0]  o_impl
  );
  // =====================================================
  // Local parameters
  // =====================================================

  // =====================================================
  // Type definition
  // =====================================================

  // =====================================================
  // Signal declarations
  // =====================================================
  // RAM interface
  l2_sram_req_t           [L2_NUM_SRAMS-1:0] sram_req;
  l2_sram_data_t          [L2_NUM_SRAMS-1:0] sram_rsp;
  // Read Request
  logic                                      rd_req_d;
  logic                                      rd_req_q;

  // =====================================================
  // RTL
  // =====================================================

  /// @
  /// Detecting when the output of the SRAM needs to be gated
  always_comb rd_req_d = i_ram_req.ce && !i_ram_req.ram.we;

  /// @detect_rd_req_seq_proc
  /// Signal used to gate the data output of RAM
  always_ff @( posedge i_clk, negedge i_rst_n ) begin : detect_rd_req_seq_proc
    if      (~i_rst_n)            rd_req_q <= 1'b0;
    else if (rd_req_q ^ rd_req_d) rd_req_q <= rd_req_d;
  end

  /// @unroll_ram_req_comb_proc
  /// Unroll ram request into sram
  always_comb begin : unroll_ram_req_comb_proc
    foreach (sram_req[sram]) begin
      sram_req[sram] = '{
        ce: i_ram_req.ce,
        sram: '{
          addr: i_ram_req.ram.addr      ,
          we:   i_ram_req.ram.we        ,
          wbe:  i_ram_req.ram.wbe[sram] ,
          data: i_ram_req.ram.data[sram]
        }
      };
    end
  end

  for(genvar sram = 0; sram < L2_NUM_SRAMS; sram++) begin : g_sram
  axe_tcl_ram_1rwp #(
    .NumWords(L2_SRAM_DATA_DEPTH),
    .DataWidth(L2_SRAM_DATA_WIDTH),
    .ByteWidth(8),
    .ReadLatency(1),
    .ImplKey("HS_RVT"),
    .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
    .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
  ) u_l2_ram_wrapper (
    .i_clk      (i_clk),
    .i_rst_n    (i_rst_n),
    .i_impl     (i_impl[sram]),
    .o_impl     (o_impl[sram]),
    .i_req      (sram_req[sram].ce),
    .i_wr_enable(sram_req[sram].sram.we),
    .i_addr     (sram_req[sram].sram.addr),
    .i_wr_data  (sram_req[sram].sram.data),
    .i_wr_mask  (sram_req[sram].sram.wbe),
    .o_rd_data  (sram_rsp[sram])
  );
  end

  /// @gate_out_data_comb_proc
  /// Clean ram output data if no read request
  always_comb begin : gate_out_data_comb_proc
    o_ram_rsp = '{
                  data: rd_req_q ? sram_rsp : '0
                 ,valid: rd_req_q
                 };
  end

endmodule

`endif  // L2_RAM_SV
