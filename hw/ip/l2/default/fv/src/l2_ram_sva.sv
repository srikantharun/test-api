// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: SVA of l2 ram
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_RAM_SVA_SV
`define L2_RAM_SVA_SV

module l2_ram_sva
  import l2_pkg::*;
  import l2_cfg_pkg::*;
  (
    // Clock signal
    input wire         i_clk,
    input wire         i_rst_n,
    // RAM interface signals
    input l2_ram_req_t i_ram_req,
    input l2_ram_rsp_t o_ram_rsp
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

  // =====================================================
  // Bind signals
  // =====================================================

  // =====================================================
  // Properties
  // =====================================================

  property p_read_req(bit tc_sram_req, bit tc_sram_we);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_ram_req.ce && !i_ram_req.ram.we)
        |-> (tc_sram_req && (tc_sram_we == 1'b0))
      );
  endproperty

  property p_read_data(int unsigned sram, l2_sram_data_t tc_sram_rdata);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_ram_req.ce && !i_ram_req.ram.we)
        |=> ((o_ram_rsp.data[sram] == tc_sram_rdata) && o_ram_rsp.valid == 1'b1)
      );
  endproperty

  property p_no_read_req_zero_data(int unsigned sram);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        !(i_ram_req.ce && !i_ram_req.ram.we)
        |=> (o_ram_rsp.data[sram] == '0)
      );
  endproperty

  property p_write_req(int unsigned sram, bit tc_sram_req, bit tc_sram_we);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_ram_req.ce && i_ram_req.ram.we && |i_ram_req.ram.wbe[sram])
        |-> (tc_sram_req && (tc_sram_we == 1'b1))
      );
  endproperty

  property p_write_data(int unsigned sram, l2_sram_data_t tc_sram_wdata);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_ram_req.ce && i_ram_req.ram.we)
        |-> (i_ram_req.ram.data[sram] == tc_sram_wdata)
      );
  endproperty

  property p_write_byte_en(int unsigned sram, l2_sram_strb_t tc_sram_wbe);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_ram_req.ce && i_ram_req.ram.we)
        |-> (i_ram_req.ram.wbe[sram] == tc_sram_wbe)
      );
  endproperty

  property p_pde_prn(bit pde, bit prn);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        ##1 (prn == $past(pde))
      );
  endproperty

  // =====================================================
  // Assumes
  // =====================================================

  for (genvar sram = 0; sram < L2_NUM_SRAMS; sram++) begin : g_sram_asp
    asp_pde_prn : assume property (p_pde_prn(l2_ram.g_sram[sram].u_l2_ram_wrapper.i_impl.pde, l2_ram.g_sram[sram].u_l2_ram_wrapper.o_impl.prn));
  end

  // =====================================================
  // Assertions
  // =====================================================

  for (genvar sram = 0; sram < L2_NUM_SRAMS; sram++) begin : g_sram
    ap_read_req      : assert property (p_read_req(l2_ram.g_sram[sram].u_l2_ram_wrapper.i_req, l2_ram.g_sram[sram].u_l2_ram_wrapper.i_wr_enable));
    ap_read_data     : assert property (p_read_data(sram, l2_ram.g_sram[sram].u_l2_ram_wrapper.o_rd_data));
    ap_read_tied_data: assert property (p_no_read_req_zero_data(sram));
    ap_write_req     : assert property (p_write_req(sram, l2_ram.g_sram[sram].u_l2_ram_wrapper.i_req, l2_ram.g_sram[sram].u_l2_ram_wrapper.i_wr_enable));
    ap_write_data    : assert property (p_write_data(sram, l2_ram.g_sram[sram].u_l2_ram_wrapper.i_wr_data));
    ap_write_byte_en : assert property (p_write_byte_en(sram, l2_ram.g_sram[sram].u_l2_ram_wrapper.i_wr_mask));
  end

  // =====================================================
  // Covers
  // =====================================================

endmodule

`endif  // L2_RAM_SVA_SV
