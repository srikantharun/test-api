// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: SVA of l2 mem
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_MEM_SVA_SV
`define L2_MEM_SVA_SV

module l2_mem_sva
  import l2_pkg::*;
  import l2_cfg_pkg::*;
  (
  // Clock and reset signals
  input wire         i_clk,
  input wire         i_rst_n,
  // RAM interface signals
  input l2_mem_req_t i_mem_req,
  input logic        o_mem_rd_ready,
  input logic        o_mem_wr_ready,
  input l2_mem_rsp_t o_mem_rsp

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
  logic [L2_NUM_BANKS-1:0][L2_NUM_RAMS-1:0] ram_rsp_valid;

  // =====================================================
  // Bind signals
  // =====================================================
  for (genvar bank = 0; bank < L2_NUM_BANKS; bank++) begin
    for (genvar ram = 0; ram < L2_NUM_RAMS; ram++) begin
      always_comb ram_rsp_valid[bank][ram] = l2_mem.g_bank[bank].u_l2_bank.ram_rsp[ram].valid;
    end
  end

  // =====================================================
  // Properties
  // =====================================================
  property p_read_one_rsp_valid;
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        ($onehot0(ram_rsp_valid))
      );
  endproperty

  property p_read_data_valid(l2_ram_rsp_t rsp);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (!rsp.valid) |-> (rsp.data == '0)
      );
  endproperty

  property p_stable_read;
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_mem_req.rd.en && !o_mem_rd_ready) |=> $stable(i_mem_req.rd)
      );
  endproperty

  property p_stable_write;
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_mem_req.wr.en && !o_mem_wr_ready) |=> $stable(i_mem_req.wr)
      );
  endproperty

  property p_no_req(bit l2_ram_ce, bit l2_ram_we, bit trigger);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (!i_mem_req.rd.en && !i_mem_req.wr.en && trigger)
        |-> ##L2_REQ_LATENCY !l2_ram_ce
      );
  endproperty

  property p_read_req(bit l2_ram_ce, bit l2_ram_we, bit trigger);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_mem_req.rd.en && o_mem_rd_ready && trigger)
        |-> ##L2_REQ_LATENCY l2_ram_ce && (l2_ram_we == 1'b0)
      );
  endproperty

  property p_read_data(l2_ram_rsp_t rsp);
    l2_sram_data_t [L2_NUM_SRAMS-1:0] data;
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (rsp.valid, data=rsp.data)
        |-> ##L2_RSP_LATENCY (data == o_mem_rsp.data)
      );
  endproperty

  property p_write_req(bit l2_ram_ce, bit l2_ram_we, bit trigger);
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (i_mem_req.wr.en && o_mem_wr_ready && trigger)
        |-> ##L2_REQ_LATENCY (l2_ram_ce && (l2_ram_we == 1'b1))
      );
  endproperty

  property p_write_data(bit l2_ram_ce, bit l2_ram_we, l2_sram_data_t [L2_NUM_SRAMS-1:0] l2_ram_wdata, bit trigger);
    l2_sram_data_t [L2_NUM_SRAMS-1:0] data;
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (((i_mem_req.wr.en && o_mem_wr_ready && trigger)), data=i_mem_req.wr.data)
        |-> ##L2_REQ_LATENCY (data == l2_ram_wdata)
      );
  endproperty

  property p_write_byte_en(bit l2_ram_ce, bit l2_ram_we, l2_sram_strb_t [L2_NUM_SRAMS-1:0] l2_ram_wbe, bit trigger);
    l2_sram_strb_t [L2_NUM_SRAMS-1:0] wbe;
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (((i_mem_req.wr.en && o_mem_wr_ready && trigger)), wbe=i_mem_req.wr.wbe)
        |-> ##L2_REQ_LATENCY (wbe == l2_ram_wbe)
      );
  endproperty

  property p_rd_starvation;
    @(posedge i_clk) disable iff (~i_rst_n)
      ((i_mem_req.rd.en && ~o_mem_rd_ready) |-> i_mem_req.wr.en ##1 o_mem_rd_ready);
  endproperty

  property p_wr_starvation;
    @(posedge i_clk) disable iff (~i_rst_n)
      ((i_mem_req.wr.en && ~o_mem_wr_ready) |-> i_mem_req.rd.en ##1 o_mem_wr_ready);
  endproperty

  property p_rd_latency;
    bit req;
    @(posedge i_clk) disable iff (~i_rst_n)
      ((o_mem_rd_ready, req=i_mem_req.rd.en) |-> ##L2_MEMORY_RESP_LATENCY (req == o_mem_rsp.rd_rsp));
  endproperty

  property p_wr_latency;
    bit req;
    @(posedge i_clk) disable iff (~i_rst_n)
      ((o_mem_wr_ready, req=i_mem_req.wr.en) |-> ##L2_MEMORY_RESP_LATENCY (req == o_mem_rsp.wr_rsp));
  endproperty

  // =====================================================
  // Assumes
  // =====================================================

  asp_stable_read         : assume property(p_stable_read);

  asp_stable_write        : assume property(p_stable_write);

  asp_read_one_rsp_valid  : assume property(p_read_one_rsp_valid);

  for (genvar bank = 0; bank < L2_NUM_BANKS; bank++) begin : g_assume_bank
    for (genvar ram = 0; ram < L2_NUM_RAMS; ram++) begin : g_assume_ram
      asp_read_data_valid     : assume property(p_read_data_valid(l2_mem.g_bank[bank].u_l2_bank.ram_rsp[ram]));
    end
  end
  // =====================================================
  // Assertions
  // =====================================================

  for (genvar bank = 0; bank < L2_NUM_BANKS; bank++) begin : g_bank
    for (genvar ram = 0; ram < L2_NUM_RAMS; ram++) begin : g_ram
      ap_no_req          : assert property (p_no_req(l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ce
                                                    ,l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ram.we
                                                    ,((bank==i_mem_req.rd.addr.bank) && (ram==i_mem_req.rd.addr.ram))));
      ap_read_req        : assert property (p_read_req(l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ce
                                                    ,l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ram.we
                                                    ,((bank==i_mem_req.rd.addr.bank) && (ram==i_mem_req.rd.addr.ram))));
      ap_write_req       : assert property (p_write_req(l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ce
                                                     ,l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ram.we
                                                     ,((bank==i_mem_req.wr.addr.bank) && (ram==i_mem_req.wr.addr.ram))));
      ap_write_data      : assert property (p_write_data(l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ce
                                                      ,l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ram.we
                                                      ,l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ram.data
                                                      ,((bank==i_mem_req.wr.addr.bank) && (ram==i_mem_req.wr.addr.ram))));
      ap_write_byte_en   : assert property (p_write_byte_en(l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ce
                                                         ,l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ram.we
                                                         ,l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.i_ram_req.ram.wbe
                                                         ,((bank==i_mem_req.wr.addr.bank) && (ram==i_mem_req.wr.addr.ram))));
      ap_read_data       : assert property (p_read_data(l2_mem.g_bank[bank].u_l2_bank.ram_rsp[ram]));
      ap_bank_sanity_data: assert property (p_read_data_valid(l2_mem.u_l2_xbar.i_bank_rsp[bank]));
    end
  end

  ap_rd_starvation : assert property (p_rd_starvation);

  ap_wr_starvation : assert property (p_wr_starvation);

  //ap_rd_latency    : assert property (p_rd_latency);

  ap_wr_latency    : assert property (p_wr_latency);

  // =====================================================
  // Covers
  // =====================================================

endmodule

`endif  // L2_MEM_SVA_SV
