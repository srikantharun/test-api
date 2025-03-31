// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Joao Martins <joao.martins@axelera.ai>

// Description: Scratchpad memory

`ifndef SPM_MEM_MINI_BANK_SV
  `define SPM_MEM_MINI_BANK_SV

module spm_mem_mini_bank
  import spm_pkg::*;
  import axe_tcl_sram_pkg::*;
#(
  // Types
  parameter int unsigned SPM_NB_SRAMS = 2,
  parameter type spm_mem_mini_bank_addr_t = spm_mem_addr_ab_t,
  parameter type spm_sram_addr_t = logic [13-1:0],
  parameter type spm_sram_data_t = logic [64-1:0],
  parameter type spm_sram_wbe_t  = logic [8-1:0]
) (
  // Clock signal
  input  wire            i_clk,
  input  wire            i_rst_n,
  // RAM interface signals
  input  logic                    i_req,
  input  logic                    i_we,
  input  spm_sram_wbe_t           i_be,
  input  spm_mem_mini_bank_addr_t i_addr,
  input  spm_sram_data_t          i_wdata,
  output spm_sram_data_t          o_rdata,
  output logic                    o_rvalid,
  // RAM Configuration pins
  input  impl_inp_t [SPM_NB_SRAMS-1:0] i_impl,
  output impl_oup_t [SPM_NB_SRAMS-1:0] o_impl
);
  // =====================================================
  // Local parameters
  // =====================================================

  // Wrapping up the request payload into a data type
  typedef struct packed {
    logic                    we;
    spm_sram_wbe_t           be;
    spm_mem_mini_bank_addr_t addr;
    spm_sram_data_t          data;
  } spm_mem_mini_bank_req_payload_t;

  // =====================================================
  // Signal declarations
  // =====================================================
  logic i_req_q;

  logic           [SPM_NB_SRAMS-1:0] sram_i_ce;
  logic           [SPM_NB_SRAMS-1:0] sram_i_we;
  spm_sram_wbe_t  [SPM_NB_SRAMS-1:0] sram_i_be;
  spm_sram_addr_t [SPM_NB_SRAMS-1:0] sram_i_addr;
  spm_sram_data_t [SPM_NB_SRAMS-1:0] sram_i_data;
  spm_sram_data_t [SPM_NB_SRAMS-1:0] sram_o_data;

  // Read Request
  logic[SPM_NB_SRAMS-1:0] rd_req_arr_d;
  logic[SPM_NB_SRAMS-1:0] rd_req_arr_q;

  logic rd_req_d, rd_req_q;
  logic o_valid_q;

  spm_sram_data_t o_data_comb;
  spm_sram_data_t o_data_q;

  spm_mem_mini_bank_req_payload_t req_payload_sr_d, req_payload_sr_q;
  logic                           req_valid_sr_d, req_valid_sr_q;

  // =====================================================
  // RTL
  // =====================================================

  // Input pipe
  always_comb begin
    req_valid_sr_d = i_req;

    req_payload_sr_d.we   = i_we   ;
    req_payload_sr_d.be   = i_be   ;
    req_payload_sr_d.addr = i_addr ;
    req_payload_sr_d.data = i_wdata;
  end

  cc_cnt_shift_reg #(
    .data_t(spm_mem_mini_bank_req_payload_t),
    .Stages(1)
  ) u_input_shift_req (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    .i_clear(1'b0),
    .i_stall(1'b0),
    .i_data   (req_payload_sr_d),
    .i_data_en(req_valid_sr_d),
    .o_data   (req_payload_sr_q),
    .o_updated(req_valid_sr_q)
  );

  // Store if the request was a read (rd_req=1'b1) and for which RAM instance
  always_comb begin: store_req
    rd_req_d = req_valid_sr_q & !req_payload_sr_q.we;
    for(int unsigned gen_int_idx = 0; gen_int_idx < SPM_NB_SRAMS; gen_int_idx++) begin : g_rd_req_arr
      rd_req_arr_d[gen_int_idx] = sram_i_ce[gen_int_idx] && !sram_i_we[gen_int_idx];
    end
  end

  // =========================
  // -- Downstream
  always_comb begin: drive_proper_sram
    for(int unsigned gen_int_idx = 0; gen_int_idx < SPM_NB_SRAMS; gen_int_idx++) begin : g_sram_drv
      if(SPM_NB_SRAMS==1) begin
        sram_i_ce[gen_int_idx] = req_valid_sr_q;
      end else begin
        sram_i_ce[gen_int_idx] = req_valid_sr_q & (req_payload_sr_q.addr.sel == gen_int_idx);
      end

      //    Using the CE to enable just the RAM we need,
      // we can drive all other inputs assuming only 1 is ungated by the CE
      sram_i_addr [gen_int_idx] = req_payload_sr_q.addr.sram_addr;
      sram_i_we   [gen_int_idx] = req_payload_sr_q.we;
      sram_i_be   [gen_int_idx] = req_payload_sr_q.be;
      sram_i_data [gen_int_idx] = req_payload_sr_q.data;
    end
  end

  // Generated SRAMs
  for(genvar gen_idx = 0; unsigned'(gen_idx) < SPM_NB_SRAMS; gen_idx++) begin : g_sram_inst
    axe_tcl_ram_1rwp #(
      .NumWords (2**$bits(spm_sram_addr_t)),
      .DataWidth($bits(spm_sram_data_t)),
      .ByteWidth(8),
      .ReadLatency(1),
      .ImplKey("HS_RVT"),
      .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
      .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
    ) u_tc_sram (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),
      // Config
      .i_impl (i_impl[gen_idx]),
      .o_impl (o_impl[gen_idx]),
      // Interface signals
      .i_req      (sram_i_ce  [gen_idx]) ,
      .i_addr     (sram_i_addr[gen_idx]) ,
      .i_wr_enable(sram_i_we  [gen_idx]) ,
      .i_wr_data  (sram_i_data[gen_idx]) ,
      .i_wr_mask  (sram_i_be  [gen_idx]) ,
      .o_rd_data  (sram_o_data[gen_idx])
    );
  end

  // =========================
  // -- Upstream
  // Delayed read request to account for SRAM latency
  cc_cnt_shift_reg #(
    .data_t(logic[SPM_NB_SRAMS-1:0]),
    .Stages(1)
  ) u_shift_req (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    .i_clear(1'b0),
    .i_stall(1'b0),
    .i_data   (rd_req_arr_d),
    .i_data_en(rd_req_d),
    .o_data   (rd_req_arr_q),
    .o_updated(rd_req_q)
  );

  // Get proper read data out based on which one received read request.
  // Zero'ed out if there was no read request.
  int unsigned sram_idx;
  always_comb begin : g_mini_bank_mux_out
    o_data_comb  = spm_sram_data_t'(0);
    for(sram_idx = 0; sram_idx < SPM_NB_SRAMS; sram_idx++) begin : g_sram_o_merge
      if(rd_req_arr_q[sram_idx])begin
        o_data_comb |= sram_o_data[sram_idx];
      end
    end
  end

  // Then finally we register our result
  cc_cnt_shift_reg #(
    .data_t(spm_sram_data_t),
    .Stages(1)
  ) u_shift_data (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    .i_clear(1'b0),
    .i_stall(1'b0),
    .i_data   (o_data_comb),
    .i_data_en(rd_req_q),
    .o_data   (o_data_q),
    .o_updated(o_valid_q)
  );

  always_comb o_rdata = o_data_q;
  always_comb o_rvalid = o_valid_q;

endmodule

`endif // SPM_MEM_MINI_BANK_SV
