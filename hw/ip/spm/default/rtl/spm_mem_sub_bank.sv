// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Joao Martins <joao.martins@axelera.ai>

// Description: Scratchpad memory

`ifndef SPM_MEM_SUB_BANK_SV
  `define SPM_MEM_SUB_BANK_SV

module spm_mem_sub_bank
  import spm_pkg::*;
  import axe_tcl_sram_pkg::*;
#(
  // Types
  parameter int unsigned SPM_NB_SRAMS_PER_MINI_BANK = 2,
  parameter int unsigned SPM_NB_MINI_BANKS = 2,
  parameter type spm_mem_sub_bank_addr_t = spm_mem_addr_ab_t,
  parameter type spm_sram_addr_t = logic [13-1:0],
  parameter type spm_sram_data_t = logic [64-1:0],
  parameter type spm_sram_wbe_t  = logic [8-1:0],
  // Adding these here ensures the math is centralised upstream
  parameter int unsigned SPM_MEM_MINI_BANK_SEL_WIDTH = 0,
  parameter int unsigned SPM_MEM_SRAM_SEL_WIDTH      = 0
) (
  // Clock signal
  input  wire            i_clk,
  input  wire            i_rst_n,
  // RAM interface signals
  input  logic                    i_req,
  input  logic                    i_we,
  input  spm_sram_wbe_t           i_be,
  input  spm_mem_sub_bank_addr_t  i_addr,
  input  spm_sram_data_t          i_wdata,
  output spm_sram_data_t          o_rdata,
  output logic                    o_rvalid,
  // RAM Configuration pins
  input  impl_inp_t [SPM_NB_MINI_BANKS-1:0][SPM_NB_SRAMS_PER_MINI_BANK-1:0] i_impl,
  output impl_oup_t [SPM_NB_MINI_BANKS-1:0][SPM_NB_SRAMS_PER_MINI_BANK-1:0] o_impl
);
  // =====================================================
  // Local parameters
  // =====================================================
  localparam int unsigned SEL_ADDR_WIDTH = SPM_MEM_SRAM_SEL_WIDTH;

  typedef struct packed {
    logic [SEL_ADDR_WIDTH-1:0] sel;
    spm_sram_addr_t            sram_addr;
  } spm_mem_mini_bank_addr_t;

  // =====================================================
  // Signal declarations
  // =====================================================
  logic                    [SPM_NB_MINI_BANKS-1:0] mini_bank_i_req;
  logic                    [SPM_NB_MINI_BANKS-1:0] mini_bank_i_we;
  spm_sram_wbe_t           [SPM_NB_MINI_BANKS-1:0] mini_bank_i_be;
  spm_mem_mini_bank_addr_t [SPM_NB_MINI_BANKS-1:0] mini_bank_i_addr;
  spm_sram_data_t          [SPM_NB_MINI_BANKS-1:0] mini_bank_i_wdata;
  logic                    [SPM_NB_MINI_BANKS-1:0] mini_bank_o_rvalid;
  spm_sram_data_t          [SPM_NB_MINI_BANKS-1:0] mini_bank_o_rdata;

  spm_mem_mini_bank_addr_t sliced_i_addr;

  // =========================
  // -- Downstream
  // Generated inputs
  // Compute the local address and slice the address to pass downstream
  always_comb begin
    sliced_i_addr.sel       = i_addr.sel[SEL_ADDR_WIDTH-1:0];
    sliced_i_addr.sram_addr = i_addr.sram_addr;
  end

  always_comb begin
    for(int unsigned gen_int_idx = 0; gen_int_idx < SPM_NB_MINI_BANKS; gen_int_idx++) begin: g_inp_drv
      if(SPM_NB_MINI_BANKS==1) begin
        mini_bank_i_req[gen_int_idx] = i_req;
      end else begin
        mini_bank_i_req[gen_int_idx] = i_req &
                                     ( (i_addr.sel >> SEL_ADDR_WIDTH) == gen_int_idx);
      end

      // Drive all inputs assuming CE will ensure only the right macro is actually driven
      mini_bank_i_we   [gen_int_idx] = i_we;
      mini_bank_i_be   [gen_int_idx] = i_be;
      mini_bank_i_wdata[gen_int_idx] = i_wdata;
      mini_bank_i_addr [gen_int_idx] = sliced_i_addr;
    end
  end

  // Generated Mini-Banks
  for(genvar gen_idx = 0; unsigned'(gen_idx) < SPM_NB_MINI_BANKS; gen_idx++) begin : g_mini_bank_inst
    spm_mem_mini_bank #(
      .SPM_NB_SRAMS(SPM_NB_SRAMS_PER_MINI_BANK),
      .spm_mem_mini_bank_addr_t(spm_mem_mini_bank_addr_t),
      .spm_sram_addr_t(spm_sram_addr_t),
      .spm_sram_data_t(spm_sram_data_t),
      .spm_sram_wbe_t (spm_sram_wbe_t )
    ) u_spm_mem_mini_bank (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),
      .i_impl (i_impl[gen_idx]),
      .o_impl (o_impl[gen_idx]),
      // RAM interface signals
      .i_req   (mini_bank_i_req   [gen_idx]),
      .i_we    (mini_bank_i_we    [gen_idx]),
      .i_be    (mini_bank_i_be    [gen_idx]),
      .i_addr  (mini_bank_i_addr  [gen_idx]),
      .i_wdata (mini_bank_i_wdata [gen_idx]),
      .o_rdata (mini_bank_o_rdata [gen_idx]),
      .o_rvalid(mini_bank_o_rvalid[gen_idx])
    );
  end

  // =========================
  // -- Upstream
  // TODO(jmartins, Bronze, Possibly group this into 2 by 2 mini-banks)
  int unsigned mini_bank_idx;
  always_comb begin : g_sub_bank_mux_out
    o_rdata  = spm_sram_data_t'(0);
    o_rvalid= 1'b0;
    for(mini_bank_idx = 0; mini_bank_idx < SPM_NB_MINI_BANKS; mini_bank_idx++) begin : g_mini_bank_o_merge
      o_rdata  |= ({$bits(o_rdata){mini_bank_o_rvalid[mini_bank_idx]}} &
                                   mini_bank_o_rdata [mini_bank_idx]);
      o_rvalid |= mini_bank_o_rvalid[mini_bank_idx];
    end
  end

endmodule
`endif // SPM_MEM_SUB_BANK_SV
