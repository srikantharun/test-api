// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Joao Martins <joao.martins@axelera.ai>

// Description: Scratchpad memory

`ifndef SPM_MEM_SV
  `define SPM_MEM_SV

module spm_mem
  import spm_pkg::*;
  import axe_tcl_sram_pkg::*;
#(
  parameter int unsigned SPM_NB_BANKS      = 1,
  parameter int unsigned SPM_NB_SUB_BANKS  = 1,
  parameter int unsigned SPM_NB_MINI_BANKS = 1,
  parameter int unsigned SPM_NB_SRAMS_PER_MINI_BANK = 2,
  parameter int unsigned SPM_NB_REQ_PIPELINE = 0,
  parameter int unsigned SPM_NB_RSP_PIPELINE = 0,
  parameter int unsigned SPM_MEM_MACRO_ADDR_WIDTH = 13, // 8K
  parameter int unsigned SPM_MEM_DATA_WIDTH = 64,
  parameter int unsigned SPM_MEM_ADDR_WIDTH = 16,
  parameter int unsigned SPM_MEM_WBE_WIDTH  = 8,
  parameter int unsigned SPM_DAISY_CHAIN_MAPPING_OVERWRITE_EN,
  parameter spm_mem_map_cfg_t SPM_DAISY_CHAIN_MAPPING[SPM_NB_BANKS * SPM_NB_SUB_BANKS * SPM_NB_MINI_BANKS * SPM_NB_SRAMS_PER_MINI_BANK] =
    '{(SPM_NB_BANKS*SPM_NB_SUB_BANKS*SPM_NB_MINI_BANKS*SPM_NB_SRAMS_PER_MINI_BANK){spm_mem_map_cfg_t'{bank_idx:0, subbank_idx:0, minibank_idx:0, srams_idx:0}}}
) (
  // Clock signal
  input  wire                           i_clk,
  input  wire                           i_rst_n,
  // RAM interface signals
  input  logic                          i_req,
  input  logic                          i_we,
  input  logic [ SPM_MEM_WBE_WIDTH-1:0] i_be,
  input  logic [SPM_MEM_ADDR_WIDTH-1:0] i_addr,
  input  logic [SPM_MEM_DATA_WIDTH-1:0] i_wdata,
  output logic [SPM_MEM_DATA_WIDTH-1:0] o_rdata,
  output logic                          o_rvalid,
  // RAM Configuration pins
  input  impl_inp_t i_impl,
  output impl_oup_t o_impl
);

  // =====================================================
  // Local parameters
  // =====================================================
  typedef logic[SPM_MEM_MACRO_ADDR_WIDTH-1:0] spm_sram_addr_t;
  typedef logic[SPM_MEM_DATA_WIDTH-1:0]       spm_sram_data_t;
  typedef logic [SPM_MEM_WBE_WIDTH-1:0]       spm_sram_wbe_t;

  // TODO(jmartins, Bronze, Add checks for the widths)
  localparam int unsigned SPM_MEM_BANK_SEL_WIDTH      = $clog2(SPM_NB_BANKS);
  localparam int unsigned SPM_MEM_SUB_BANK_SEL_WIDTH  = $clog2(SPM_NB_SUB_BANKS);
  localparam int unsigned SPM_MEM_MINI_BANK_SEL_WIDTH = $clog2(SPM_NB_MINI_BANKS);
  localparam int unsigned SPM_MEM_SRAM_SEL_WIDTH      = $clog2(SPM_NB_SRAMS_PER_MINI_BANK);

  localparam int unsigned SEL_ADDR_WIDTH = SPM_MEM_SUB_BANK_SEL_WIDTH+SPM_MEM_MINI_BANK_SEL_WIDTH+SPM_MEM_SRAM_SEL_WIDTH;
  localparam int unsigned BANK_SEL_WIDTH = SPM_MEM_BANK_SEL_WIDTH;

  typedef struct packed {
    logic [SEL_ADDR_WIDTH-1:0] sel;
    spm_sram_addr_t            sram_addr;
  } spm_mem_bank_addr_t;

  // =====================================================
  // Tech Cell Library impl configurations
  // Power Down chaining
  // =====================================================

  // Generation of the default value for power ip daisy chain
  localparam int unsigned SPM_SUBBANK_OFFSET = SPM_NB_MINI_BANKS * SPM_NB_SRAMS_PER_MINI_BANK;
  localparam int unsigned SPM_BANK_OFFSET = SPM_NB_SUB_BANKS * SPM_SUBBANK_OFFSET;
  typedef spm_mem_map_cfg_t spm_int_def_daisy_chain_t[SPM_NB_BANKS * SPM_BANK_OFFSET];

  function automatic spm_int_def_daisy_chain_t spm_fill_default_daisy_chain_mapping();
    for (int unsigned bank_idx=0; bank_idx<SPM_NB_BANKS; bank_idx++) begin
      for (int unsigned subbank_idx=0; subbank_idx<SPM_NB_SUB_BANKS; subbank_idx++) begin
        for (int unsigned minibank_idx=0; minibank_idx<SPM_NB_MINI_BANKS; minibank_idx++) begin
          for (int unsigned srams_idx=0; srams_idx<SPM_NB_SRAMS_PER_MINI_BANK; srams_idx++) begin
            spm_fill_default_daisy_chain_mapping[(bank_idx * SPM_BANK_OFFSET) +
                            (subbank_idx * SPM_SUBBANK_OFFSET) + (minibank_idx * SPM_NB_SRAMS_PER_MINI_BANK) + srams_idx].bank_idx = bank_idx;
            spm_fill_default_daisy_chain_mapping[(bank_idx * SPM_BANK_OFFSET) +
                            (subbank_idx * SPM_SUBBANK_OFFSET) + (minibank_idx * SPM_NB_SRAMS_PER_MINI_BANK) + srams_idx].subbank_idx = subbank_idx;
            spm_fill_default_daisy_chain_mapping[(bank_idx * SPM_BANK_OFFSET) +
                            (subbank_idx * SPM_SUBBANK_OFFSET) + (minibank_idx * SPM_NB_SRAMS_PER_MINI_BANK) + srams_idx].minibank_idx = minibank_idx;
            spm_fill_default_daisy_chain_mapping[(bank_idx * SPM_BANK_OFFSET) +
                            (subbank_idx * SPM_SUBBANK_OFFSET) + (minibank_idx * SPM_NB_SRAMS_PER_MINI_BANK) + srams_idx].srams_idx = srams_idx;
          end
        end
      end
    end
  endfunction

  localparam spm_mem_map_cfg_t DEFAULT_SPM_DAISY_CHAIN_MAPPING[SPM_NB_BANKS * SPM_BANK_OFFSET] =
                                 spm_fill_default_daisy_chain_mapping();

  localparam spm_mem_map_cfg_t SPM_DAISY_CHAIN_MAPPING_FINAL[SPM_NB_BANKS * SPM_BANK_OFFSET] =
                                 SPM_DAISY_CHAIN_MAPPING_OVERWRITE_EN ? SPM_DAISY_CHAIN_MAPPING : DEFAULT_SPM_DAISY_CHAIN_MAPPING;


  // Power Down chaining
  impl_inp_t [SPM_NB_BANKS-1:0][SPM_NB_SUB_BANKS-1:0][SPM_NB_MINI_BANKS-1:0][SPM_NB_SRAMS_PER_MINI_BANK-1:0] inst_mem_impl_inp;
  impl_oup_t [SPM_NB_BANKS-1:0][SPM_NB_SUB_BANKS-1:0][SPM_NB_MINI_BANKS-1:0][SPM_NB_SRAMS_PER_MINI_BANK-1:0] inst_mem_impl_oup;
  impl_inp_t [(SPM_NB_BANKS*SPM_NB_SUB_BANKS*SPM_NB_MINI_BANKS*SPM_NB_SRAMS_PER_MINI_BANK)-1:0] daisy_chain_mem_impl_inp;
  impl_oup_t [(SPM_NB_BANKS*SPM_NB_SUB_BANKS*SPM_NB_MINI_BANKS*SPM_NB_SRAMS_PER_MINI_BANK)-1:0] daisy_chain_mem_impl_oup;

  // chain mapping:
  always_comb begin: c_chain_mem_assign
    for (uint_t mem_idx=0; mem_idx<(SPM_NB_BANKS*SPM_NB_SUB_BANKS*SPM_NB_MINI_BANKS*SPM_NB_SRAMS_PER_MINI_BANK); mem_idx++) begin
      automatic uint_t bank_idx = SPM_DAISY_CHAIN_MAPPING_FINAL[mem_idx].bank_idx;
      automatic uint_t subbank_idx = SPM_DAISY_CHAIN_MAPPING_FINAL[mem_idx].subbank_idx;
      automatic uint_t minibank_idx  = SPM_DAISY_CHAIN_MAPPING_FINAL[mem_idx].minibank_idx;
      automatic uint_t srams_idx = SPM_DAISY_CHAIN_MAPPING_FINAL[mem_idx].srams_idx;

      inst_mem_impl_inp[bank_idx][subbank_idx][minibank_idx][srams_idx] = daisy_chain_mem_impl_inp[mem_idx];
      daisy_chain_mem_impl_oup[mem_idx] = inst_mem_impl_oup[bank_idx][subbank_idx][minibank_idx][srams_idx];
    end
  end

  // actual chain:
  axe_tcl_sram_cfg #(
    .NUM_SRAMS(SPM_NB_BANKS*SPM_NB_SUB_BANKS*SPM_NB_MINI_BANKS*SPM_NB_SRAMS_PER_MINI_BANK)
  ) u_sram_cfg (
    .i_s(i_impl),
    .o_s(o_impl),
    .o_m(daisy_chain_mem_impl_inp),
    .i_m(daisy_chain_mem_impl_oup)
  );

  // =====================================================
  // Signal declarations
  // =====================================================
  logic               [SPM_NB_BANKS-1:0] bank_i_req  ;
  logic               [SPM_NB_BANKS-1:0] bank_i_we   ;
  spm_sram_wbe_t      [SPM_NB_BANKS-1:0] bank_i_be   ;
  spm_mem_bank_addr_t [SPM_NB_BANKS-1:0] bank_i_addr ;
  spm_sram_data_t     [SPM_NB_BANKS-1:0] bank_i_wdata;
  logic               [SPM_NB_BANKS-1:0] bank_o_rvalid;
  spm_sram_data_t     [SPM_NB_BANKS-1:0] bank_o_rdata;

  spm_mem_bank_addr_t     sliced_i_addr;

  // =====================================================
  // Logic
  // =====================================================
  // Compute the local address and slice the address to pass downstream
  always_comb begin
    sliced_i_addr.sel       = i_addr[SPM_MEM_ADDR_WIDTH-SPM_MEM_BANK_SEL_WIDTH-1:SPM_MEM_MACRO_ADDR_WIDTH];
    sliced_i_addr.sram_addr = i_addr[SPM_MEM_MACRO_ADDR_WIDTH-1:0];
  end

  // =========================
  // -- Downstream
  // Generated inputs
  always_comb begin
    for(int unsigned gen_int_idx = 0; gen_int_idx < SPM_NB_BANKS; gen_int_idx++) begin : g_inp_drv
      // The math here means that we can cover the corner case where there's a single Bank
      // - When NB_BANK=1 - the address is shifted until disappearing meaning we get 0 which matches gen_int_idx
      // - When NB_BANK>1 - Normal operation where we shift leaving the MSBs needed for selection
      bank_i_req[gen_int_idx] = i_req &
                                (i_addr >> (SPM_MEM_ADDR_WIDTH-SPM_MEM_BANK_SEL_WIDTH) == gen_int_idx);

      // Drive all inputs assuming CE will ensure only the right macro is actually driven
      bank_i_we   [gen_int_idx] = i_we;
      bank_i_be   [gen_int_idx] = i_be;
      bank_i_wdata[gen_int_idx] = i_wdata;
      bank_i_addr [gen_int_idx] = sliced_i_addr;
    end
  end

  // Generated Banks
  for(genvar gen_idx = 0; unsigned'(gen_idx) < SPM_NB_BANKS; gen_idx++) begin : g_bank_inst
    spm_mem_bank #(
      .SPM_NB_SUB_BANKS (SPM_NB_SUB_BANKS ),
      .SPM_NB_MINI_BANKS(SPM_NB_MINI_BANKS),
      .SPM_NB_SRAMS_PER_MINI_BANK(SPM_NB_SRAMS_PER_MINI_BANK),
      .SPM_NB_REQ_PIPELINE(SPM_NB_REQ_PIPELINE),
      .SPM_NB_RSP_PIPELINE(SPM_NB_RSP_PIPELINE),
      .spm_mem_bank_addr_t(spm_mem_bank_addr_t),
      .spm_sram_addr_t(spm_sram_addr_t),
      .spm_sram_data_t(spm_sram_data_t),
      .spm_sram_wbe_t (spm_sram_wbe_t ),
      .SPM_MEM_SUB_BANK_SEL_WIDTH (SPM_MEM_SUB_BANK_SEL_WIDTH ),
      .SPM_MEM_MINI_BANK_SEL_WIDTH(SPM_MEM_MINI_BANK_SEL_WIDTH),
      .SPM_MEM_SRAM_SEL_WIDTH     (SPM_MEM_SRAM_SEL_WIDTH     )
    ) u_spm_mem_bank (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),
      .i_impl (inst_mem_impl_inp[gen_idx]),
      .o_impl (inst_mem_impl_oup[gen_idx]),
      // RAM interface signals
      .i_req   (bank_i_req   [gen_idx]),
      .i_we    (bank_i_we    [gen_idx]),
      .i_be    (bank_i_be    [gen_idx]),
      .i_addr  (bank_i_addr  [gen_idx]),
      .i_wdata (bank_i_wdata [gen_idx]),
      .o_rdata (bank_o_rdata [gen_idx]),
      .o_rvalid(bank_o_rvalid[gen_idx])
    );
  end

  // =========================
  // -- Output
  // We mask each bank's output based on the valid and OR every masked result
  int unsigned bank_idx;
  always_comb begin : gate_out_data_comb_proc
    o_rdata  = {SPM_MEM_DATA_WIDTH{1'b0}};
    o_rvalid = 1'b0;
    for(bank_idx = 0; bank_idx < SPM_NB_BANKS; bank_idx++) begin : g_sub_bank_out
      o_rdata  |= ({$bits(o_rdata){bank_o_rvalid[bank_idx]}} &
                                   bank_o_rdata[bank_idx]);
      o_rvalid |= bank_o_rvalid[bank_idx];
    end
  end

endmodule
`endif // SPM_MEM_SV
