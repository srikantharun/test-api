// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Joao Martins <joao.martins@axelera.ai>

// Description: Scratchpad memory

`ifndef SPM_MEM_BANK_SV
  `define SPM_MEM_BANK_SV

module spm_mem_bank
  import spm_pkg::*;
  import axe_tcl_sram_pkg::*;
#(
  parameter int unsigned SPM_NB_SUB_BANKS  = 2,
  parameter int unsigned SPM_NB_MINI_BANKS = 2,
  parameter int unsigned SPM_NB_SRAMS_PER_MINI_BANK = 2,
  parameter int unsigned SPM_NB_REQ_PIPELINE = 0,
  parameter int unsigned SPM_NB_RSP_PIPELINE = 0,
  parameter type spm_mem_bank_addr_t = spm_mem_addr_ab_t,
  parameter type spm_sram_addr_t     = logic [13-1:0],
  parameter type spm_sram_data_t     = logic [64-1:0],
  parameter type spm_sram_wbe_t      = logic [8-1:0],
  // Adding these here ensures the math is centralised upstream
  parameter int unsigned SPM_MEM_SUB_BANK_SEL_WIDTH  = 0,
  parameter int unsigned SPM_MEM_MINI_BANK_SEL_WIDTH = 0,
  parameter int unsigned SPM_MEM_SRAM_SEL_WIDTH      = 0
) (
  // Clock signal
  input  wire                i_clk,
  input  wire                i_rst_n,
  // RAM interface signals
  input  logic               i_req,
  input  logic               i_we,
  input  spm_sram_wbe_t      i_be,
  input  spm_mem_bank_addr_t i_addr,
  input  spm_sram_data_t     i_wdata,
  output spm_sram_data_t     o_rdata,
  output logic               o_rvalid,
  // RAM Configuration pins
  input  impl_inp_t [SPM_NB_SUB_BANKS-1:0][SPM_NB_MINI_BANKS-1:0][SPM_NB_SRAMS_PER_MINI_BANK-1:0] i_impl,
  output impl_oup_t [SPM_NB_SUB_BANKS-1:0][SPM_NB_MINI_BANKS-1:0][SPM_NB_SRAMS_PER_MINI_BANK-1:0] o_impl
);

  // =====================================================
  // Local parameters
  // =====================================================
  localparam int unsigned SEL_ADDR_WIDTH = SPM_MEM_MINI_BANK_SEL_WIDTH+SPM_MEM_SRAM_SEL_WIDTH;

  // Wrapping up the request and response payloads into a data type
  typedef struct packed {
    logic               we;
    spm_sram_wbe_t      be;
    spm_mem_bank_addr_t addr;
    spm_sram_data_t     data;
  } spm_bank_req_payload_t;

  typedef struct packed {
    spm_sram_data_t      data;
  } spm_bank_rsp_payload_t;

  // Easier to handle address slicing type
  typedef struct packed {
    logic [SEL_ADDR_WIDTH-1:0] sel;
    spm_sram_addr_t            sram_addr;
  } spm_mem_sub_bank_addr_t;

  // =====================================================
  // Signal declarations
  // =====================================================
  spm_bank_req_payload_t req_payload_sr_d, req_payload_sr_q;
  logic                  req_valid_sr_d, req_valid_sr_q;

  spm_bank_rsp_payload_t rsp_payload_sr_d, rsp_payload_sr_q;
  logic                  rsp_valid_sr_d, rsp_valid_sr_q;

  spm_mem_sub_bank_addr_t sliced_i_addr;

  logic                   [SPM_NB_SUB_BANKS-1:0] sub_bank_i_req;
  logic                   [SPM_NB_SUB_BANKS-1:0] sub_bank_i_we;
  spm_sram_wbe_t          [SPM_NB_SUB_BANKS-1:0] sub_bank_i_be;
  spm_mem_sub_bank_addr_t [SPM_NB_SUB_BANKS-1:0] sub_bank_i_addr;
  spm_sram_data_t         [SPM_NB_SUB_BANKS-1:0] sub_bank_i_wdata;
  logic                   [SPM_NB_SUB_BANKS-1:0] sub_bank_o_rvalid;
  spm_sram_data_t         [SPM_NB_SUB_BANKS-1:0] sub_bank_o_rdata;

  // =====================================================
  // Logic
  // =====================================================
  // Pipeline and send down
  always_comb begin
    req_valid_sr_d = i_req;

    req_payload_sr_d.we   = i_we   ;
    req_payload_sr_d.be   = i_be   ;
    req_payload_sr_d.addr = i_addr ;
    req_payload_sr_d.data = i_wdata;
  end

  cc_cnt_shift_reg #(
    .data_t(spm_bank_req_payload_t),
    .Stages(SPM_NB_REQ_PIPELINE)
  ) u_shift_bank_req (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    .i_clear(1'b0),
    .i_stall(1'b0),
    .i_data   (req_payload_sr_d),
    .i_data_en(req_valid_sr_d),
    .o_data   (req_payload_sr_q),
    .o_updated(req_valid_sr_q)
  );

  // =========================
  // -- Downstream
  // Generated inputs
  // Compute the local address and slice the address to pass downstream
  always_comb begin
    sliced_i_addr.sel       = req_payload_sr_q.addr.sel[SEL_ADDR_WIDTH-1:0];
    sliced_i_addr.sram_addr = req_payload_sr_q.addr.sram_addr;
  end

  always_comb begin
    for(int unsigned gen_int_idx = 0; gen_int_idx < SPM_NB_SUB_BANKS; gen_int_idx++) begin: g_inp_drv
      if(SPM_NB_SUB_BANKS==1) begin
        sub_bank_i_req[gen_int_idx] = req_valid_sr_q;
      end else begin
        sub_bank_i_req[gen_int_idx] = req_valid_sr_q &
                                    ( (req_payload_sr_q.addr.sel>>SEL_ADDR_WIDTH) == gen_int_idx);
      end

      // Drive all inputs assuming CE will ensure only the right macro is actually driven
      sub_bank_i_we   [gen_int_idx] = req_payload_sr_q.we;
      sub_bank_i_be   [gen_int_idx] = req_payload_sr_q.be;
      sub_bank_i_wdata[gen_int_idx] = req_payload_sr_q.data;
      sub_bank_i_addr [gen_int_idx] = sliced_i_addr;
    end
  end

  // Generated Sub-Banks
  for(genvar gen_idx = 0; unsigned'(gen_idx) < SPM_NB_SUB_BANKS; gen_idx++) begin : g_sub_bank_inst
    spm_mem_sub_bank #(
      .SPM_NB_MINI_BANKS(SPM_NB_MINI_BANKS),
      .SPM_NB_SRAMS_PER_MINI_BANK(SPM_NB_SRAMS_PER_MINI_BANK),
      .spm_mem_sub_bank_addr_t(spm_mem_sub_bank_addr_t),
      .spm_sram_addr_t(spm_sram_addr_t),
      .spm_sram_data_t(spm_sram_data_t),
      .spm_sram_wbe_t (spm_sram_wbe_t ),
      .SPM_MEM_MINI_BANK_SEL_WIDTH(SPM_MEM_MINI_BANK_SEL_WIDTH),
      .SPM_MEM_SRAM_SEL_WIDTH(SPM_MEM_SRAM_SEL_WIDTH)
    ) u_spm_mem_sub_bank (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),
      .i_impl (i_impl[gen_idx]),
      .o_impl (o_impl[gen_idx]),
      // RAM interface signals
      .i_req   (sub_bank_i_req   [gen_idx]),
      .i_we    (sub_bank_i_we    [gen_idx]),
      .i_be    (sub_bank_i_be    [gen_idx]),
      .i_addr  (sub_bank_i_addr  [gen_idx]),
      .i_wdata (sub_bank_i_wdata [gen_idx]),
      .o_rdata (sub_bank_o_rdata [gen_idx]),
      .o_rvalid(sub_bank_o_rvalid[gen_idx])
    );
  end

  // =========================
  // -- Upstream
  int unsigned sub_bank_idx;
  always_comb begin : g_bank_mux_out
    rsp_payload_sr_d  = spm_sram_data_t'(0);
    rsp_valid_sr_d    = 1'b0;
    for(sub_bank_idx = 0; sub_bank_idx < SPM_NB_SUB_BANKS; sub_bank_idx++) begin : g_sub_bank_o_merge
      rsp_payload_sr_d |= ({$bits(o_rdata){sub_bank_o_rvalid[sub_bank_idx]}} &
                                           sub_bank_o_rdata [sub_bank_idx]);
      rsp_valid_sr_d   |= sub_bank_o_rvalid[sub_bank_idx];
    end
  end

  cc_cnt_shift_reg #(
    .data_t(spm_bank_rsp_payload_t),
    .Stages(SPM_NB_RSP_PIPELINE)
  ) u_shift_bank_rsp (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    .i_clear(1'b0),
    .i_stall(1'b0),
    .i_data   (rsp_payload_sr_d),
    .i_data_en(rsp_valid_sr_d),
    .o_data   (rsp_payload_sr_q),
    .o_updated(rsp_valid_sr_q)
  );

  always_comb begin
    o_rdata  = rsp_payload_sr_q.data;
    o_rvalid = rsp_valid_sr_q;
  end

endmodule
`endif // SPM_MEM_BANK_SV
