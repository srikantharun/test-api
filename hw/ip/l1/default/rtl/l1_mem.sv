// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L1 memory
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module l1_mem
  import axe_tcl_sram_pkg::*, l1_pkg::*, mmio_pkg::*;
#(
  parameter uint_t L1_NUM_BANKS = DEFAULT_L1_NUM_BANKS,
  parameter uint_t L1_MACROS_PER_MINI_BANK = 1,
  parameter bit L1_REQ_PIPE = 1'b1,

  parameter uint_t NUM_DMC_SOURCES = 10,
  parameter uint_t NUM_RVV_SOURCES = 8,
  parameter mem_map_cfg_t L1_DAISY_CHAIN_MAPPING[L1_NR_SUB_BANKS * L1_NUM_BANKS * 1]  = DEFAULT_L1_DAISY_CHAIN_MAPPING,
  localparam uint_t TOT_NUM_SOURCES = NUM_DMC_SOURCES + NUM_RVV_SOURCES,
  localparam uint_t SRC_SEL_W = $clog2(TOT_NUM_SOURCES),
  localparam uint_t MINI_BANK_ADDR_WIDTH = L1_MACRO_ADDR_WIDTH + unsigned'($clog2(L1_MACROS_PER_MINI_BANK))
) (
  // Clock and reset signals
  input  wire                        i_clk,
  input  wire                        i_gated_clk,
  input  wire                        i_rst_n,

  input  logic [L1_NR_SUB_BANKS-1:0][L1_NUM_BANKS-1:0][SRC_SEL_W-1:0]  i_src_sel,
  input  logic [L1_NR_SUB_BANKS-1:0][L1_NUM_BANKS-1:0]                 i_src_vld,

  input  mmio_dmc_full_req_t [NUM_DMC_SOURCES-1:0]                     i_dmc_src_req,
  input  mmio_rvv_req_t      [NUM_RVV_SOURCES-1:0]                     i_rvv_src_req,

  output mmio_dmc_slim_rsp_t [NUM_DMC_SOURCES-1:0]                     o_dmc_src_rsp,
  output mmio_rvv_slim_rsp_t [NUM_RVV_SOURCES-1:0]                     o_rvv_src_rsp,

  input  impl_inp_t i_mem_impl,
  output impl_oup_t o_mem_impl
);

  // mini bank addr creation:            byte_offset         + sub_bank sel            + bank sel
  localparam uint_t ADDR_MINI_BANK_LSB = $clog2(L1_SUB_BANK_WIDTH/8) + $clog2(L1_NR_SUB_BANKS) + $clog2(L1_NUM_BANKS);
  // =====================================================
  // Power Down chaining
  // =====================================================
  impl_inp_t [L1_NR_SUB_BANKS-1:0][L1_NUM_BANKS-1:0][L1_MACROS_PER_MINI_BANK-1:0] inst_mem_impl_inp;
  impl_oup_t [L1_NR_SUB_BANKS-1:0][L1_NUM_BANKS-1:0][L1_MACROS_PER_MINI_BANK-1:0] inst_mem_impl_oup;
  impl_inp_t [(L1_NR_SUB_BANKS * L1_NUM_BANKS * L1_MACROS_PER_MINI_BANK)-1:0] daisy_chain_mem_impl_inp;
  impl_oup_t [(L1_NR_SUB_BANKS * L1_NUM_BANKS * L1_MACROS_PER_MINI_BANK)-1:0] daisy_chain_mem_impl_oup;

  // chain mapping:
  always_comb begin: c_chain_mem_assign
    automatic uint_t sb_idx;
    automatic uint_t mb_idx;
    automatic uint_t m_idx;

    for (uint_t mem_idx=0; mem_idx<L1_NR_SUB_BANKS * L1_NUM_BANKS * L1_MACROS_PER_MINI_BANK; mem_idx++) begin
      sb_idx = L1_DAISY_CHAIN_MAPPING[mem_idx].sb;
      mb_idx = L1_DAISY_CHAIN_MAPPING[mem_idx].mb;
      m_idx  = L1_DAISY_CHAIN_MAPPING[mem_idx].m;

      inst_mem_impl_inp[sb_idx][mb_idx][m_idx] = daisy_chain_mem_impl_inp[mem_idx];
      daisy_chain_mem_impl_oup[mem_idx] = inst_mem_impl_oup[sb_idx][mb_idx][m_idx];
    end
  end
  // actual chain:
  axe_tcl_sram_cfg #(
    .NUM_SRAMS(L1_NR_SUB_BANKS*L1_NUM_BANKS*L1_MACROS_PER_MINI_BANK)
  ) u_sram_cfg (
    .i_s(i_mem_impl),
    .o_s(o_mem_impl),
    .o_m(daisy_chain_mem_impl_inp),
    .i_m(daisy_chain_mem_impl_oup)
  );

  reg                 [L1_NR_SUB_BANKS-1:0][L1_NUM_BANKS-1:0][SRC_SEL_W-1:0]               src_sel_q;
  reg                 [L1_NR_SUB_BANKS-1:0][L1_NUM_BANKS-1:0]                              src_vld_q;
  reg                 [L1_NR_SUB_BANKS-1:0][TOT_NUM_SOURCES-1:0][MINI_BANK_ADDR_WIDTH-1:0] src_req_addr_q;
  mem_req_t           [L1_NR_SUB_BANKS-1:0][TOT_NUM_SOURCES-1:0]                           src_req_q;
  mem_rsp_t           [L1_NR_SUB_BANKS-1:0][TOT_NUM_SOURCES-1:0]                           src_rsp;
  mmio_dmc_full_rsp_t [NUM_DMC_SOURCES-1:0][L1_NR_SUB_BANKS-1:0]                           prev_dmc_src_rsp;
  mmio_rvv_rsp_t      [NUM_RVV_SOURCES-1:0][L1_NR_SUB_BANKS-1:0]                           prev_rvv_src_rsp;
  mmio_dmc_full_rsp_t [NUM_DMC_SOURCES-1:0][L1_NR_SUB_BANKS-1:0]                           dmc_src_rsp;
  mmio_rvv_rsp_t      [NUM_RVV_SOURCES-1:0][L1_NR_SUB_BANKS-1:0]                           rvv_src_rsp;

  for (genvar sbank = 0; unsigned'(sbank) < L1_NR_SUB_BANKS; sbank++) begin : g_sbank
    l1_sub_bank #(
      .L1_NUM_BANKS(L1_NUM_BANKS),
      .L1_MACROS_PER_MINI_BANK(L1_MACROS_PER_MINI_BANK),
      .TOT_NUM_SOURCES(NUM_DMC_SOURCES + NUM_RVV_SOURCES)
    ) u_sub_bank (
      // Clock and reset signals
      .i_clk  (i_gated_clk),
      .i_rst_n(i_rst_n),

      .i_src_sel     (src_sel_q[sbank]),
      .i_src_vld     (src_vld_q[sbank]),
      .i_src_req_addr(src_req_addr_q[sbank]),
      .i_src_req     (src_req_q[sbank]),
      .o_src_rsp     (src_rsp[sbank]),

      .i_mem_impl (inst_mem_impl_inp[sbank]),
      .o_mem_impl (inst_mem_impl_oup[sbank])
    );

    /////////////////////////////////////////////////////////
    /// Create pipe for src sel:
    for (genvar b = 0; unsigned'(b)<L1_NUM_BANKS; b++) begin : g_sel_pipe
      if (L1_REQ_PIPE) begin : g_add_pipe
        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (i_rst_n == 1'b0) begin
            src_sel_q[sbank][b]  <= '0;
            src_vld_q[sbank][b]  <= '0;
          end else if (i_src_vld[sbank][b] || src_vld_q[sbank][b]) begin
            src_sel_q[sbank][b] <= i_src_sel[sbank][b];
            src_vld_q[sbank][b] <= i_src_vld[sbank][b];
          end
        end
      end else begin : g_no_pipe
        always_comb src_sel_q[sbank][b] = i_src_sel[sbank][b];
        always_comb src_vld_q[sbank][b] = i_src_vld[sbank][b];
      end
    end
    /////////////////////////////////////////////////////////

    /////////////////////////////////////////////////////////
    /// Request wiring, immediately create pipe:
    for (genvar src = 0; unsigned'(src)<NUM_DMC_SOURCES; src++) begin : g_dmc_req_pipe
      if (L1_REQ_PIPE) begin : g_add_pipe
        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (i_rst_n == 1'b0) begin
            src_req_q[sbank][src]       <= '0;
            src_req_addr_q[sbank][src]  <= '0;
          end else if (i_dmc_src_req[src].valid == 1'b1) begin
            src_req_q[sbank][src].valid        <= '0; // don't care, make sure it's not a latch (spyglass...)
            src_req_q[sbank][src].payload.we   <= i_dmc_src_req[src].payload.we;
            src_req_q[sbank][src].payload.wbe  <= i_dmc_src_req[src].payload.wbe[sbank*L1_SUB_BANK_WBE_WIDTH+:L1_SUB_BANK_WBE_WIDTH];
            src_req_q[sbank][src].payload.data <= i_dmc_src_req[src].payload.data[sbank*L1_SUB_BANK_WIDTH+:L1_SUB_BANK_WIDTH];
            src_req_addr_q[sbank][src]         <= i_dmc_src_req[src].payload.addr[ADDR_MINI_BANK_LSB+:MINI_BANK_ADDR_WIDTH];
          end
        end
      end else begin : g_no_pipe
        always_comb src_req_q[sbank][src].valid        = '0; // don't care, make sure it's not a latch (spyglass...)
        always_comb src_req_q[sbank][src].payload.we   = i_dmc_src_req[src].payload.we;
        always_comb src_req_q[sbank][src].payload.wbe  = i_dmc_src_req[src].payload.wbe[sbank*L1_SUB_BANK_WBE_WIDTH+:L1_SUB_BANK_WBE_WIDTH];
        always_comb src_req_q[sbank][src].payload.data = i_dmc_src_req[src].payload.data[sbank*L1_SUB_BANK_WIDTH+:L1_SUB_BANK_WIDTH];
        always_comb src_req_addr_q[sbank][src]         = i_dmc_src_req[src].payload.addr[ADDR_MINI_BANK_LSB+:MINI_BANK_ADDR_WIDTH];
      end
      logic rsp_rdy_nc;
      always_comb rsp_rdy_nc = i_dmc_src_req[src].rsp_ready; // ASO-UNUSED_VARIABLE: memory can't backpressure, thus response ready is not used
    end
    for (genvar src = 0; unsigned'(src)<NUM_RVV_SOURCES; src++) begin : g_rvv_req_pipe
      if (L1_REQ_PIPE) begin : g_add_pipe
        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (i_rst_n == 1'b0) begin
            src_req_q[sbank][src+NUM_DMC_SOURCES]       <= '0;
            src_req_addr_q[sbank][src+NUM_DMC_SOURCES]  <= '0;
          end else if (i_rvv_src_req[src].valid == 1'b1) begin
            src_req_q[sbank][src+NUM_DMC_SOURCES].valid        <= '0; // don't care, make sure it's not a latch (spyglass...)
            src_req_q[sbank][src+NUM_DMC_SOURCES].payload.we   <= i_rvv_src_req[src].payload.we;
            src_req_q[sbank][src+NUM_DMC_SOURCES].payload.wbe  <= i_rvv_src_req[src].payload.wbe;
            src_req_q[sbank][src+NUM_DMC_SOURCES].payload.data <= i_rvv_src_req[src].payload.data;
            src_req_addr_q[sbank][src+NUM_DMC_SOURCES]         <= i_rvv_src_req[src].payload.addr[ADDR_MINI_BANK_LSB+:MINI_BANK_ADDR_WIDTH];
          end
        end
      end else begin : g_no_pipe
        always_comb src_req_q[sbank][src+NUM_DMC_SOURCES].valid        = '0; // don't care, make sure it's not a latch (spyglass...)
        always_comb src_req_q[sbank][src+NUM_DMC_SOURCES].payload.we   = i_rvv_src_req[src].payload.we;
        always_comb src_req_q[sbank][src+NUM_DMC_SOURCES].payload.wbe  = i_rvv_src_req[src].payload.wbe;
        always_comb src_req_q[sbank][src+NUM_DMC_SOURCES].payload.data = i_rvv_src_req[src].payload.data;
        always_comb src_req_addr_q[sbank][src+NUM_DMC_SOURCES]         = i_rvv_src_req[src].payload.addr[ADDR_MINI_BANK_LSB+:MINI_BANK_ADDR_WIDTH];
      end
      logic rsp_rdy_nc;
      always_comb rsp_rdy_nc = i_rvv_src_req[src].rsp_ready; // ASO-UNUSED_VARIABLE: memory can't backpressure, thus response ready is not used
    end
    /////////////////////////////////////////////////////////

    /////////////////////////////////////////////////////////
    /// Response wiring, combine for DMC, select for RVV:
    for (genvar src = 0; unsigned'(src)<NUM_DMC_SOURCES; src++) begin : g_dmc_rsp
      // generate previous response, based on sbank. If first sbank set all to zero
      if (sbank==0) begin : g_prev_data_0
        always_comb prev_dmc_src_rsp[src][sbank].ack = '0;
        always_comb prev_dmc_src_rsp[src][sbank].payload.data = '0;
      end else begin : g_prev_data_non_0
        always_comb prev_dmc_src_rsp[src][sbank].ack = dmc_src_rsp[src][sbank-1].ack;
        always_comb prev_dmc_src_rsp[src][sbank].payload.data = dmc_src_rsp[src][sbank-1].payload.data;
      end

      // orr reponse valid
      always_comb dmc_src_rsp[src][sbank].ack = src_rsp[sbank][src].valid | prev_dmc_src_rsp[src][sbank].ack;

      // combine response with previous one, don't care about valid
      always_comb begin
        for (uint_t sb = 0; sb < L1_NR_SUB_BANKS; sb++) begin
          // set to resp for this sbank, else previous one
          dmc_src_rsp[src][sbank].payload.data[sb*L1_SUB_BANK_WIDTH+:L1_SUB_BANK_WIDTH] = (sb==sbank) ?
                                        src_rsp[sbank][src].data :
                                         prev_dmc_src_rsp[src][sbank].payload.data[sb*L1_SUB_BANK_WIDTH+:L1_SUB_BANK_WIDTH];
        end
      end
    end

    for (genvar src = 0; unsigned'(src)<NUM_RVV_SOURCES; src++) begin : g_rvv_rsp
      // generate previous response, based on sbank. If first sbank set all to zero
      if (sbank==0) begin : g_prev_data_0
        always_comb prev_rvv_src_rsp[src][sbank].ack = '0;
        always_comb prev_rvv_src_rsp[src][sbank].payload.data = '0;
      end else begin : g_prev_data_non_0
        always_comb prev_rvv_src_rsp[src][sbank].ack = rvv_src_rsp[src][sbank-1].ack;
        always_comb prev_rvv_src_rsp[src][sbank].payload.data = rvv_src_rsp[src][sbank-1].payload.data;
      end

      // orr reponse valid
      always_comb rvv_src_rsp[src][sbank].ack = src_rsp[sbank][src+NUM_DMC_SOURCES].valid | prev_rvv_src_rsp[src][sbank].ack;

      // take this response data when valid, else previous sbank
      always_comb begin
        if (src_rsp[sbank][src+NUM_DMC_SOURCES].valid)
          rvv_src_rsp[src][sbank].payload.data = src_rsp[sbank][src+NUM_DMC_SOURCES].data;
        else
          rvv_src_rsp[src][sbank].payload.data = prev_rvv_src_rsp[src][sbank].payload.data;
      end
    end
  end : g_sbank

  for (genvar src = 0; unsigned'(src)<NUM_DMC_SOURCES; src++) begin : g_dmc_rsp_outp
    always_comb o_dmc_src_rsp[src].ack          = dmc_src_rsp[src][L1_NR_SUB_BANKS-1].ack;
    always_comb o_dmc_src_rsp[src].payload.data = dmc_src_rsp[src][L1_NR_SUB_BANKS-1].payload.data;
  end
  for (genvar src = 0; unsigned'(src)<NUM_RVV_SOURCES; src++) begin : g_rvv_rsp_outp
    always_comb o_rvv_src_rsp[src].ack          = rvv_src_rsp[src][L1_NR_SUB_BANKS-1].ack;
    always_comb o_rvv_src_rsp[src].payload.data = rvv_src_rsp[src][L1_NR_SUB_BANKS-1].payload.data;
  end
  /////////////////////////////////////////////////////////

endmodule
