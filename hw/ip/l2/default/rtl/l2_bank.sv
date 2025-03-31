// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L2 Bank
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_BANK_SV
`define L2_BANK_SV

module l2_bank
  import l2_pkg::*;
  import l2_cfg_pkg::*;
  (
    // Clock signal
    input  wire                                                             i_clk,
    input  wire                                                             i_rst_n,
    // RAM interface signals
    input  l2_bank_req_t                                                    i_bank_req,
    output l2_ram_rsp_t                                                     o_bank_rsp,

    // SRAM configuration
    input  axe_tcl_sram_pkg::impl_inp_t [L2_NUM_RAMS-1:0][L2_NUM_SRAMS-1:0] i_impl,
    output axe_tcl_sram_pkg::impl_oup_t [L2_NUM_RAMS-1:0][L2_NUM_SRAMS-1:0] o_impl
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

  l2_bank_req_t                                  bank_req_q;
  l2_ram_rsp_t                                   bank_rsp_d;
  l2_ram_rsp_t                                   bank_rsp_q;
  logic                       [ L2_NUM_RAMS-1:0] inst_prn;
  logic                       [ L2_NUM_RAMS-1:0] inst_pde;
  l2_ram_req_t                [ L2_NUM_RAMS-1:0] ram_req;
  l2_ram_rsp_t                [ L2_NUM_RAMS-1:0] ram_rsp;
  logic                                          shift_en;

  // =====================================================
  // RTL
  // =====================================================

  /// Add input pipeline register when it is enabled
  /// Depth is 0 when L2_PIPELINE_IN_ENABLE=0
  cc_cnt_shift_reg #(
    .data_t(l2_bank_t),
    .Stages(1)
  ) u_shift_mem_req (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_clear  (1'b0),
    .i_stall  (1'b0),
    .i_data   (i_bank_req.bank),
    .i_data_en(i_bank_req.ce),
    .o_data   (bank_req_q.bank),
    .o_updated(bank_req_q.ce)
  );

  /// @selecting_ram_comb_proc
  /// Demux the bank information into the ram
  always_comb begin : selecting_ram_comb_proc
    foreach (ram_req[ram]) begin
      ram_req[ram] = bank_req_q.ce ? '{
        ce: bank_req_q.ce && (bank_req_q.bank.addr.ram == ram),
        ram: '{
          addr: bank_req_q.bank.addr.sram,
          we: bank_req_q.bank.we,
          wbe: bank_req_q.bank.wbe,
          data: bank_req_q.bank.data
        }
      } : '0;
    end
  end

  for (genvar ram = 0; ram < L2_NUM_RAMS; ram++) begin : g_ram
  l2_ram u_l2_ram (
    // Clock signal
    .i_clk   (i_clk),
    .i_rst_n (i_rst_n),
    // RAM interface signals
    .i_ram_req(ram_req[ram]),
    .o_ram_rsp(ram_rsp[ram]),
    // Memory configutation pins
    .i_impl (i_impl[ram]),
    .o_impl (o_impl[ram])
  );
  end

  /// @combine_ram_rsp_comb_proc
  /// Combine the responses from all rams into one
  always_comb begin : combine_ram_rsp_comb_proc
    bank_rsp_d = 0;
    foreach (ram_rsp[ram]) begin
      bank_rsp_d.data |= ram_rsp[ram].data;
      bank_rsp_d.valid |= ram_rsp[ram].valid;
    end
  end

  /// @shift_enable_seq_proc
  /// Keep shift enable to send data and clean it
  always_ff @( posedge i_clk, negedge i_rst_n ) begin : shift_enable_seq_proc
    if      (~i_rst_n)                    shift_en <= 1'b0;
    else if (bank_rsp_d.valid ^ shift_en) shift_en <= bank_rsp_d.valid;
  end

  // Add output pipeline register when it is enabled
  // Depth is 0 when L2_PIPELINE_OUT_ENABLE=0
  cc_cnt_shift_reg #(
    .data_t(l2_ram_rsp_t),
    .Stages(1)
  ) u_shift_ram_rsp (
    .i_clk,
    .i_rst_n,
    .i_clear  (1'b0),
    .i_stall  (1'b0),
    .i_data   (bank_rsp_d),
    .i_data_en(bank_rsp_d.valid | shift_en),
    .o_data   (bank_rsp_q),
    .o_updated(/* NC */) // ASO-UNUSED_OUTPUT: Only data_en and out updated are used
  );

  /// @bank_rsp_comb_proc
  /// Generates the bank response
  always_comb begin : bank_rsp_comb_proc
    o_bank_rsp = '{
                   valid: bank_rsp_q.valid
                  ,data: bank_rsp_q.data
                  };
  end

endmodule

`endif  // L2_BANK_SV
