// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

`ifndef RESET_GEN_BASIC_BLOCK_GUARD
`define RESET_GEN_BASIC_BLOCK_GUARD

module reset_gen_basic_block #(
    parameter int unsigned      STAGE_NUM       = 3,
    parameter int unsigned      RST_SRC_NUM     = 2,
    parameter bit [3:0]         RST_IP_NUM      = 4'h4,
    parameter int unsigned      RST_STRETCH_USE = 1'b0
) (
    input  logic i_test_mode,
    input  wire  i_clk,
    input  wire  i_test_rst_n,
    // Input reset stretch value
    input  logic [11:0] i_stretch_cycles,  // reset de-assertion delay
    input  wire  i_rst_n,  // broadcast simult rst for all IP in stage
    output wire  o_rst_n,  // reset to next stage
    // Per-stage reset request/acknowledgement signals
    input  wire  i_rst_req_n,  // stage simult rst for all IP in stage
    output logic o_rst_ack_n,  // ack that all rst done for this stage
    // Input hardware source resets
    input  wire  [RST_SRC_NUM-1:0] i_rst_src_n,  // simult rst from different hw sources
    input  logic [RST_SRC_NUM-1:0] i_mask_reset_src, // mask(from reg_bank) for different hw rst sources
    // Input IP reset force signals
    input  wire  [RST_IP_NUM-1:0] i_rst_ip_force,  // hard reset for particular IP in stage
    // Input IP SW reset signals
    input  wire  [RST_IP_NUM-1:0] i_rst_ip_sw_n,  // sw reset assertion for each IP in stage
    // Output IP reset & reset acks signals
    input  logic [RST_IP_NUM-1:0] i_ack_reset_ip,  // input ack from particular IP in stage
    output wire  [RST_IP_NUM-1:0] o_rst_ip_n  // output reset for particular IP in stage
);

  wire rst_stage_n, rst_stage_in_n;
  assign rst_stage_in_n = &{i_rst_n, i_rst_req_n, (i_rst_src_n | i_mask_reset_src)};

  logic        stretcher_cnt_en;
  // Stretcher logic
  if (RST_STRETCH_USE == 1'b1) begin : gen_rst_stretcher_exist
    wire         rst_sync_n;
    logic [11:0] stretch_cnt;
    wire         rst_sync_pretest_n;

    // synced resets generation
    axe_ccl_rst_n_sync #(
      .SyncStages (STAGE_NUM)
    ) u_axe_ccl_rst_n_sync (
      .i_test_mode ( i_test_mode        ),
      .i_rst_n     ( rst_stage_in_n     ),
      .i_clk       ( i_clk              ),
      .o_rst_n     ( rst_sync_pretest_n )
    );

    axe_tcl_clk_mux2 u_dft_mux (
      .i_clk0 ( rst_sync_pretest_n ),
      .i_clk1 ( i_test_rst_n       ),
      .i_sel  ( i_test_mode        ),
      .o_clk  ( rst_sync_n         )
    );

    always_ff @(posedge i_clk, negedge rst_sync_n)
      if (!rst_sync_n) stretcher_cnt_en <= 1'b1;
      else if (stretch_cnt == i_stretch_cycles) stretcher_cnt_en <= 1'b0;

    always_ff @(posedge i_clk, negedge rst_sync_n)
      if (!rst_sync_n) stretch_cnt <= 12'h0;
      else if (stretcher_cnt_en) stretch_cnt <= stretch_cnt + 12'h1;

    assign rst_stage_n = (i_stretch_cycles == 12'b0) ? rst_stage_in_n : ~stretcher_cnt_en;

  // No stretcher logic
  end else begin : gen_rst_stretcher_nonexist
    assign rst_stage_n = rst_stage_in_n;
  end

  // IP resets forming
  for (genvar ip_num = 0; ip_num < RST_IP_NUM; ip_num++) begin : g_rst_ip_num_
    assign o_rst_ip_n[ip_num] = &{rst_stage_n, i_rst_ip_sw_n[ip_num], !i_rst_ip_force[ip_num]};
  end

  assign o_rst_ack_n = !(&i_ack_reset_ip);
  assign o_rst_n = !(!rst_stage_n || (&i_ack_reset_ip));

endmodule

`endif  // RESET_GEN_BASIC_BLOCK_GUARD
