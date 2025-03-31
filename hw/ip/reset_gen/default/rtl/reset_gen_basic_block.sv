// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

`ifndef RESET_GEN_BASIC_BLOCK_GUARD
`define RESET_GEN_BASIC_BLOCK_GUARD

module reset_gen_basic_block #(
    parameter       STAGE_NUM       = 3,
    parameter       RST_SRC_NUM     = 2,
    parameter [3:0] RST_IP_NUM      = 4'h4,
    parameter       RST_STRETCH_USE = 1'b0
) (
    input logic test_i,
    input logic clk_i,
    input logic test_rst_ni,
    // Input reset stretch value
    input logic [11:0] rst_stretch_i,  // reset de-assertion delay
    input logic rst_ni,  // broadcast simult rst for all IP in stage
    output logic rst_no,  // reset to next stage
    // Per-stage reset request/acknowledgement signals
    input logic rst_req_ni,  // stage simult rst for all IP in stage
    output logic rst_ack_no,  // ack that all rst done for this stage
    // Input hardware source resets
    input logic [RST_SRC_NUM-1:0] rst_src_ni,  // simult rst from different hw sources
    input  logic [RST_SRC_NUM-1:0] rst_src_mask_i, // mask(from reg_bank) for different hw rst soures
    // Input IP reset force signals
    input logic [RST_IP_NUM-1:0] rst_ip_force_i,  // hard reset for particular IP in stage
    // Input IP SW reset signals
    input logic [RST_IP_NUM-1:0] rst_ip_sw_ni,  // sw reset assertion for each IP in stage
    // Output IP reset & reset acks signals
    input logic [RST_IP_NUM-1:0] rst_ip_ack_i,  // input ack from particular IP in stage
    output logic [RST_IP_NUM-1:0] rst_ip_no  // output reset for particular IP in stage
);

  logic rst_stage_n, rst_stage_in_n;
  assign rst_stage_in_n = &{rst_ni, rst_req_ni, (rst_src_ni | rst_src_mask_i)};

  logic        stretcher_cnt_en;
  // Stretcher logic
  if (RST_STRETCH_USE == 1'b1) begin : gen_rst_stretcher_exist
    logic        rst_sync_n;
    logic [11:0] rst_stretcher_cnt;
    logic        rst_sync_pretest_n;

    // synced resets generation
    reset_sync #(
      .RESET_DELAY(0),
      .STAGE_NUM  (STAGE_NUM)
    ) reset_sync (
      .test_i (test_i),
      .s_rst_ni (rst_stage_in_n),
      .d_clk_i (clk_i),
      .d_rst_no (rst_sync_pretest_n)
    );

    always_comb rst_sync_n = test_i ? test_rst_ni : rst_sync_pretest_n;

    always_ff @(posedge clk_i, negedge rst_sync_n)
      if (!rst_sync_n) stretcher_cnt_en <= 1'b1;
      else if (rst_stretcher_cnt == rst_stretch_i) stretcher_cnt_en <= 1'b0;

    always_ff @(posedge clk_i, negedge rst_sync_n)
      if (!rst_sync_n) rst_stretcher_cnt <= 12'h0;
      else if (stretcher_cnt_en) rst_stretcher_cnt <= rst_stretcher_cnt + 12'h1;

    assign rst_stage_n = (rst_stretch_i == 12'b0) ? rst_stage_in_n : ~stretcher_cnt_en;

  // No stretcher logic
  end else begin : gen_rst_stretcher_nonexist
    assign rst_stage_n = rst_stage_in_n;
  end

  // IP resets forming
  for (genvar ip_num = 0; ip_num < RST_IP_NUM; ip_num++) begin : rst_ip_num_
    assign rst_ip_no[ip_num] = &{rst_stage_n, rst_ip_sw_ni[ip_num], !rst_ip_force_i[ip_num]};
  end

  assign rst_ack_no = !(&rst_ip_ack_i);
  assign rst_no = !(!rst_stage_n || (&rst_ip_ack_i));

endmodule

`endif  // RESET_GEN_BASIC_BLOCK_GUARD
