// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

`ifndef RESET_GEN
`define RESET_GEN

 module reset_gen import reset_gen_reg_pkg::*; #(
  parameter int unsigned NUM_RESETS_RSTGEN = 14,
  parameter int unsigned STAGE_NUM = 3
) (
  input  logic     clk_i,
  input  logic     por_rst_ni,
  input  logic     hw_rst_ni,
  input  logic     pcie_button_rst_ni,
  input  logic     test_i,
  input  logic     dft_clk_rst_ctrl,
  input  logic [NUM_RESETS_RSTGEN-1:0]    rst_test_ni,
  input  logic     pclk_i,
  input  logic     prst_ni,
  input  logic     hw_rst_sync_periph,
  input  logic     dmi_rst_ni,
  input  logic     tamper_rst_ni, ndm_rst_ni, wdt_rst_ni,
  /// different "full reset" sources for every stage
  /// consistently reset request from particular stage
  input  logic hw_rst_req_ni,
  /// reset ack for particular stage
  output logic hw_rst_ack_no,
  /// rst ack for particular IP
  input  logic hw_rst_ip_ack_i,
  /// rst strobe for particular IP
  output logic hw_rst_ip_no,
  /// consistently reset request from particular stage
  input  logic dmi_rst_req_ni,
  /// reset ack for particular stage
  output logic dmi_rst_ack_no,
  /// rst ack for particular IP
  input  logic dmi_rst_ip_ack_i,
  /// rst strobe for particular IP
  output logic dmi_rst_ip_no,
  /// consistently reset request from particular stage
  input  logic bus_rst_asyn_req_ni,
  /// reset ack for particular stage
  output logic bus_rst_asyn_ack_no,
  /// rst ack for particular IP
  input  logic bus_rst_asyn_ip_ack_i,
  /// rst strobe for particular IP
  output logic bus_rst_asyn_ip_no,
  /// consistently reset request from particular stage
  input  logic sys_core_rst_req_ni,
  /// reset ack for particular stage
  output logic sys_core_rst_ack_no,
  /// rst ack for particular IP
  input  logic sys_core_rst_ip_ack_i,
  /// rst strobe for particular IP
  output logic sys_core_rst_ip_no,
  /// consistently reset request from particular stage
  input  logic ai_core_rst_req_ni,
  /// reset ack for particular stage
  output logic ai_core_rst_ack_no,
  /// rst ack for particular IP
  input  logic ai_core_rst_ip_ack_i,
  /// rst strobe for particular IP
  output logic ai_core_rst_ip_no,
  /// consistently reset request from particular stage
  input  logic pcie_rst_req_ni,
  /// reset ack for particular stage
  output logic pcie_rst_ack_no,
  /// rst ack for particular IP
  input  logic [2:0] pcie_rst_ip_ack_i,
  /// rst strobe for particular IP
  output logic [2:0] pcie_rst_ip_no,
  /// consistently reset request from particular stage
  input  logic ddr_rst_req_ni,
  /// reset ack for particular stage
  output logic ddr_rst_ack_no,
  /// rst ack for particular IP
  input  logic [5:0] ddr_rst_ip_ack_i,
  /// rst strobe for particular IP
  output logic [5:0] ddr_rst_ip_no,
  /// force rst request for particular IP (* unused *)
  // input  logic [TOTAL_RST_IP_NUM-1:0] rst_ip_force_i,
  input  apb_h2d_t apb_i,
  output apb_d2h_t apb_o
 );

  reset_gen_reg_pkg::reset_gen_reg2hw_t reg2hw;
  reset_gen_reg_pkg::reset_gen_hw2reg_t hw2reg;

  logic hw_rst_ni_dbnc;
  logic pcie_button_rst_ni_dbnc;
  logic [6:0] rst_stage;
  logic [2:0] rst_src_ni;
  
  logic hw_rst_ip_n, hw_rst;

  assign hw_rst = &{por_rst_ni, hw_rst_ni_dbnc};
  assign rst_src_ni = {tamper_rst_ni, ndm_rst_ni, wdt_rst_ni};

  reset_gen_basic_block #(
    .RST_SRC_NUM (3),
    .RST_IP_NUM (1),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_hw_rst (
    .test_i (test_i),
    .clk_i (clk_i),
    .test_rst_ni(por_rst_ni),
    .rst_ni (hw_rst),
    .rst_no (rst_stage[0]),
    .rst_req_ni (hw_rst_req_ni),
    .rst_ack_no (hw_rst_ack_no),
    .rst_stretch_i (12'h14), // min reset duration should be 1us for PLL in clkgen. 
    .rst_src_ni (3'b111),
    .rst_src_mask_i ('0),
    .rst_ip_sw_ni ('1),
    .rst_ip_no (hw_rst_ip_n),
    .rst_ip_force_i ('0),
    .rst_ip_ack_i (hw_rst_ip_ack_i)
);

  assign hw_rst_ip_no = dft_clk_rst_ctrl ? rst_test_ni[0] : hw_rst_ip_n;
    
  logic dmi_rst_ip_n, dmi_rst;

  assign dmi_rst = &{rst_stage[0]};

  reset_gen_basic_block #(
    .RST_SRC_NUM (3),
    .RST_IP_NUM (1),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_dmi_rst (
    .test_i (test_i),
    .clk_i (clk_i),
    .test_rst_ni(por_rst_ni),
    .rst_ni (dmi_rst),
    .rst_no (rst_stage[1]),
    .rst_req_ni (dmi_rst_req_ni),
    .rst_ack_no (dmi_rst_ack_no),
    .rst_stretch_i (reg2hw.rst_cfg_dmi_rst.rst_stretch.q),
    .rst_src_ni ({tamper_rst_ni, 2'b11}),
    .rst_src_mask_i (reg2hw.rst_cfg_dmi_rst.rst_src_mask.q),
    .rst_ip_sw_ni ('1),
    .rst_ip_no (dmi_rst_ip_n),
    .rst_ip_force_i (~dmi_rst_ni),
    .rst_ip_ack_i (dmi_rst_ip_ack_i)
);

  assign dmi_rst_ip_no = dft_clk_rst_ctrl ? rst_test_ni[1] : dmi_rst_ip_n;
    
  logic bus_rst_asyn_ip_n, bus_rst_asyn;

  assign bus_rst_asyn = &{rst_stage[1]};

  reset_gen_basic_block #(
    .RST_SRC_NUM (3),
    .RST_IP_NUM (1),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_bus_rst_asyn (
    .test_i (test_i),
    .clk_i (clk_i),
    .test_rst_ni(por_rst_ni),
    .rst_ni (bus_rst_asyn),
    .rst_no (rst_stage[2]),
    .rst_req_ni (bus_rst_asyn_req_ni),
    .rst_ack_no (bus_rst_asyn_ack_no),
    .rst_stretch_i (reg2hw.rst_cfg_bus_rst_asyn.rst_stretch.q),
    .rst_src_ni (rst_src_ni),
    .rst_src_mask_i (reg2hw.rst_cfg_bus_rst_asyn.rst_src_mask.q),
    .rst_ip_sw_ni ('1),
    .rst_ip_no (bus_rst_asyn_ip_n),
    .rst_ip_force_i ('0),
    .rst_ip_ack_i (bus_rst_asyn_ip_ack_i)
);

  assign bus_rst_asyn_ip_no = dft_clk_rst_ctrl ? rst_test_ni[2] : bus_rst_asyn_ip_n;
    
  logic sys_core_rst_ip_n, sys_core_rst;

  assign sys_core_rst = &{rst_stage[2]};

  reset_gen_basic_block #(
    .RST_SRC_NUM (3),
    .RST_IP_NUM (1),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_sys_core_rst (
    .test_i (test_i),
    .clk_i (clk_i),
    .test_rst_ni(por_rst_ni),
    .rst_ni (sys_core_rst),
    .rst_no (rst_stage[3]),
    .rst_req_ni (sys_core_rst_req_ni),
    .rst_ack_no (sys_core_rst_ack_no),
    .rst_stretch_i (reg2hw.rst_cfg_sys_core_rst.rst_stretch.q),
    .rst_src_ni (rst_src_ni),
    .rst_src_mask_i (reg2hw.rst_cfg_sys_core_rst.rst_src_mask.q),
    .rst_ip_sw_ni ('1),
    .rst_ip_no (sys_core_rst_ip_n),
    .rst_ip_force_i ('0),
    .rst_ip_ack_i (sys_core_rst_ip_ack_i)
);

  assign sys_core_rst_ip_no = dft_clk_rst_ctrl ? rst_test_ni[3] : sys_core_rst_ip_n;
    
  logic ai_core_rst_ip_n, ai_core_rst;

  assign ai_core_rst = &{rst_stage[3]};

  reset_gen_basic_block #(
    .RST_SRC_NUM (3),
    .RST_IP_NUM (1),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_ai_core_rst (
    .test_i (test_i),
    .clk_i (clk_i),
    .test_rst_ni(por_rst_ni),
    .rst_ni (ai_core_rst),
    .rst_no (rst_stage[4]),
    .rst_req_ni (ai_core_rst_req_ni),
    .rst_ack_no (ai_core_rst_ack_no),
    .rst_stretch_i (reg2hw.rst_cfg_ai_core_rst.rst_stretch.q),
    .rst_src_ni (rst_src_ni),
    .rst_src_mask_i (reg2hw.rst_cfg_ai_core_rst.rst_src_mask.q),
    .rst_ip_sw_ni (reg2hw.rst_sw_ai_core_rst.q),
    .rst_ip_no (ai_core_rst_ip_n),
    .rst_ip_force_i ('0),
    .rst_ip_ack_i (ai_core_rst_ip_ack_i)
);

  assign ai_core_rst_ip_no = dft_clk_rst_ctrl ? rst_test_ni[4] : ai_core_rst_ip_n;
    
  logic [2:0] pcie_rst_ip_n;
  logic pcie_rst;

  assign pcie_rst = &{rst_stage[4]};

  reset_gen_basic_block #(
    .RST_SRC_NUM (3),
    .RST_IP_NUM (3),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_pcie_rst (
    .test_i (test_i),
    .clk_i (clk_i),
    .test_rst_ni(por_rst_ni),
    .rst_ni (pcie_rst),
    .rst_no (rst_stage[5]),
    .rst_req_ni (pcie_rst_req_ni),
    .rst_ack_no (pcie_rst_ack_no),
    .rst_stretch_i (reg2hw.rst_cfg_pcie_rst.rst_stretch.q),
    .rst_src_ni (rst_src_ni),
    .rst_src_mask_i (reg2hw.rst_cfg_pcie_rst.rst_src_mask.q),
    .rst_ip_sw_ni (reg2hw.rst_sw_pcie_rst.q),
    .rst_ip_no (pcie_rst_ip_n),
    .rst_ip_force_i ({1'b0, 1'b0, ~pcie_button_rst_ni_dbnc}),
    .rst_ip_ack_i (pcie_rst_ip_ack_i)
);

  assign pcie_rst_ip_no = dft_clk_rst_ctrl ? rst_test_ni[ 5 + 3-1:5 ] : pcie_rst_ip_n;
    
  logic [5:0] ddr_rst_ip_n;
  logic ddr_rst;

  assign ddr_rst = &{rst_stage[5]};

  reset_gen_basic_block #(
    .RST_SRC_NUM (3),
    .RST_IP_NUM (6),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_ddr_rst (
    .test_i (test_i),
    .clk_i (clk_i),
    .test_rst_ni(por_rst_ni),
    .rst_ni (ddr_rst),
    .rst_no (rst_stage[6]),
    .rst_req_ni (ddr_rst_req_ni),
    .rst_ack_no (ddr_rst_ack_no),
    .rst_stretch_i (reg2hw.rst_cfg_ddr_rst.rst_stretch.q),
    .rst_src_ni (rst_src_ni),
    .rst_src_mask_i (reg2hw.rst_cfg_ddr_rst.rst_src_mask.q),
    .rst_ip_sw_ni (reg2hw.rst_sw_ddr_rst.q),
    .rst_ip_no (ddr_rst_ip_n),
    .rst_ip_force_i ('0),
    .rst_ip_ack_i (ddr_rst_ip_ack_i)
);

  assign ddr_rst_ip_no = dft_clk_rst_ctrl ? rst_test_ni[ 8 + 6-1:8 ] : ddr_rst_ip_n;
    

  reset_gen_reg_top #(
    .StageNum (STAGE_NUM)
  ) i_reset_gen_reg_top (
    .clk_i (pclk_i),
    .rst_ni (hw_rst_sync_periph),
    .apb_i,
    .apb_o,
    .reg2hw (reg2hw),
    .hw2reg (hw2reg),
    .devmode_i (1'b1)
  );

  logic por_rst_n_sync;
  // synchronize the por_rst_ni to the input clock domain since the por_rst_ni is fully asynchronous. 
  reset_sync #(
    .RESET_DELAY(0),
    .STAGE_NUM  (2)
  ) i_reset_sync_por (
    .test_i (test_i),
    .s_rst_ni (por_rst_ni),
    .d_clk_i (clk_i),
    .d_rst_no (por_rst_n_sync)
  );

  logic por_rst_n_sync_periph;
  // synchronize the por_rst_ni to the input clock domain since the por_rst_ni is fully asynchronous. 
  reset_sync #(
    .RESET_DELAY(0),
    .STAGE_NUM  (2)
  ) i_reset_sync_por_periph (
    .test_i (test_i),
    .s_rst_ni (por_rst_ni),
    .d_clk_i (pclk_i),
    .d_rst_no (por_rst_n_sync_periph)
  );

  logic [31:0] dbnc_timer_val;
  logic [31:0] dbnc_timer_pcie_btn_val;
  // instantiation of the reset debounce module for the input button reset (hw_rst_ni)
  signal_debounce i_signal_debounce (
    .clk_i(clk_i),
    .por_rst_n_sync_i(por_rst_n_sync),
    .inp_sig_ni(hw_rst_ni),

    .dbnc_timer_val_i(dbnc_timer_val),
    .inp_sig_dbncd_no(hw_rst_ni_dbnc),

    .test_mode_i(test_i)
  );

  // instantiation of the reset debounce module for the input pcie button reset (hw_rst_ni)
  signal_debounce i_signal_debounce_pcie_btn (
    .clk_i(clk_i),
    .por_rst_n_sync_i(por_rst_n_sync),
    .inp_sig_ni(pcie_button_rst_ni),

    .dbnc_timer_val_i(dbnc_timer_pcie_btn_val),
    .inp_sig_dbncd_no(pcie_button_rst_ni_dbnc),

    .test_mode_i(test_i)
  );

  // Instantiation of the "hwext" reset debounce timer register since it has a different reset to the other registers in the reset_gen register block. 
  always_ff @(posedge pclk_i or negedge por_rst_n_sync_periph) begin
    if (~por_rst_n_sync_periph)
      dbnc_timer_val <= RESET_GEN_DBNC_TIMER_RESVAL;
    else if (reg2hw.dbnc_timer.qe)
      dbnc_timer_val <= reg2hw.dbnc_timer.q;
  end
    assign hw2reg.dbnc_timer.d = dbnc_timer_val;

  // Instantiation of the "hwext" reset debounce timer register for the pcie button reset since it has a different reset to the other registers in the reset_gen register block. 
  always_ff @(posedge pclk_i or negedge por_rst_n_sync_periph) begin
    if (~por_rst_n_sync_periph)
      dbnc_timer_pcie_btn_val <= RESET_GEN_DBNC_TIMER_PCIE_BTN_RST_RESVAL;
    else if (reg2hw.dbnc_timer_pcie_btn_rst.qe)
      dbnc_timer_pcie_btn_val <= reg2hw.dbnc_timer_pcie_btn_rst.q;
  end
    assign hw2reg.dbnc_timer_pcie_btn_rst.d = dbnc_timer_pcie_btn_val;

 endmodule

`endif

