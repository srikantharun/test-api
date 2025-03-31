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
  input  logic     ${cfg['ext_resets']},
  /// different "full reset" sources for every stage
  % for c in cfg['stages']:
    % for r in c['resets']:
      % if r:
  input  logic ${r}i,
      % endif
    % endfor
  % endfor
  % for c in cfg['stages']:
  /// consistently reset request from particular stage
  input  logic ${c['name']}_req_ni,
  /// reset ack for particular stage
  output logic ${c['name']}_ack_no,
  /// rst ack for particular IP
    % if c['num_ips']>1:
  input  logic [${c['num_ips']-1}:0] ${c['name']}_ip_ack_i,
  /// rst strobe for particular IP
  output logic [${c['num_ips']-1}:0] ${c['name']}_ip_no,
    % else:
  input  logic ${c['name']}_ip_ack_i,
  /// rst strobe for particular IP
  output logic ${c['name']}_ip_no,
    %endif
  % endfor
  /// force rst request for particular IP (* unused *)
  // input  logic [TOTAL_RST_IP_NUM-1:0] rst_ip_force_i,
  input  apb_h2d_t apb_i,
  output apb_d2h_t apb_o
 );

  reset_gen_reg_pkg::reset_gen_reg2hw_t reg2hw;
  reset_gen_reg_pkg::reset_gen_hw2reg_t hw2reg;

  logic hw_rst_ni_dbnc;
  logic pcie_button_rst_ni_dbnc;
  logic [${len(cfg['stages'])-1}:0] rst_stage;
  logic [${cfg['resets']-1}:0] rst_src_ni;
  <% rst_cnt = 0 %>
  % for i, c in enumerate(cfg['stages']):
    % if c['num_ips']>1:
  logic [${c['num_ips']-1}:0] ${c['name']}_ip_n;
  logic ${c['name']};
    % else:
  logic ${c['name']}_ip_n, ${c['name']};
    %endif

  assign ${c['name']} = &{${f"rst_stage[{i-1}]" if i > 0 else "por_rst_ni, hw_rst_ni_dbnc"}\
% if len(c.get('resets', [])):
,\
 ${", ".join(r + 'i' for i in [c['resets']])}\
% endif
};
    % if i == 0:
  assign rst_src_ni = {${cfg['ext_resets']}};
    % endif

  reset_gen_basic_block #(
    .RST_SRC_NUM (${cfg['resets']}),
    .RST_IP_NUM (${c['num_ips']}),
    .RST_STRETCH_USE (${int(c.get('stretch', True))})
  ) i_reset_gen_basic_block_${c['name']} (
    .test_i (test_i),
    .clk_i (clk_i),
    .test_rst_ni(por_rst_ni),
    .rst_ni (${c['name']}),
    .rst_no (rst_stage[${i}]),
    .rst_req_ni (${c['name']}_req_ni),
    .rst_ack_no (${c['name']}_ack_no),
    % if i == 0:
    .rst_stretch_i (12'h14), // min reset duration should be 1us for PLL in clkgen. 
    .rst_src_ni (3'b111),
    .rst_src_mask_i ('0),
    % elif i == 1:
    .rst_stretch_i (reg2hw.rst_cfg_${c['name']}.rst_stretch.q),
    .rst_src_ni ({tamper_rst_ni, 2'b11}),
    .rst_src_mask_i (reg2hw.rst_cfg_${c['name']}.rst_src_mask.q),
    % else:
    .rst_stretch_i (reg2hw.rst_cfg_${c['name']}.rst_stretch.q),
    .rst_src_ni (rst_src_ni),
    .rst_src_mask_i (reg2hw.rst_cfg_${c['name']}.rst_src_mask.q),
    % endif
    %if c['name'] == "pcie_rst":
    .rst_ip_sw_ni (reg2hw.rst_sw_${c['name']}.q),
    %elif c['name'] == "ddr_rst":
    .rst_ip_sw_ni (reg2hw.rst_sw_${c['name']}.q),
    %elif c['name'] == "ai_core_rst":
    .rst_ip_sw_ni (reg2hw.rst_sw_${c['name']}.q),
    % else:
    .rst_ip_sw_ni ('1),
    % endif
    .rst_ip_no (${c['name']}_ip_n),
    % if c['name'] == "dmi_rst":
    .rst_ip_force_i (~dmi_rst_ni),
    % elif c['name'] == "pcie_rst":
    .rst_ip_force_i ({1'b0, 1'b0, ~pcie_button_rst_ni_dbnc}),
    % else:
    .rst_ip_force_i ('0),
    % endif
    .rst_ip_ack_i (${c['name']}_ip_ack_i)
);

    % if c['num_ips']>1:
  assign ${c['name']}_ip_no = dft_clk_rst_ctrl ? rst_test_ni[ ${rst_cnt} + ${c['num_ips']}-1:${rst_cnt} ] : ${c['name']}_ip_n;
    <% rst_cnt = rst_cnt + c['num_ips'] %>
    % else:
  assign ${c['name']}_ip_no = dft_clk_rst_ctrl ? rst_test_ni[${rst_cnt}] : ${c['name']}_ip_n;
    <% rst_cnt = rst_cnt+1 %>
    %endif
  % endfor

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
