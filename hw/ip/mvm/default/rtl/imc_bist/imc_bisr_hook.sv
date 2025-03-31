// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Deserialize and decompress for IMC repair data
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module imc_bisr_hook
  import imc_bist_pkg::compressed_repair_t;
  import imc_bist_pkg::uncompressed_repair_t;
(
  input  wire                  i_clk,
  input  wire                  i_rst_n,

  /// i_mux_mode == 0: Repair settings are fed from IMC BIRA controller
  /// i_mux_mode == 1: Repair settings are fed from eFuse
  input  logic                 i_mux_mode,
  input  logic                 i_imc_bisr_shift_en,
  input  logic                 i_imc_bisr_ue,
  input  logic                 i_imc_bisr_si,
  output logic                 o_mux_mode,
  output logic                 o_imc_bisr_shift_en,
  output logic                 o_imc_bisr_ue,
  output logic                 o_imc_bisr_so,

  output logic                 o_update_repair_setting,
  output compressed_repair_t   o_compressed_repair_setting,
  output uncompressed_repair_t o_repair_setting
);

  logic [$bits(compressed_repair_t)-1:0] shift_en_shift_reg, ue_shift_reg;
  compressed_repair_t r_repair_settings, r_updated_repair_settings;
  uncompressed_repair_t s_uncompressed_repair_settings;
  logic r_imc_bisr_shift_en;
  logic r_imc_bisr_ue;
  logic [31:0] s_onehot_repair_setting;

  logic [1:0] off_reset_detect;
  logic       off_reset_pulse;

  // !! The signals below are hooked into by DFT logic !!
  // !! Be careful about deleting/renaming them        !!
  logic hook_core_mux_mode;
  logic [31:0] hook_core_d;
  logic [31:0] hook_core_q;
  compressed_repair_t hook_core_compressed_repair;
  uncompressed_repair_t hook_core_uncompressed_repair;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if(!i_rst_n) r_repair_settings <= '0;
    else if(i_imc_bisr_shift_en)
      r_repair_settings <= {i_imc_bisr_si, r_repair_settings[$bits(compressed_repair_t)-1:1]};
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if(!i_rst_n) r_updated_repair_settings <= '0;
    else if(i_imc_bisr_ue)
      r_updated_repair_settings <= {i_imc_bisr_si, r_repair_settings[$bits(compressed_repair_t)-1:1]};
  end

  always_comb foreach(s_uncompressed_repair_settings[i])
    s_uncompressed_repair_settings[i] = r_updated_repair_settings.repair_en & (i >= r_updated_repair_settings.repair_col);

  always_comb foreach(s_onehot_repair_setting[i])
    s_onehot_repair_setting[i] = r_updated_repair_settings.repair_en & (i == r_updated_repair_settings.repair_col);

  // Pipelined shift out decision for design timing although prevents readback
  always_ff @(posedge i_clk, negedge i_rst_n)
    if(!i_rst_n) r_imc_bisr_shift_en <= '0;
    else         r_imc_bisr_shift_en <= i_imc_bisr_shift_en;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(!i_rst_n) r_imc_bisr_ue <= '0;
    else         r_imc_bisr_ue <= i_imc_bisr_ue;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(!i_rst_n) begin
      o_imc_bisr_shift_en <= '0;
      o_imc_bisr_so       <= '0;
      o_imc_bisr_ue       <= '0;
    end else begin
      o_imc_bisr_shift_en <= i_imc_bisr_shift_en;
      o_imc_bisr_so       <= r_repair_settings[0];
      o_imc_bisr_ue       <= i_imc_bisr_ue;
    end

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n) off_reset_detect <= 2'b00;
    else if(~&off_reset_detect) off_reset_detect <= {off_reset_detect[0], 1'b1};

  // A repair is triggered when functional reset is raised (efuse-sourced repair data will be shifted before functional boot).
  assign off_reset_pulse = (off_reset_detect == 2'b01);

  // In eFuse-source-mode, loopback D into Q to maintain current value after shifting has finished
  // In IMC-BIRA-source-mode, feed settings shifted from i_imc_bisr interface
  assign hook_core_d = i_mux_mode ? s_onehot_repair_setting : hook_core_q;

`ifndef TARGET_DFT
`ifndef TESSENT
  // This will be driven by Tessent-inserted logic, tie it to 0 for non-DFT simulation
  assign hook_core_q = '0;
`endif // ! TESSENT
`endif // ! TARGET_DFT

  always_comb begin : hook_core_compressed_repair_cproc
    hook_core_compressed_repair = '0;
    foreach(hook_core_q[i])
      if(hook_core_q[i])
        hook_core_compressed_repair = '{repair_en: 1'b1, repair_col: i};
  end : hook_core_compressed_repair_cproc

  always_comb foreach(hook_core_uncompressed_repair[i])
    hook_core_uncompressed_repair[i] = hook_core_compressed_repair.repair_en & (i >= hook_core_compressed_repair.repair_col);

  assign o_update_repair_setting     = r_imc_bisr_ue | off_reset_pulse;
  assign o_compressed_repair_setting = i_mux_mode ? r_updated_repair_settings : hook_core_compressed_repair;
  assign o_repair_setting            = i_mux_mode ? s_uncompressed_repair_settings : hook_core_uncompressed_repair;
  // Do not pipeline as this signal is quasi-static, must be constrained as such in PD
  assign o_mux_mode                  = i_mux_mode;

endmodule : imc_bisr_hook
