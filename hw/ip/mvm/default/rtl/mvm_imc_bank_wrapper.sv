// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// mvm_imc_bank_wrapper combines 2 outputs to generate 19 bits output
/// and implements the column repair
///
module mvm_imc_bank_wrapper
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  (
  /// Clock, positive edge triggered
  input  wire                                                          i_clk,
  /// Asynchronous reset, active low
  input  wire                                                          i_rst_n,

  /// Repair interface signals
  input  logic                                                         i_imc_bisr_mux_mode,
  input  logic                                                         i_imc_bisr_shift_en,
  input  logic                                                         i_imc_bisr_ue,
  input  logic                                                         i_imc_bisr_si,
  output logic                                                         o_imc_bisr_mux_mode,
  output logic                                                         o_imc_bisr_shift_en,
  output logic                                                         o_imc_bisr_ue,
  output logic                                                         o_imc_bisr_so,

  /// Weight interface signals
  /// weight write enable bit for this block
  input  logic                                                         i_write_enable,
  /// row select address
  input  logic                                        [IMC_ROW_PW-1:0] i_write_row,
  /// weight set select for weight writing (should never equal compute_wss when w_en is active)
  input  logic                                 [IMC_WEIGHT_SET_PW-1:0] i_write_wss,
  /// weight values to be written
  input  logic              [IMC_NB_COLS_PER_BANK-1:0][IMC_DATA_W-1:0] i_write_values,

  /// Compute interface signals
  input  logic                                                         i_compute_enable,
  /// compute input vector of 1 bit elements
  input  logic                                       [IMC_NB_ROWS-1:0] i_compute_inp,
  /// compute weight set select (should never equal write_wss when w_en is active)
  input  logic                                 [IMC_WEIGHT_SET_PW-1:0] i_compute_wss,
  /// compute block enable. If all blocks enables are disabled (0) then the imc operation equals zero.
  input  logic                                [IMC_BLOCK_ENABLE_W-1:0] i_compute_block_enable,
  /// determines how weights should be interpreted (00: unsigned, 01: 4 bit signed, 10: 8 bit signed, 11: 16 bit signed)
  input  logic                                                   [1:0] i_compute_weight_format,
  /// Partial accumulation result
  output logic [MVM_IMC_COLS_GROUP-1:0][MVM_IMC_COLS_GROUP_OUT_WD-1:0] o_compute_out
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
  logic      [IMC_NB_COLS_PER_BANK:0][IMC_OUT_DATA_W-1:0] imc_bank_compute_out;
  logic [MVM_IMC_COLS_GROUP-1:0][1:0][IMC_OUT_DATA_W-1:0] compute_out;

  logic                               update_repair_setting;
  imc_bist_pkg::compressed_repair_t   compressed_repair_setting;
  imc_bist_pkg::uncompressed_repair_t repair_setting;

  logic [IMC_NB_COLS_PER_BANK:0][IMC_DATA_W-1:0] write_values;

  // =====================================================
  // RTL
  // =====================================================

  always_comb begin : cproc_write_values_repair_mux
    foreach(write_values[i])
      if(~compressed_repair_setting.repair_en) begin
        // If not repairing operate normally (i mapped to i, column 32 tied off)
        write_values[i] = (i < IMC_NB_COLS_PER_BANK) ? i_write_values[i] : '0;
      end else begin
        // If repairing:
        if(i > compressed_repair_setting.repair_col) begin
          // Left of the repaired column we are shifting away 1 position
          //   towards the redundant column 32 (i mapped to i-1)
          write_values[i] = (i > 0) ? i_write_values[i-1] : '0;
        end else if(i == compressed_repair_setting.repair_col) begin
          // Repaired column is tied off
          write_values[i] = '0;
        end else begin
          // Right of the repaired column operate normally (i mapped to i)
          write_values[i] = (i < IMC_NB_COLS_PER_BANK) ? i_write_values[i] : '0;
        end
      end
  end

  imc_bisr_hook u_imc_bisr_hook (
    .i_clk,
    .i_rst_n,
    .i_mux_mode(i_imc_bisr_mux_mode),
    .i_imc_bisr_shift_en,
    .i_imc_bisr_ue,
    .i_imc_bisr_si,
    .o_mux_mode(o_imc_bisr_mux_mode),
    .o_imc_bisr_shift_en,
    .o_imc_bisr_ue,
    .o_imc_bisr_so,
    .o_update_repair_setting(update_repair_setting),
    .o_compressed_repair_setting(compressed_repair_setting),
    .o_repair_setting(repair_setting)
  );

  imc_bank u_imc_bank (
    .clock          (i_clk),
    .rst_n          (i_rst_n),
    .repair_setting (repair_setting),
    .update_repair_setting(update_repair_setting),
    // Weight related input signals
    // input vector of 32 weights sliced from 64 bit weight in vector
    .write_values_0 (write_values[0]),
    .write_values_1 (write_values[1]),
    .write_values_2 (write_values[2]),
    .write_values_3 (write_values[3]),
    .write_values_4 (write_values[4]),
    .write_values_5 (write_values[5]),
    .write_values_6 (write_values[6]),
    .write_values_7 (write_values[7]),
    .write_values_8 (write_values[8]),
    .write_values_9 (write_values[9]),
    .write_values_10(write_values[10]),
    .write_values_11(write_values[11]),
    .write_values_12(write_values[12]),
    .write_values_13(write_values[13]),
    .write_values_14(write_values[14]),
    .write_values_15(write_values[15]),
    .write_values_16(write_values[16]),
    .write_values_17(write_values[17]),
    .write_values_18(write_values[18]),
    .write_values_19(write_values[19]),
    .write_values_20(write_values[20]),
    .write_values_21(write_values[21]),
    .write_values_22(write_values[22]),
    .write_values_23(write_values[23]),
    .write_values_24(write_values[24]),
    .write_values_25(write_values[25]),
    .write_values_26(write_values[26]),
    .write_values_27(write_values[27]),
    .write_values_28(write_values[28]),
    .write_values_29(write_values[29]),
    .write_values_30(write_values[30]),
    .write_values_31(write_values[31]),
    .write_values_32(write_values[32]),

    .write_wss(i_write_wss),  // weight set select
    // pass on the correct weight write enable bit for this block
    // (0 when test_mode_i is 1 to avoid destroying any stored weights)
    .write_enable(i_write_enable),
    .write_row(i_write_row),
    .compute_weight_format(i_compute_weight_format),
    // Compute related input signals
    .compute_enable(i_compute_enable), // TODO: Connect this signals correctly
    // compute_serial_bits_i input vector of 1 bit elements
    .compute_inp(i_compute_inp),
    // compute weight set select (should never equal w_set when w_en is active)
    .compute_wss(i_compute_wss),
    // compute block enable signals for this block
    // (all 0's when test_mode_i is active to get the output to go to 0)
    .compute_block_enable(i_compute_block_enable),
    //.compute_launch_operation   (c_en), // Global compute enable for all blocks
    // In test_mode_i, compute_gate_clock should be 0 as to get the outputs to go to 0 after 6 cycles.
    //.compute_gate_clock(compute_gate_clock & !test_mode_i),

    // Compute output
    .compute_out_0 (imc_bank_compute_out[0]),
    .compute_out_1 (imc_bank_compute_out[1]),
    .compute_out_2 (imc_bank_compute_out[2]),
    .compute_out_3 (imc_bank_compute_out[3]),
    .compute_out_4 (imc_bank_compute_out[4]),
    .compute_out_5 (imc_bank_compute_out[5]),
    .compute_out_6 (imc_bank_compute_out[6]),
    .compute_out_7 (imc_bank_compute_out[7]),
    .compute_out_8 (imc_bank_compute_out[8]),
    .compute_out_9 (imc_bank_compute_out[9]),
    .compute_out_10(imc_bank_compute_out[10]),
    .compute_out_11(imc_bank_compute_out[11]),
    .compute_out_12(imc_bank_compute_out[12]),
    .compute_out_13(imc_bank_compute_out[13]),
    .compute_out_14(imc_bank_compute_out[14]),
    .compute_out_15(imc_bank_compute_out[15]),
    .compute_out_16(imc_bank_compute_out[16]),
    .compute_out_17(imc_bank_compute_out[17]),
    .compute_out_18(imc_bank_compute_out[18]),
    .compute_out_19(imc_bank_compute_out[19]),
    .compute_out_20(imc_bank_compute_out[20]),
    .compute_out_21(imc_bank_compute_out[21]),
    .compute_out_22(imc_bank_compute_out[22]),
    .compute_out_23(imc_bank_compute_out[23]),
    .compute_out_24(imc_bank_compute_out[24]),
    .compute_out_25(imc_bank_compute_out[25]),
    .compute_out_26(imc_bank_compute_out[26]),
    .compute_out_27(imc_bank_compute_out[27]),
    .compute_out_28(imc_bank_compute_out[28]),
    .compute_out_29(imc_bank_compute_out[29]),
    .compute_out_30(imc_bank_compute_out[30]),
    .compute_out_31(imc_bank_compute_out[31]),
    .compute_out_32(imc_bank_compute_out[32])
  );

  always_comb begin : cproc_compute_out_repair_mux
    foreach(compute_out[i,j])
      if(~compressed_repair_setting.repair_en)              compute_out[i][j] = imc_bank_compute_out[i*2+j];
      else begin
        if((i*2+j) >= compressed_repair_setting.repair_col) compute_out[i][j] = imc_bank_compute_out[i*2+j+1];
        else                                                compute_out[i][j] = imc_bank_compute_out[i*2+j];
      end
  end

  always_comb begin : c_combining_columns_proc
    foreach (o_compute_out[group]) begin
      o_compute_out[group] = {compute_out[group][1], {IMC_DATA_W{1'b0}}}
                           + {
                               {IMC_DATA_W{compute_out[group][0][IMC_OUT_DATA_W-1]}},
                               compute_out[group][0]
                             };
    end
  end
endmodule
