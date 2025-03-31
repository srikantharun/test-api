// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IMC bank data dumper
// Owner: Tiago Campos <tiago.campos@axelera.ai>
`timescale 1ns/1fs

`ifdef DUMP_IMC_BANKS
module imc_bank_dumper
import imc_bank_pkg::*;
import imc_bank_dumper_pkg::*;
#(
  parameter ID=0,
  parameter SUB_ID=0
)(
  // Common interface
  input	  wire                                  clock,
  input	  wire                                  rst_n,
  input	  wire [IMC_NB_TOTAL_COLS_PER_BANK-2:0] repair_setting,
  input	  wire                                  update_repair_setting,

  // Write interface
  input   wire                                  write_enable,         // weight write enable bit for this block
  input   wire [IMC_ROW_PW-1:0]                 write_row,            // row select address
  input   wire [IMC_WEIGHT_SET_PW-1:0]          write_wss,            // weight set select for weight writing (should never equal compute_wss when w_en is active)
  input   wire [IMC_DATA_W-1:0]                 write_values_0,       // weight values to be written
  input   wire [IMC_DATA_W-1:0]                 write_values_1,
  input   wire [IMC_DATA_W-1:0]                 write_values_2,
  input   wire [IMC_DATA_W-1:0]                 write_values_3,
  input   wire [IMC_DATA_W-1:0]                 write_values_4,
  input   wire [IMC_DATA_W-1:0]                 write_values_5,
  input   wire [IMC_DATA_W-1:0]                 write_values_6,
  input   wire [IMC_DATA_W-1:0]                 write_values_7,
  input   wire [IMC_DATA_W-1:0]                 write_values_8,
  input   wire [IMC_DATA_W-1:0]                 write_values_9,
  input   wire [IMC_DATA_W-1:0]                 write_values_10,
  input   wire [IMC_DATA_W-1:0]                 write_values_11,
  input   wire [IMC_DATA_W-1:0]                 write_values_12,
  input   wire [IMC_DATA_W-1:0]                 write_values_13,
  input   wire [IMC_DATA_W-1:0]                 write_values_14,
  input   wire [IMC_DATA_W-1:0]                 write_values_15,
  input   wire [IMC_DATA_W-1:0]                 write_values_16,
  input   wire [IMC_DATA_W-1:0]                 write_values_17,
  input   wire [IMC_DATA_W-1:0]                 write_values_18,
  input   wire [IMC_DATA_W-1:0]                 write_values_19,
  input   wire [IMC_DATA_W-1:0]                 write_values_20,
  input   wire [IMC_DATA_W-1:0]                 write_values_21,
  input   wire [IMC_DATA_W-1:0]                 write_values_22,
  input   wire [IMC_DATA_W-1:0]                 write_values_23,
  input   wire [IMC_DATA_W-1:0]                 write_values_24,
  input   wire [IMC_DATA_W-1:0]                 write_values_25,
  input   wire [IMC_DATA_W-1:0]                 write_values_26,
  input   wire [IMC_DATA_W-1:0]                 write_values_27,
  input   wire [IMC_DATA_W-1:0]                 write_values_28,
  input   wire [IMC_DATA_W-1:0]                 write_values_29,
  input   wire [IMC_DATA_W-1:0]                 write_values_30,
  input   wire [IMC_DATA_W-1:0]                 write_values_31,
  input   wire [IMC_DATA_W-1:0]                 write_values_32,

  // Compute interface
  input   wire                                  compute_enable,
  input   wire [IMC_NB_ROWS-1:0]                compute_inp,            // compute input vector of 1 bit elements
  input   wire [IMC_WEIGHT_SET_PW-1:0]          compute_wss,            // compute weight set select (should never equal write_wss when w_en is active)
  input   wire [IMC_BLOCK_ENABLE_W-1:0]         compute_block_enable,   // compute block enable. If all blocks enables are disabled (0) then the imc operation equals zero.
  input   wire [1:0]                            compute_weight_format,  // determines how weights should be interpreted (00: unsigned, 01: 4 bit signed, 10: 8 bit signed, 11: 16 bit signed)
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_0,          // Partial accumulation result
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_1,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_2,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_3,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_4,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_5,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_6,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_7,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_8,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_9,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_10,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_11,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_12,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_13,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_14,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_15,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_16,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_17,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_18,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_19,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_20,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_21,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_22,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_23,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_24,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_25,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_26,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_27,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_28,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_29,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_30,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_31,
  output  wire [IMC_OUT_DATA_W-1:0]             compute_out_32
);

dataDump_both_t    data_dump_both;
dataDump_write_t   data_dump_write;
dataDump_compute_t data_dump_compute;

logic has_compute;
logic [IMC_DATA_W-1:0] write_value_mask;

string fname_both;
string fname_compute;
string fname_write;

assign write_value_mask = {IMC_DATA_W{1'b1}};

assign data_dump_write = '{
  write_enable   : write_enable,
  write_values_0 : write_values_0  & write_value_mask,
  write_values_1 : write_values_1  & write_value_mask,
  write_values_2 : write_values_2  & write_value_mask,
  write_values_3 : write_values_3  & write_value_mask,
  write_values_4 : write_values_4  & write_value_mask,
  write_values_5 : write_values_5  & write_value_mask,
  write_values_6 : write_values_6  & write_value_mask,
  write_values_7 : write_values_7  & write_value_mask,
  write_values_8 : write_values_8  & write_value_mask,
  write_values_9 : write_values_9  & write_value_mask,
  write_values_10: write_values_10 & write_value_mask,
  write_values_11: write_values_11 & write_value_mask,
  write_values_12: write_values_12 & write_value_mask,
  write_values_13: write_values_13 & write_value_mask,
  write_values_14: write_values_14 & write_value_mask,
  write_values_15: write_values_15 & write_value_mask,
  write_values_16: write_values_16 & write_value_mask,
  write_values_17: write_values_17 & write_value_mask,
  write_values_18: write_values_18 & write_value_mask,
  write_values_19: write_values_19 & write_value_mask,
  write_values_20: write_values_20 & write_value_mask,
  write_values_21: write_values_21 & write_value_mask,
  write_values_22: write_values_22 & write_value_mask,
  write_values_23: write_values_23 & write_value_mask,
  write_values_24: write_values_24 & write_value_mask,
  write_values_25: write_values_25 & write_value_mask,
  write_values_26: write_values_26 & write_value_mask,
  write_values_27: write_values_27 & write_value_mask,
  write_values_28: write_values_28 & write_value_mask,
  write_values_29: write_values_29 & write_value_mask,
  write_values_30: write_values_30 & write_value_mask,
  write_values_31: write_values_31 & write_value_mask,
  write_values_32: write_values_32 & write_value_mask,
  write_row      : write_row       & {IMC_ROW_PW{write_enable}},
  write_wss      : write_wss       & {IMC_WEIGHT_SET_PW{write_enable}}
};

assign has_compute = compute_enable;
assign data_dump_compute = '{
  compute_weight_format : compute_weight_format  & {2{has_compute}},
  compute_enable        : compute_enable,
  compute_inp           : compute_inp            & {IMC_NB_ROWS{has_compute}},
  compute_wss           : compute_wss            & {IMC_WEIGHT_SET_PW{has_compute}},
  compute_block_enable  : compute_block_enable   & {IMC_BLOCK_ENABLE_W{has_compute}}
};

assign data_dump_both = '{
  write  : data_dump_write,
  compute: data_dump_compute
};

imc_bank_to_file #(
  .AXIS_NB_DATA_WORDS(1),
  .AXIS_WORD_WIDTH($bits(dataDump_both_t)),
  .RANDOM_READY(0)
) axis_dumper_both (
  .clk_i(clock),
  .tready_o(),
  .tvalid_i(write_enable|has_compute),
  .tlast_i(write_enable|has_compute),
  .tdata_i(data_dump_both),
  .tstrb_i(1'b1)
);

imc_bank_to_file #(
  .AXIS_NB_DATA_WORDS(1),
  .AXIS_WORD_WIDTH($bits(dataDump_compute_t)),
  .RANDOM_READY(0)
) axis_dumper_compute (
  .clk_i(clock),
  .tready_o(),
  .tvalid_i(has_compute),
  .tlast_i(has_compute),
  .tdata_i(data_dump_compute),
  .tstrb_i(1'b1)
);

imc_bank_to_file #(
  .AXIS_NB_DATA_WORDS(1),
  .AXIS_WORD_WIDTH($bits(dataDump_write_t)),
  .RANDOM_READY(0)
) axis_dumper_write (
  .clk_i(clock),
  .tready_o(),
  .tvalid_i(write_enable),
  .tlast_i(write_enable),
  .tdata_i(data_dump_write),
  .tstrb_i(1'b1)
);

initial begin
  $sformat(fname_both, "imc_bank_%0d_%0d_dump_both.txt", ID, SUB_ID);
  $sformat(fname_compute, "imc_bank_%0d_%0d_dump_compute.txt", ID, SUB_ID);
  $sformat(fname_write, "imc_bank_%0d_%0d_dump_write.txt", ID, SUB_ID);
  axis_dumper_both.openDumpFile(fname_both);
  axis_dumper_compute.openDumpFile(fname_compute);
  axis_dumper_write.openDumpFile(fname_write);
end

//final begin
//  axis_dumper_both.closeDumpFile();
//  axis_dumper_compute.closeDumpFile();
//  axis_dumper_write.closeDumpFile();
//end

endmodule
`endif // DUMP_IMC_BANKS
