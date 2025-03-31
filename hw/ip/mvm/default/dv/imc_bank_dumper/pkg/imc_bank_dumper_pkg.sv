// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: imc bank dumper package
// Defines parameters and structs
// Owner: Tiago Campos <tiago.campos@axelera.ai>

package imc_bank_dumper_pkg;
  import imc_bank_pkg::*;
  //`define DUMP_COLUMN_32
  typedef struct packed {
      logic                          write_enable;    // weight write enable bit for this block
      logic  [       IMC_DATA_W-1:0] write_values_0;  // weight values to be written [0:32]
      logic  [       IMC_DATA_W-1:0] write_values_1;
      logic  [       IMC_DATA_W-1:0] write_values_2;
      logic  [       IMC_DATA_W-1:0] write_values_3;
      logic  [       IMC_DATA_W-1:0] write_values_4;
      logic  [       IMC_DATA_W-1:0] write_values_5;
      logic  [       IMC_DATA_W-1:0] write_values_6;
      logic  [       IMC_DATA_W-1:0] write_values_7;
      logic  [       IMC_DATA_W-1:0] write_values_8;
      logic  [       IMC_DATA_W-1:0] write_values_9;
      logic  [       IMC_DATA_W-1:0] write_values_10;
      logic  [       IMC_DATA_W-1:0] write_values_11;
      logic  [       IMC_DATA_W-1:0] write_values_12;
      logic  [       IMC_DATA_W-1:0] write_values_13;
      logic  [       IMC_DATA_W-1:0] write_values_14;
      logic  [       IMC_DATA_W-1:0] write_values_15;
      logic  [       IMC_DATA_W-1:0] write_values_16;
      logic  [       IMC_DATA_W-1:0] write_values_17;
      logic  [       IMC_DATA_W-1:0] write_values_18;
      logic  [       IMC_DATA_W-1:0] write_values_19;
      logic  [       IMC_DATA_W-1:0] write_values_20;
      logic  [       IMC_DATA_W-1:0] write_values_21;
      logic  [       IMC_DATA_W-1:0] write_values_22;
      logic  [       IMC_DATA_W-1:0] write_values_23;
      logic  [       IMC_DATA_W-1:0] write_values_24;
      logic  [       IMC_DATA_W-1:0] write_values_25;
      logic  [       IMC_DATA_W-1:0] write_values_26;
      logic  [       IMC_DATA_W-1:0] write_values_27;
      logic  [       IMC_DATA_W-1:0] write_values_28;
      logic  [       IMC_DATA_W-1:0] write_values_29;
      logic  [       IMC_DATA_W-1:0] write_values_30;
      logic  [       IMC_DATA_W-1:0] write_values_31;
      logic  [       IMC_DATA_W-1:0] write_values_32;
      logic  [       IMC_ROW_PW-1:0] write_row;       // row select address
      logic  [IMC_WEIGHT_SET_PW-1:0] write_wss;       // weight set select for weight writing (should never equal compute_wss when w_en is active)
    } dataDump_write_t;
    
    typedef struct packed {
      logic                  [2-1:0] compute_weight_format; // Treat weights as signed during imc computation
      logic                          compute_enable;        // Global clock gate for the imc_bank (gating when signal is high)
      logic [       IMC_NB_ROWS-1:0] compute_inp;           // compute_inp input vector of 1 bit elements
      logic [ IMC_WEIGHT_SET_PW-1:0] compute_wss;           // compute weight set select (should never equal write_wss when w_en is active)
      logic [IMC_BLOCK_ENABLE_W-1:0] compute_block_enable;  // Compute block enable. If all blocks enables are disabled (0) then the imc operation equals zero.
    } dataDump_compute_t;
    
    typedef struct packed {
      dataDump_write_t   write;
      dataDump_compute_t compute;
    } dataDump_both_t;
endpackage
