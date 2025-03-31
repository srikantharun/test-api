//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_pw.sv#2 $
// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
// ------------------------------------------------------------------------------

// ----------------------------------------------------------------------------
//                              DDR Controller
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//                              Description
//
// Posted Writes sub-module to generate internal ih signals related to Partial 
// Writes from HIF command (hif_col and hif_cmd_length) only
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module ih_pw
import DWC_ddrctl_reg_pkg::*;
#(
    //------------------------------ PARAMETERS ------------------------------------
      parameter CMD_LEN_BITS         = 1                             // bits for command length, when used
     ,parameter WRDATA_CYCLES        = `MEMC_WRDATA_CYCLES 
     ,parameter MWR_BITS = 1  // currently 1-bit info (OR of all data beats)
     ,parameter PARTIAL_WR_BITS      = `UMCTL2_PARTIAL_WR_BITS 
     ,parameter PARTIAL_WR_BITS_LOG2 = 1 
     ,parameter PW_WORD_CNT_WD_MAX   = 1 
    )
    (
    //-------------------------- INPUTS AND OUTPUTS --------------------------------    
      input [CMD_LEN_BITS-1:0]            ih_te_rd_length
     ,input [`MEMC_WORD_BITS-1:0]         ih_te_critical_dword      // for reads only, critical word within a block - not currently supported
                                                                    // would be qualified by ((ih_te_rd_valid | ih_te_wr_valid) & ih_te_rd))
                                                                    // for rmw, this is forced to 0
     `ifdef SNPS_ASSERT_ON
      `ifndef SYNTHESIS
     ,input                               core_ddrc_core_clk
     ,input                               core_ddrc_rstn      
      `endif //SYNTHESIS
     `endif //SNPS_ASSERT_ON
     ,input  [BURST_RDWR_WIDTH-1:0]       reg_ddrc_burst_rdwr 
     ,input                               reg_ddrc_frequency_ratio
     ,output [PARTIAL_WR_BITS-1:0]        ih_te_wr_word_valid 
     ,output [PARTIAL_WR_BITS_LOG2-1:0]   ih_te_wr_ram_raddr_lsb_first 
     ,output [PW_WORD_CNT_WD_MAX-1:0]     ih_te_wr_pw_num_beats_m1 
     ,output [PW_WORD_CNT_WD_MAX-1:0]     ih_te_wr_pw_num_cols_m1 
    );



// drive length info for write as well for Posted Writes
wire [CMD_LEN_BITS-1:0] ih_te_wr_length;
assign ih_te_wr_length = ih_te_rd_length;



// hif_cmd_len=2'b00 - Full 
// hif_cmd_len=2'b10 - Half 
// hif_cmd_len=2'b11 - Quarter
// For Half/Quarter, use critical_dword to determine which half/quarter is valid
wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_full;
assign ih_te_wr_word_valid_full = {PARTIAL_WR_BITS{1'b1}};

wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_half_2nd;
assign ih_te_wr_word_valid_half_2nd = { {PARTIAL_WR_BITS/2{1'b1}}, {PARTIAL_WR_BITS/2{1'b0}} };
wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_half_1st;
assign ih_te_wr_word_valid_half_1st = { {PARTIAL_WR_BITS/2{1'b0}}, {PARTIAL_WR_BITS/2{1'b1}} };

wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_half;

assign ih_te_wr_word_valid_half = (ih_te_critical_dword[`MEMC_WORD_BITS-1]) ? ih_te_wr_word_valid_half_2nd : ih_te_wr_word_valid_half_1st;

// Quarter length only in MEMC_BL=16
wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_quarter_1st;
assign ih_te_wr_word_valid_quarter_1st = { {3*PARTIAL_WR_BITS/4{1'b0}}, {PARTIAL_WR_BITS/4{1'b1}}                              };
wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_quarter_2nd;
assign ih_te_wr_word_valid_quarter_2nd = { {2*PARTIAL_WR_BITS/4{1'b0}}, {PARTIAL_WR_BITS/4{1'b1}}, {1*PARTIAL_WR_BITS/4{1'b0}} };
wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_quarter_3rd;
assign ih_te_wr_word_valid_quarter_3rd = { {1*PARTIAL_WR_BITS/4{1'b0}}, {PARTIAL_WR_BITS/4{1'b1}}, {2*PARTIAL_WR_BITS/4{1'b0}} };
wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_quarter_4th;
assign ih_te_wr_word_valid_quarter_4th = {                              {PARTIAL_WR_BITS/4{1'b1}}, {3*PARTIAL_WR_BITS/4{1'b0}} };

wire [PARTIAL_WR_BITS-1:0] ih_te_wr_word_valid_quarter;

assign ih_te_wr_word_valid_quarter = (ih_te_critical_dword[`MEMC_WORD_BITS-1-:2]==2'b11) ? ih_te_wr_word_valid_quarter_4th : 
                                     (ih_te_critical_dword[`MEMC_WORD_BITS-1-:2]==2'b10) ? ih_te_wr_word_valid_quarter_3rd :
                                     (ih_te_critical_dword[`MEMC_WORD_BITS-1-:2]==2'b01) ? ih_te_wr_word_valid_quarter_2nd :
                                                                                           ih_te_wr_word_valid_quarter_1st ;


assign ih_te_wr_word_valid = (!ih_te_wr_length[CMD_LEN_BITS-1]) ? ih_te_wr_word_valid_full :
                             ( ih_te_wr_length[0])              ? ih_te_wr_word_valid_quarter : 
                                                                  ih_te_wr_word_valid_half ;


wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_full;
assign ih_te_wr_ram_raddr_lsb_first_full = {PARTIAL_WR_BITS_LOG2{1'b0}};


wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_eq1;

assign ih_te_wr_ram_raddr_lsb_first_eq1 = { { (PARTIAL_WR_BITS_LOG2-1){1'b0}}, 1'b1 };


wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_half;
wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_half_1st;
assign ih_te_wr_ram_raddr_lsb_first_half_1st = ih_te_wr_ram_raddr_lsb_first_full;
wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_half_2nd;
assign ih_te_wr_ram_raddr_lsb_first_half_2nd = ih_te_wr_ram_raddr_lsb_first_eq1 << (PARTIAL_WR_BITS_LOG2-1);

assign ih_te_wr_ram_raddr_lsb_first_half = (ih_te_critical_dword[`MEMC_WORD_BITS-1]) ? ih_te_wr_ram_raddr_lsb_first_half_2nd : ih_te_wr_ram_raddr_lsb_first_half_1st;

// Quarter length only in MEMC_BL=16
wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_quarter;
wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_quarter_1st;
assign ih_te_wr_ram_raddr_lsb_first_quarter_1st = ih_te_wr_ram_raddr_lsb_first_full;
wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_quarter_2nd;
assign ih_te_wr_ram_raddr_lsb_first_quarter_2nd = ih_te_wr_ram_raddr_lsb_first_eq1 << (PARTIAL_WR_BITS_LOG2-2);
wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_quarter_3rd;
assign ih_te_wr_ram_raddr_lsb_first_quarter_3rd = ih_te_wr_ram_raddr_lsb_first_half_2nd;
wire [PARTIAL_WR_BITS_LOG2:0]   ih_te_wr_ram_raddr_lsb_first_quarter_4th_wider;
assign ih_te_wr_ram_raddr_lsb_first_quarter_4th_wider = ih_te_wr_ram_raddr_lsb_first_half_2nd + ih_te_wr_ram_raddr_lsb_first_quarter_2nd;
wire [PARTIAL_WR_BITS_LOG2-1:0] ih_te_wr_ram_raddr_lsb_first_quarter_4th;
assign ih_te_wr_ram_raddr_lsb_first_quarter_4th = ih_te_wr_ram_raddr_lsb_first_quarter_4th_wider[PARTIAL_WR_BITS_LOG2-1:0];

assign ih_te_wr_ram_raddr_lsb_first_quarter = (ih_te_critical_dword[`MEMC_WORD_BITS-1-:2]==2'b11) ? ih_te_wr_ram_raddr_lsb_first_quarter_4th : 
                                              (ih_te_critical_dword[`MEMC_WORD_BITS-1-:2]==2'b10) ? ih_te_wr_ram_raddr_lsb_first_quarter_3rd :
                                              (ih_te_critical_dword[`MEMC_WORD_BITS-1-:2]==2'b01) ? ih_te_wr_ram_raddr_lsb_first_quarter_2nd :
                                                                                                    ih_te_wr_ram_raddr_lsb_first_quarter_1st ;

assign ih_te_wr_ram_raddr_lsb_first = (!ih_te_wr_length[CMD_LEN_BITS-1]) ? ih_te_wr_ram_raddr_lsb_first_full :
                                      ( ih_te_wr_length[0])              ? ih_te_wr_ram_raddr_lsb_first_quarter : 
                                                                           ih_te_wr_ram_raddr_lsb_first_half ;







wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_cols_a;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_cols_b;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_cols_c;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_cols_d;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_cols_e;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_cols_f;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_cols_m1_int;
wire                            ih_te_wr_pw_num_cols_eq0;

assign ih_te_wr_pw_num_cols_a = { {(PW_WORD_CNT_WD_MAX){1'b0}}, 1'b1};
assign ih_te_wr_pw_num_cols_b = ih_te_wr_pw_num_cols_a;

// quarter Writes only in MEMC_BL=16
assign ih_te_wr_pw_num_cols_c = ih_te_wr_pw_num_cols_b << !ih_te_wr_length[CMD_LEN_BITS-1];
assign ih_te_wr_pw_num_cols_d = ih_te_wr_pw_num_cols_c << !ih_te_wr_length[0];

assign ih_te_wr_pw_num_cols_e = ih_te_wr_pw_num_cols_d >> (reg_ddrc_burst_rdwr[3] || reg_ddrc_burst_rdwr[2]);
assign ih_te_wr_pw_num_cols_f = ih_te_wr_pw_num_cols_e >> reg_ddrc_burst_rdwr[3];


assign ih_te_wr_pw_num_cols_m1_int = ih_te_wr_pw_num_cols_f - { {(PW_WORD_CNT_WD_MAX){1'b0}}, 1'b1};
assign ih_te_wr_pw_num_cols_eq0 = &(~ih_te_wr_pw_num_cols_f);
assign ih_te_wr_pw_num_cols_m1 = (ih_te_wr_pw_num_cols_eq0) ? {PW_WORD_CNT_WD_MAX{1'b0}} : ih_te_wr_pw_num_cols_m1_int[PW_WORD_CNT_WD_MAX-1:0];

wire [3:0] reg_ddrc_burst_rdwr_x;
assign reg_ddrc_burst_rdwr_x = 
                                 (reg_ddrc_frequency_ratio) ? {1'b0, reg_ddrc_burst_rdwr[4:2]} : reg_ddrc_burst_rdwr[4:1]
                               ;


wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_beats_a;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_beats_b;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_beats_c;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_beats_d;
wire [PW_WORD_CNT_WD_MAX+1-1:0] ih_te_wr_pw_num_beats_m1_int;

assign ih_te_wr_pw_num_beats_a = (ih_te_wr_pw_num_cols_eq0) ? { {(PW_WORD_CNT_WD_MAX){1'b0}}, 1'b1} : ih_te_wr_pw_num_cols_f;
assign ih_te_wr_pw_num_beats_b = ih_te_wr_pw_num_beats_a << (reg_ddrc_burst_rdwr_x[1] || reg_ddrc_burst_rdwr_x[2] || reg_ddrc_burst_rdwr_x[3]) ;
assign ih_te_wr_pw_num_beats_c = ih_te_wr_pw_num_beats_b << (reg_ddrc_burst_rdwr_x[2] || reg_ddrc_burst_rdwr_x[3]) ;
assign ih_te_wr_pw_num_beats_d = ih_te_wr_pw_num_beats_c << (reg_ddrc_burst_rdwr_x[3]) ;
//spyglass disable_block TA_09
//SMD: Net 'DWC_ddrctl.U_ddrc.ddrc_ctrl_wrapper.\ddrc_ctrl_inst[0].ddrc_ctrl .ih.ih_ie_cmd_ctl.ih_pw.ih_te_wr_pw_num_beats_d[3]' [in 'ih_pw'] is not observable[affected by other input(s)].
//SJ: Functionally correct. In some configs, ih_te_wr_pw_num_beats_d[3] might never have value 1'b1.
assign ih_te_wr_pw_num_beats_m1_int = ih_te_wr_pw_num_beats_d - { {(PW_WORD_CNT_WD_MAX){1'b0}}, 1'b1};
//spyglass enable_block TA_09
assign ih_te_wr_pw_num_beats_m1 = 
                                  ih_te_wr_pw_num_beats_m1_int[PW_WORD_CNT_WD_MAX-1:0];


`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
localparam CATEGORY = 5; // Allows groups of assertions to be enabled/disabled at the same time

// ih_te_wr_ram_raddr_lsb_first_quarter_4th overflow
assert_never #(0, 0, "ih_te_wr_ram_raddr_lsb_first_quarter_4th overflow", CATEGORY) a_ih_te_wr_ram_raddr_lsb_first_quarter_4th_overflow
  (core_ddrc_core_clk, core_ddrc_rstn, (ih_te_wr_ram_raddr_lsb_first_quarter_4th_wider[PARTIAL_WR_BITS_LOG2]==1'b1));

`endif // SYNTHESIS
`endif
endmodule
