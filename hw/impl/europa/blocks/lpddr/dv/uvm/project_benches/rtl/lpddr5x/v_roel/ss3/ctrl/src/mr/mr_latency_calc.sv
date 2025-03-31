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

// -------------------------------------------------------------------------
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/mr/mr_latency_calc.sv#8 $
// -------------------------------------------------------------------------
// Description:
//                Memory Read Engine sub-unit: latency calculation.  This
//                block calculate the write data latency and the command latency
//                to compensate the write data delay from SRAM.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module mr_latency_calc 
import DWC_ddrctl_reg_pkg::*;
#(
   parameter MAX_CMD_DELAY     = `UMCTL2_MAX_CMD_DELAY
  ,parameter CMD_DELAY_BITS    = `UMCTL2_CMD_DELAY_BITS
)
(

     input                              co_yy_clk                   // clock
    ,input                              core_ddrc_rstn              // asynchronous negative-edge reset

    ,input                              dh_mr_frequency_ratio       // 0 - 1:2 mode, 1 - 1:4 mode
    ,input                              dh_mr_en_2t_timing_mode     // if in 2T mode, then increase write latency by 1 clk
    ,input                              reg_ddrc_lpddr4             // LPDDR4 mode
    ,input                              reg_ddrc_lpddr5
    ,input  [DFI_TWCK_EN_RD_WIDTH-1:0]  reg_ddrc_dfi_twck_en_rd     // WCK enable read timing
    ,input  [DFI_TWCK_EN_WR_WIDTH-1:0]  reg_ddrc_dfi_twck_en_wr     // WCK enable write timing
    ,input                              reg_ddrc_wck_on
    ,input  [`MEMC_NUM_RANKS-1:0]       reg_ddrc_active_ranks
    ,input  [DFI_TWCK_EN_FS_WIDTH-1:0]  reg_ddrc_dfi_twck_en_fs
    ,input  [EXTRA_GAP_FOR_DFI_LP_DATA_WIDTH-1:0]  reg_ddrc_extra_gap_for_dfi_lp_data
    ,input                              reg_ddrc_wr_link_ecc_enable
    ,input  [DFI_T_RDDATA_EN_WIDTH-1:0] reg_ddrc_dfi_t_rddata_en    // t_rddata_en parameter from dfi spec
    ,input  [DFI_TPHY_WRLAT_WIDTH-1:0]  reg_ddrc_dfi_tphy_wrlat     // write latency (command to data latency)
    ,input  [DFI_TPHY_WRDATA_WIDTH-1:0] reg_ddrc_dfi_tphy_wrdata    // tphy_wrdata parameter from dfi spec
    ,input                              reg_ddrc_dfi_lp_en_data
    ,input  [1:0]                       gs_mr_write_ph              // indicates that write phase
    ,input  [1:0]                       gs_mr_read_ph               // indicates that read  phase

    ,output reg [CMD_DELAY_BITS-1:0]         dfi_cmd_delay
    ,output reg [1:0]                        mr_t_wrlat_add_sdr
    ,output     [DFI_TPHY_WRLAT_WIDTH-1:0]   mr_t_wrlat
    ,output reg [1:0]                        mr_t_wrdata_add_sdr
    ,output reg [DFI_TPHY_WRDATA_WIDTH-1:0]  mr_t_wrdata
    ,output reg [1:0]                        mr_t_rddata_en_add_sdr
    ,output     [DFI_T_RDDATA_EN_WIDTH-1:0]  mr_t_rddata_en
    ,output reg [DFI_TWCK_EN_RD_WIDTH-2:0]   mr_lp_data_rd
    ,output reg [DFI_TWCK_EN_WR_WIDTH-2:0]   mr_lp_data_wr

);

// VCS UNR CONSTANT declarations


    wire [CMD_DELAY_BITS-1:0]   dfilp_cmd_gap;
    wire [CMD_DELAY_BITS-1:0]   wr_cmd_gap;
    wire [$bits(reg_ddrc_dfi_tphy_wrlat):0]      wrlat_sdr;
    wire [$bits(wrlat_sdr)-1:0]                  wrlat_adj;
    wire [$bits(wrlat_sdr)-1:0]                  wrdata_lat;
    wire [$bits(wrlat_sdr)-1:0]                  wrdata_lat_p0;
    wire [$bits(wrdata_lat)-1:0]                 wrdata_adj;
    wire [$bits(wrdata_lat)-1:0]                 wrdata_lat_cyc;
    wire [$bits(wrdata_lat):0]                   wrdata_cmd_delay_wider;
    wire [$bits(wrdata_lat)-1:0]                 wrdata_cmd_delay;
    wire                                         add_wrdata_lat;

    reg  [DFI_TPHY_WRLAT_WIDTH-1:0]         wrlat_adj_cyc;
    wire [DFI_TPHY_WRLAT_WIDTH:0]           mr_t_wrlat_wider;
    reg  [$bits(wrdata_lat)-2:0]            wrdata_adj_cyc;
    wire [$bits(wrdata_lat)-1:0]            mr_t_wrdata_int_wider;
    wire [DFI_TPHY_WRDATA_WIDTH-1:0]        mr_t_wrdata_int;

    wire [DFI_TWCK_EN_RD_WIDTH-1:0]  read_en_lat;
    wire [DFI_TWCK_EN_RD_WIDTH-2:0]  read_en_lat_cyc;
    wire [DFI_TWCK_EN_WR_WIDTH-1:0]  write_en_lat;
    wire [DFI_TWCK_EN_WR_WIDTH-2:0]  write_en_lat_cyc;
    wire [DFI_TWCK_EN_RD_WIDTH-2:0]  data_en_lat_cyc;
    wire [DFI_TWCK_EN_RD_WIDTH-2:0]  data_en_cmd_delay;

    reg  [DFI_TWCK_EN_RD_WIDTH-1:0]  mr_lp_data_rd_wider;
    reg  [DFI_TWCK_EN_WR_WIDTH-1:0]  mr_lp_data_wr_wider;

    wire                         cas_ws_fs_en;
    assign cas_ws_fs_en = reg_ddrc_wck_on & (reg_ddrc_active_ranks != {{$bits(reg_ddrc_active_ranks)-1{1'b0}}, 1'b1});


    assign  dfilp_cmd_gap = {{($bits(dfilp_cmd_gap)-2){1'b0}}, 2'd3}
                            + {{($bits(dfilp_cmd_gap)-$bits(reg_ddrc_extra_gap_for_dfi_lp_data)){1'b0}}, reg_ddrc_extra_gap_for_dfi_lp_data};

    assign  wr_cmd_gap = {{($bits(wr_cmd_gap)-2){1'b0}}, 2'd3};

    // ----------------------------------------------------------------------------------------
    // deassert timing of dfi_lp_data_req
    // ----------------------------------------------------------------------------------------
    // minimum latency of rddata_en or wck_en for read
    assign  read_en_lat =
                          reg_ddrc_lpddr4 ? {{DFI_TWCK_EN_RD_WIDTH-DFI_T_RDDATA_EN_WIDTH{1'b0}}, reg_ddrc_dfi_t_rddata_en} :
                          cas_ws_fs_en    ? reg_ddrc_dfi_twck_en_fs :
                          (reg_ddrc_dfi_twck_en_rd < {{DFI_TWCK_EN_RD_WIDTH-DFI_T_RDDATA_EN_WIDTH{1'b0}}, reg_ddrc_dfi_t_rddata_en}) ? reg_ddrc_dfi_twck_en_rd :
                          {{DFI_TWCK_EN_RD_WIDTH-DFI_T_RDDATA_EN_WIDTH{1'b0}}, reg_ddrc_dfi_t_rddata_en}
                          ;

    // read_en_lat (core clock cycle)
    assign  read_en_lat_cyc = (read_en_lat[DFI_TWCK_EN_RD_WIDTH-1:1] >> dh_mr_frequency_ratio);

    // minimum latency of wrdata_en or wck_en for write
    assign  write_en_lat =
                          reg_ddrc_lpddr4 ? {{DFI_TWCK_EN_RD_WIDTH-DFI_TPHY_WRLAT_WIDTH{1'b0}}, reg_ddrc_dfi_tphy_wrlat} :
                          cas_ws_fs_en    ? reg_ddrc_dfi_twck_en_fs :
                          (reg_ddrc_dfi_twck_en_wr < {{DFI_TWCK_EN_RD_WIDTH-DFI_TPHY_WRLAT_WIDTH{1'b0}}, reg_ddrc_dfi_tphy_wrlat}) ? reg_ddrc_dfi_twck_en_wr :
                                            {{DFI_TWCK_EN_RD_WIDTH-DFI_TPHY_WRLAT_WIDTH{1'b0}}, reg_ddrc_dfi_tphy_wrlat}
                           ; 

    // write_en_lat (core clock cycle)
    assign  write_en_lat_cyc = (write_en_lat[DFI_TWCK_EN_WR_WIDTH-1:1] >> dh_mr_frequency_ratio);

    // mininum data_en latency (core clock cycle)
    assign  data_en_lat_cyc = (read_en_lat_cyc < write_en_lat_cyc) ? read_en_lat_cyc : write_en_lat_cyc;

    // command delay for DFI low power
//spyglass disable_block W164a
//SMD: LHS: 'data_en_cmd_delay' width 7 is less than RHS: '({{ ((DFI_TWCK_EN_RD_WIDTH - 1) - CMD_DELAY_BITS){ 1'b0} }  ,dfilp_cmd_gap} - data_en_lat_cyc)' width 8 in assignment 
//SJ: Overflow not possible since below statement will be executed dfilp_cmd_gap > data_en_lat_cyc
    assign  data_en_cmd_delay = (!reg_ddrc_dfi_lp_en_data)                                            ? {(DFI_TWCK_EN_RD_WIDTH-1){1'b0}} :
                                (data_en_lat_cyc > {{(DFI_TWCK_EN_RD_WIDTH-1-CMD_DELAY_BITS){1'b0}},dfilp_cmd_gap}) ? {(DFI_TWCK_EN_RD_WIDTH-1){1'b0}} :
                                {{(DFI_TWCK_EN_RD_WIDTH-1-CMD_DELAY_BITS){1'b0}},dfilp_cmd_gap} - data_en_lat_cyc;
//spyglass enable_block W164a

    // deassert timing of dfi_lp_data_req for READ
    logic [DFI_TWCK_EN_RD_WIDTH-1:0] mr_lp_data_rd_wider_update;
    assign mr_lp_data_rd_wider_update =  {1'b0, read_en_lat_cyc} + {{($bits(mr_lp_data_rd_wider) - $bits(dfi_cmd_delay)){1'b0}}, dfi_cmd_delay}
                                                                 - {{($bits(mr_lp_data_rd_wider) - $bits(dfilp_cmd_gap)){1'b0}}, dfilp_cmd_gap};

    always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         mr_lp_data_rd_wider <= {$bits(mr_lp_data_rd_wider){1'b0}};
      end
      else if (mr_lp_data_rd_wider != mr_lp_data_rd_wider_update) begin
         mr_lp_data_rd_wider <= mr_lp_data_rd_wider_update;
      end
    end

    assign mr_lp_data_rd = reg_ddrc_dfi_lp_en_data ? mr_lp_data_rd_wider[DFI_TWCK_EN_RD_WIDTH-2:0] :
                                                     {$bits(mr_lp_data_rd){1'b0}};

    // deassert timing of dfi_lp_data_req for WRITE
    logic [DFI_TWCK_EN_WR_WIDTH-1:0] mr_lp_data_wr_wider_update;
    assign mr_lp_data_wr_wider_update = {1'b0, write_en_lat_cyc} + {{$bits(mr_lp_data_wr_wider) - $bits(dfi_cmd_delay){1'b0}}, dfi_cmd_delay}
                                                                 - {{$bits(mr_lp_data_wr_wider) - $bits(dfilp_cmd_gap){1'b0}}, dfilp_cmd_gap};

    always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         mr_lp_data_wr_wider <= {$bits(mr_lp_data_wr_wider){1'b0}};
      end
      else if (mr_lp_data_wr_wider != mr_lp_data_wr_wider_update) begin
         mr_lp_data_wr_wider <= mr_lp_data_wr_wider_update;
      end
    end

    assign mr_lp_data_wr = reg_ddrc_dfi_lp_en_data ? mr_lp_data_wr_wider[DFI_TWCK_EN_WR_WIDTH-2:0] :
                                                     {$bits(mr_lp_data_wr){1'b0}};

    // ----------------------------------------------------------------------------------------
    // command delay
    // ----------------------------------------------------------------------------------------
    // WR data path delay

    // calculate wrdata_en latency from command output to wrdata_en output in pi module
    assign  wrlat_sdr      = {{($bits(wrlat_sdr)-$bits(reg_ddrc_dfi_tphy_wrlat)){1'b0}}, reg_ddrc_dfi_tphy_wrlat}
                            // compensation for LPDDR4, +3 because WR is 4-cycles command
                             + (reg_ddrc_lpddr4 ? {{($bits(wrlat_sdr)-2){1'b0}},2'b11} : {$bits(wrlat_sdr){1'b0}})
                             + {5'd0,gs_mr_write_ph} // phase offset of WR command
                             + (reg_ddrc_lpddr5 ? (dh_mr_frequency_ratio ? 7'd4 : 7'd2) : 7'd0)
                             ;

    // (tphy_wrlat + tphy_wrdata) cycles in memory clock
    assign  wrdata_lat     = {{($bits(wrdata_lat)-$bits(wrlat_sdr)){1'b0}},wrlat_sdr}
                             + (( dh_mr_en_2t_timing_mode) ? {{($bits(wrdata_lat)-1){1'b0}},1'b1} : {$bits(wrdata_lat){1'b0}})
                             - (( reg_ddrc_wr_link_ecc_enable) ? {{($bits(wrdata_lat)-4){1'b0}},4'b1000} : {$bits(wrdata_lat){1'b0}})
                             + {{($bits(wrlat_sdr)-$bits(reg_ddrc_dfi_tphy_wrdata)){1'b0}}, reg_ddrc_dfi_tphy_wrdata};


    assign wrdata_lat_p0 = wrdata_lat;


    // (tphy_wrlat + tphy_wrdata) cycles in DFI clock
    assign  wrdata_lat_cyc = ((dh_mr_frequency_ratio) ? {{($bits(wrdata_lat_cyc)-($bits(wrdata_lat_p0)-2)){1'b0}}, wrdata_lat_p0[$bits(wrdata_lat_p0)-1:2]}:
                                                        {{($bits(wrdata_lat_cyc)-($bits(wrdata_lat_p0)-1)){1'b0}}, wrdata_lat_p0[$bits(wrdata_lat_p0)-1:1]})
                           ;

    // additional DFI command delay for WR command due to a difference btw WR data path and command path delay
    assign  wrdata_cmd_delay_wider  =
                                    (wrdata_lat_cyc > {{($bits(wrdata_cmd_delay) - $bits(wr_cmd_gap)){1'b0}},wr_cmd_gap}) ? 
                                    {$bits(wrdata_cmd_delay_wider){1'b0}} :
                                    {{($bits(wrdata_cmd_delay_wider) - $bits(wr_cmd_gap)){1'b0}},wr_cmd_gap} - wrdata_lat_cyc;
    assign  wrdata_cmd_delay        = wrdata_cmd_delay_wider[$bits(wrdata_lat)-1:0];

    always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
        if (!core_ddrc_rstn) begin
            dfi_cmd_delay <= {$bits(dfi_cmd_delay){1'b0}};
        end
        else if (wrdata_cmd_delay[$bits(dfi_cmd_delay)-1:0] > data_en_cmd_delay[$bits(dfi_cmd_delay)-1:0]) begin
            dfi_cmd_delay <= wrdata_cmd_delay[$bits(dfi_cmd_delay)-1:0];
        end
        else if (dfi_cmd_delay != data_en_cmd_delay[$bits(dfi_cmd_delay)-1:0]) begin
            dfi_cmd_delay <= data_en_cmd_delay[$bits(dfi_cmd_delay)-1:0];
        end
    end

    // ----------------------------------------------------------------------------------------
    // wrdata_en latency
    // ----------------------------------------------------------------------------------------
    // calculate wrdata_en latency from command output to wrdata_en output in pi module
    assign  wrlat_adj      =  {{($bits(wrlat_adj)-$bits(wrlat_sdr)){1'b0}}, wrlat_sdr}
                             + ((dh_mr_en_2t_timing_mode
                                ) ? {{($bits(wrlat_adj)-1){1'b0}},1'b1} : {$bits(wrlat_adj){1'b0}});

    always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
        if (!core_ddrc_rstn) begin
            mr_t_wrlat_add_sdr  <= '0;
            wrlat_adj_cyc       <= '0;
        end
        else begin
            mr_t_wrlat_add_sdr  <= (dh_mr_frequency_ratio) ? wrlat_adj[1:0] : {{($bits(wrlat_adj)-1){1'b0}},wrlat_adj[0]};
            wrlat_adj_cyc       <= (dh_mr_frequency_ratio) ? {1'b0, wrlat_adj[$bits(wrlat_adj)-1:2]} : wrlat_adj[$bits(wrlat_adj)-1:1];
        end
    end

    assign  mr_t_wrlat_wider    = wrlat_adj_cyc + {{($bits(mr_t_wrlat_wider)-$bits(dfi_cmd_delay)-1){1'b0}}, dfi_cmd_delay};
    assign  mr_t_wrlat          = mr_t_wrlat_wider[$bits(mr_t_wrlat)-1:0];


    // ----------------------------------------------------------------------------------------
    // wrdata data latency
    // ----------------------------------------------------------------------------------------   
    assign  add_wrdata_lat = 1'b0;

    // calculate wrdata_en latency from command output to wrdata_en output in pi module
    assign  wrdata_adj  = {{($bits(wrdata_adj)-$bits(wrdata_lat)){1'b0}},wrdata_lat}
                             ;

    always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
        if (!core_ddrc_rstn) begin
            mr_t_wrdata_add_sdr <= '0;
            wrdata_adj_cyc      <= '0;
        end
        else begin
            mr_t_wrdata_add_sdr <= (dh_mr_frequency_ratio) ? wrdata_adj[1:0] : {{($bits(wrdata_adj)-1){1'b0}},wrdata_adj[0]};
            wrdata_adj_cyc      <= (dh_mr_frequency_ratio) ? {1'b0, wrdata_adj[$bits(wrdata_adj)-1:2]} : wrdata_adj[$bits(wrdata_adj)-1:1];
        end
    end

    assign mr_t_wrdata_int_wider    = {1'b0,wrdata_adj_cyc}
                                    - {{($bits(mr_t_wrdata_int_wider)-$bits(wr_cmd_gap)){1'b0}},     wr_cmd_gap}
                                    + {{($bits(mr_t_wrdata_int_wider)-$bits(dfi_cmd_delay)){1'b0}},  dfi_cmd_delay}
                                    + {{($bits(mr_t_wrdata_int_wider)-$bits(add_wrdata_lat)){1'b0}}, add_wrdata_lat};
    assign mr_t_wrdata_int          = mr_t_wrdata_int_wider[DFI_TPHY_WRDATA_WIDTH-1:0];

    always @(*) begin
        begin
            mr_t_wrdata = mr_t_wrdata_int;
        end
    end


    // ----------------------------------------------------------------------------------------
    // rddata_en latency
    // ----------------------------------------------------------------------------------------

    wire [$bits(reg_ddrc_dfi_t_rddata_en)-1:0]       rdlat_sdr;
    wire [$bits(rdlat_sdr)-1:0]                    rdlat_adj;
    reg  [$bits(rdlat_adj):0]                      mr_t_rddata_en_wider;

    assign  rdlat_sdr      = {{($bits(rdlat_sdr)-$bits(reg_ddrc_dfi_t_rddata_en)){1'b0}},reg_ddrc_dfi_t_rddata_en}
                             + (reg_ddrc_lpddr4 ? {{($bits(rdlat_sdr)-2){1'b0}},2'b11} : {$bits(rdlat_sdr){1'b0}})
                             + {5'd0,gs_mr_read_ph}
                             + (reg_ddrc_lpddr5 ? (dh_mr_frequency_ratio ? 7'd4 : 7'd2) : 7'd0)
                             ;

    assign  rdlat_adj      = {{($bits(rdlat_adj)-$bits(rdlat_sdr)){1'b0}},rdlat_sdr}
                             + ((dh_mr_en_2t_timing_mode
                                ) ? {{($bits(rdlat_adj)-1){1'b0}},1'b1} : {$bits(rdlat_adj){1'b0}});

    always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
        if (!core_ddrc_rstn) begin
            mr_t_rddata_en_add_sdr <= 2'b0;
            mr_t_rddata_en_wider   <= {$bits(mr_t_rddata_en_wider){1'b0}};
        end
        else begin
            mr_t_rddata_en_add_sdr <= (dh_mr_frequency_ratio) ? rdlat_adj[1:0] : {{($bits(rdlat_adj)-1){1'b0}},rdlat_adj[0]};
            mr_t_rddata_en_wider   <= ((dh_mr_frequency_ratio) ? {{($bits(mr_t_rddata_en_wider)-($bits(rdlat_adj)-2)){1'b0}}, rdlat_adj[$bits(rdlat_adj)-1:2]} : {{($bits(mr_t_rddata_en_wider)-($bits(rdlat_adj)-2)){1'b0}}, rdlat_adj[$bits(rdlat_adj)-1:1]}) + {{($bits(mr_t_rddata_en_wider)-($bits(dfi_cmd_delay)-2)){1'b0}}, dfi_cmd_delay};
        end
    end

    assign mr_t_rddata_en = mr_t_rddata_en_wider[$bits(mr_t_rddata_en)-1:0];
    
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
  localparam CATEGORY = 5; // Allows groups of assertions to be enabled/disabled at the same time

  // mr_t_wrlat overflow
  assert_never #(0, 0, "mr_t_wrlat overflow", CATEGORY) a_mr_t_wrlat_overflow
    (co_yy_clk, core_ddrc_rstn, (mr_t_wrlat_wider[$bits(mr_t_wrlat_wider)-1]==1'b1));

  // mr_t_rddata_en overflow
  assert_never #(0, 0, "mr_t_rddata_en overflow", CATEGORY) a_mr_t_rddata_en_overflow
    (co_yy_clk, core_ddrc_rstn, (mr_t_rddata_en_wider[$bits(mr_t_rddata_en_wider)-1]==1'b1));

// comment out temporaliry because some signals are set to correct value after initialization
//  // mr_lp_data_rd overflow
//  assert_never #(0, 0, "mr_lp_data_rd overflow", CATEGORY) a_mr_lp_data_rd_overflow
//    (co_yy_clk, core_ddrc_rstn, (mr_lp_data_rd_wider[$bits(mr_lp_data_rd_wider)-1]==1'b1));
//
//  // mr_lp_data_wr overflow
//  assert_never #(0, 0, "mr_lp_data_wr overflow", CATEGORY) a_mr_lp_data_wr_overflow
//    (co_yy_clk, core_ddrc_rstn, (mr_lp_data_wr_wider[$bits(mr_lp_data_wr_wider)-1]==1'b1));
//
//  // wrdata_cmd_delay overflow
//  assert_never #(0, 0, "wrdata_cmd_delay overflow", CATEGORY) a_wrdata_cmd_delay_overflow
//    (co_yy_clk, core_ddrc_rstn, (wrdata_cmd_delay_wider[$bits(wrdata_cmd_delay_wider)-1]==1'b1));
//
//  // mr_t_wrdata_int overflow
//  assert_never #(0, 0, "mr_t_wrdata_int overflow", CATEGORY) a_mr_t_wrdata_int_overflow
//    (co_yy_clk, core_ddrc_rstn, (mr_t_wrdata_int_wider[$bits(mr_t_wrdata_int_wider)-1]==1'b1));

`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON  

endmodule
