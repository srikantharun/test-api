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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/mr/mr.sv#8 $
// -------------------------------------------------------------------------
// Description:
//                Memory Read Engine.  This unit takes the write command
//                from GS & TE, controls reading data out of the write data
//                RAM, performs ECC encoding if necessary, and sends the
//                data to memory when a write is performed.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module mr 
import DWC_ddrctl_reg_pkg::*;
#(
   parameter CORE_DATA_WIDTH     = `MEMC_DFI_DATA_WIDTH       // internal data width
  ,parameter CORE_MASK_WIDTH     = `MEMC_DFI_DATA_WIDTH/8     // data mask width
  ,parameter CORE_METADATA_WIDTH = `DDRCTL_HIF_METADATA_WIDTH    // data mask width
  ,parameter WRSRAM_DATA_WIDTH   = `MEMC_DFI_DATA_WIDTH       // WR-SRAM data width
  ,parameter WRSRAM_MASK_WIDTH   = `MEMC_DFI_DATA_WIDTH/8     // WR-SRAM data mask width
  ,parameter CORE_DCERRBITS      = `MEMC_DCERRBITS

  ,parameter PHY_DATA_WIDTH      = `MEMC_DFI_TOTAL_DATA_WIDTH   // width of data to the PHY
                                                                 // (should be 2x the DDR DQ width)
  ,parameter PHY_MASK_WIDTH      = PHY_DATA_WIDTH/8             // width of data mask bits to the PHY
                                                       // (note that if both ECC and DM
                                                       //  are supported in a system:
                                                       //  1) Only one or the other allowed at any given time
                                                       //  2) ECC byte enable need not be maskable           )

  ,parameter WRCAM_ADDR_WIDTH      = 4                          // bits to address into CAM
  ,parameter WRCAM_ADDR_WIDTH_IE   = 0                          // bits to address into CAM
  ,parameter WRDATA_RAM_ADDR_WIDTH = WRCAM_ADDR_WIDTH + 1  // data width to RAM
  ,parameter PARTIAL_WR_BITS       = `UMCTL2_PARTIAL_WR_BITS
  ,parameter PW_WORD_CNT_WD_MAX    = 2
  ,parameter PARTIAL_WR_BITS_LOG2  = `log2(PARTIAL_WR_BITS)
  ,parameter OCPAR_EN              = 0 // enables on-chip parity
  ,parameter ECC_POISON_REG_WIDTH  = `ECC_POISON_REG_WIDTH
   
  ,parameter WRDATA_CYCLES         = 2
  ,parameter CMD_LEN_BITS          = 1

  ,parameter NUM_RANKS             = `MEMC_NUM_RANKS

  ,parameter NO_OF_BWT             = 16
  ,parameter IE_WR_TYPE_BITS       = 2
  ,parameter IE_BURST_NUM_BITS     = 3
  ,parameter ECC_ERR_RAM_WIDTH     = 16 //MEMC_WRDATA_CYCLES*SECDED_LANES;
  ,parameter ECC_INFO_WIDTH        = 35
  ,parameter BWT_BITS              = 4
  ,parameter BRT_BITS              = 4
  ,parameter BT_BITS               = 4
  ,parameter ECC_RAM_ADDR_BITS     = `log2(`MEMC_ECC_RAM_DEPTH)
  ,parameter ECC_ERR_RAM_ADDR_BITS = 4
  ,parameter WDATARAM_RD_LATENCY   = `DDRCTL_WDATARAM_RD_LATENCY
  ,parameter MAX_CMD_DELAY         = `UMCTL2_MAX_CMD_DELAY
  ,parameter CMD_DELAY_BITS        = `UMCTL2_CMD_DELAY_BITS
  
  ,parameter OCECC_EN              = 0
  ,parameter OCECC_MR_RD_GRANU     = 8
  ,parameter WDATA_PAR_WIDTH       = `UMCTL2_WDATARAM_PAR_DW
  ,parameter WDATA_PAR_WIDTH_EXT   = `UMCTL2_WDATARAM_PAR_DW_EXT
  ,parameter DRAM_BYTE_NUM         = `MEMC_DRAM_TOTAL_BYTE_NUM
  ,parameter DFI_KBD_WIDTH         = `DDRCTL_DFI_KBD_WIDTH
)
(     
   input           co_yy_clk                              // clock
  ,input           core_ddrc_rstn                         // asynchronous negative-edge reset
  ,input           ddrc_cg_en                             // clock gating enable
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used only in sideband ECC configs, but keeping input available for all ECC configs for debug purposes.
  ,input           reg_ddrc_ecc_type                         
  ,input [2:0]     dh_mr_ecc_mode                         // ECC mode:
                                                        //  000: No ECC
                                                        //  001: Reserved
                                                        //  010: Parity
                                                        //  011: Reserved
                                                        //  100: SEC/DED ECC over 1 beat
                                                        //  101: SEC/DED ECC over multiple beats
                                                        //  110: Device Correction ECC
                                                        //  111: Reserved
//spyglass enable_block W240
  ,input [1:0]     dh_mr_data_bus_width                   // Width of the DRAM data bus:
                                                        //  00: Full bus width
                                                        //  01: Half bus width
                                                        //  10: Quarter bus width
                                                        //  11: unused 
  ,input           dh_mr_en_2t_timing_mode                // 2T timing enable, send write data one clock later
  ,input           dh_mr_frequency_ratio                  // 0 - 1:2 mode, 1 - 1:1 mode
  ,input           dh_mr_lpddr4                           // LPDDR4 mode
  ,input           reg_ddrc_lpddr5                        // LPDDR5 mode
  ,input           reg_ddrc_lp_optimized_write            // To save power consumption LPDDR4 write DQ is set to 8'hF8 if this is set to 1 (masked + DBI)
  ,input           ts_pi_mwr 
  ,output          mr_te_half_clear_en
  ,input           gs_mr_write                            // write command issued this cycle 
//`ifdef MEMC_FREQ_RATIO_4
  ,input [1:0]     gs_mr_write_ph                         // indicates that write command phase
  ,input [1:0]     gs_mr_read_ph                          // indicates that read command phase
//`endif // MEMC_FREQ_RATIO_4
  ,input [WRCAM_ADDR_WIDTH_IE-1:0] te_mr_wr_ram_addr// write RAM address

  ,input   [PARTIAL_WR_BITS-1:0]   te_pi_wr_word_valid
  ,input   [PARTIAL_WR_BITS_LOG2-1:0]      te_mr_ram_raddr_lsb_first
  ,input   [PW_WORD_CNT_WD_MAX-1:0]        te_mr_pw_num_beats_m1
   
   
//,input [CORE_DATA_WIDTH-1:0]     me_mr_rdata    // write data read from write data RAM
  ,input [CORE_MASK_WIDTH-1:0]     me_mr_rdatamask// write data read from write data RAM
  ,input [WRSRAM_DATA_WIDTH-1:0]   me_mr_rdata    // write data read from write data RAM
//,input [WRSRAM_MASK_WIDTH-1:0]   me_mr_rdatamask// write data read from write data RAM
  ,output [PHY_MASK_WIDTH-1:0]     mr_ph_wdatamask// write data output to phy with ECC
  ,output [PHY_MASK_WIDTH-1:0]     mr_ph_wdatamask_retry// write data output to retry with ECC

  ,input [WDATA_PAR_WIDTH_EXT-1:0] me_mr_rdatapar
  ,output [WRDATA_RAM_ADDR_WIDTH-1:0]  mr_wu_cerr_addr           // read address to write data RAM
   
  ,output [WRDATA_RAM_ADDR_WIDTH-1:0] mr_wu_raddr    // read address to wu module
  ,output [WRDATA_RAM_ADDR_WIDTH-1:0] mr_me_raddr    // read address to write data RAM
  ,output                             mr_me_re       // read enable: enables the RAM read path
  ,output                             mr_me_re_last
  ,output [PHY_DATA_WIDTH-1:0]        mr_ph_wdata    // write data output to phy with ECC
  ,output [PHY_DATA_WIDTH-1:0]        mr_ph_wdata_retry    // write data output to retry with ECC
                                                      //  encoding, valid only with
                                                      //  mr_ph_datavld=1
  ,output                             mr_re_wdata_lsb_sel
  ,input                              reg_ddrc_wr_link_ecc_enable
  ,input  [DRAM_BYTE_NUM-1:0]         reg_ddrc_linkecc_poison_byte_sel
  ,input  [DRAM_BYTE_NUM-1:0]         reg_ddrc_linkecc_poison_dmi_sel
  ,input                              reg_ddrc_linkecc_poison_rw
  ,input                              reg_ddrc_linkecc_poison_type
  ,input                              reg_ddrc_linkecc_poison_inject_en
  ,output [CORE_MASK_WIDTH-1:0]       dfi_wrdata_ecc
  ,output                             ddrc_reg_wr_linkecc_poison_complete
  ,output                             mr_ph_wdatavld_early   // write data valid to phy - comes one clock earlier than mr_ph_wdatavld
  ,output                             mr_ph_wdatavld_early_retry   // write data valid to retry
  ,output                             mr_yy_free_wr_entry_valid// done with this write entry
  ,output [WRCAM_ADDR_WIDTH_IE-1:0]      mr_yy_free_wr_entry    //write RAM to be used by TE
                                                              //  to return this entry to
                                                              //  the pool of available entries
                                                              // (qualified by mr_yy_free_wr_entry_valid) 
  ,output                             mr_gs_empty    // MR pipeline is empty
                                                      // (used to issue DFI controller update)

  ,output [NUM_RANKS-1:0]  mr_wr_empty_per_rank   // MR is idle, OK to powerdown

  ,input                              oc_parity_en // enables on-chip parity
  ,input                              oc_parity_type // selects parity type. 0 even, 1 odd

  ,output                             wdata_par_err
  ,output [CORE_MASK_WIDTH-1:0]       wdata_par_err_vec
  ,output                             wdata_par_err_ie

  ,input                              reg_ddrc_phy_dbi_mode
  ,input                              reg_ddrc_wr_dbi_en
  ,input                              reg_ddrc_dm_en
  ,input [BURST_RDWR_WIDTH-1:0]       reg_ddrc_burst_rdwr
   
  ,output                             ddrc_reg_crc_poison_inject_complete

   // TE to MR for receive data
  ,input  [BT_BITS-1:0]               te_mr_ie_bt
  ,input  [IE_WR_TYPE_BITS-1:0]       te_mr_ie_wr_type
  ,input  [IE_BURST_NUM_BITS-1:0]     te_mr_ie_blk_burst_num  //only for the Data command
  // IH to MR for load BWT
  ,input  [BRT_BITS-1:0]              ih_mr_ie_brt
  ,input                              ih_mr_ie_brt_vld
  ,input  [BWT_BITS-1:0]              ih_mr_ie_bwt       
  ,input  [NO_OF_BWT-1:0]             ih_mr_ie_wr_cnt_dec_vct
  ,input                              ih_mr_ie_wr_cnt_inc
  ,input                              ih_mr_ie_blk_wr_end

   ,input                              rd_mr_free_brt_vld
   ,input  [BRT_BITS-1:0]              rd_mr_free_brt

   ,input  [BWT_BITS-1:0]              ih_mr_lkp_bwt
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in RTL assertion
   ,input                              ih_mr_lkp_bwt_vld
//spyglass enable_block W240
   ,input  [BRT_BITS-1:0]              ih_mr_lkp_brt
   ,input                              ih_mr_lkp_brt_vld
// ECC ACC and ECC RAM interface
   ,input  [CORE_DATA_WIDTH-1:0]       ecc_acc_mr_rdata
   ,input  [CORE_MASK_WIDTH-1:0]       ecc_acc_mr_rdata_par
   ,input  [CORE_MASK_WIDTH-1:0]       ecc_acc_mr_rdata_mask_n
   ,input  [CORE_DATA_WIDTH-1:0]       ecc_ram_mr_rdata_2
   ,input  [CORE_MASK_WIDTH-1:0]       ecc_ram_mr_rdata_par_2
   ,input  [ECC_ERR_RAM_WIDTH-1:0]     ecc_err_mr_rdata
   // MR to IH for free BWT
   ,output                             mr_ih_free_bwt_vld
   ,output [BWT_BITS-1:0]              mr_ih_free_bwt
 
   ,output [BT_BITS-1:0]               mr_ih_lkp_bwt_by_bt
   ,output [BT_BITS-1:0]               mr_ih_lkp_brt_by_bt
// ECC ACC and ECC RAM interface
   ,output                             mr_ecc_acc_wr
   ,output [ECC_RAM_ADDR_BITS-1:0]     mr_ecc_acc_waddr
   ,output [CORE_DATA_WIDTH-1:0]       mr_ecc_acc_wdata
   ,output [CORE_MASK_WIDTH-1:0]       mr_ecc_acc_wdata_par
   ,output [CORE_MASK_WIDTH-1:0]       mr_ecc_acc_wdata_mask_n
   ,output                             mr_ecc_acc_rd
   ,output [ECC_RAM_ADDR_BITS-1:0]     mr_ecc_acc_raddr
   ,output [ECC_RAM_ADDR_BITS-1:0]     mr_ecc_ram_raddr_2
   ,output                             mr_ecc_err_rd
   ,output [ECC_ERR_RAM_ADDR_BITS-1:0] mr_ecc_err_raddr
   ,output                             mr_ecc_acc_flush_en
   ,output [BWT_BITS-1:0]              mr_ecc_acc_flush_addr
 
   ,input                    te_mr_eccap

    ,input  [DFI_T_RDDATA_EN_WIDTH-1:0] reg_ddrc_dfi_t_rddata_en    // t_rddata_en parameter from dfi spec
    ,input  [DFI_TPHY_WRLAT_WIDTH-1:0]  reg_ddrc_dfi_tphy_wrlat     // write latency (command to data latency)
    ,input  [DFI_TPHY_WRDATA_WIDTH-1:0] reg_ddrc_dfi_tphy_wrdata    // tphy_wrdata parameter from dfi spec
    ,input                              reg_ddrc_dfi_lp_en_data

    ,input  [DFI_TWCK_EN_RD_WIDTH-1:0]  reg_ddrc_dfi_twck_en_rd     // WCK enable read timing
    ,input  [DFI_TWCK_EN_WR_WIDTH-1:0]  reg_ddrc_dfi_twck_en_wr     // WCK enable write timing
    ,input                              reg_ddrc_wck_on
    ,input  [`MEMC_NUM_RANKS-1:0]       reg_ddrc_active_ranks
    ,input  [DFI_TWCK_EN_FS_WIDTH-1:0]  reg_ddrc_dfi_twck_en_fs
    ,input  [EXTRA_GAP_FOR_DFI_LP_DATA_WIDTH-1:0]  reg_ddrc_extra_gap_for_dfi_lp_data

    ,output [CMD_DELAY_BITS-1:0]        dfi_cmd_delay
    ,output [CMD_DELAY_BITS-1:0]        ddrc_reg_dfi_cmd_delay
    ,output [1:0]                       mr_t_wrlat_add_sdr
    ,output [DFI_TPHY_WRLAT_WIDTH-1:0]  mr_t_wrlat
    ,output [1:0]                       mr_t_wrdata_add_sdr
    ,output [DFI_TPHY_WRDATA_WIDTH-1:0] mr_t_wrdata
    ,output [1:0]                       mr_t_rddata_en_add_sdr
    ,output [DFI_T_RDDATA_EN_WIDTH-1:0] mr_t_rddata_en
    ,output [DFI_TWCK_EN_RD_WIDTH-2:0]  mr_lp_data_rd
    ,output [DFI_TWCK_EN_WR_WIDTH-2:0]  mr_lp_data_wr

//unused port, tobe removed, 
//keep it just for avoiding re-numbering or number check error.
  ,output [1:0]                       mr_wu_ie_rmw_type
  ,output [WRDATA_RAM_ADDR_WIDTH-1:0] mr_wu_ie_wr_ram_addr
  ,output [CORE_DATA_WIDTH-1:0]       mr_wu_ie_wdata
  ,output [CORE_DATA_WIDTH/8-1:0]     mr_wu_ie_wdata_mask_n
  ,output [CORE_MASK_WIDTH-1:0]       mr_wu_ie_wdatapar 
  ,output                             mr_wu_ie_wdata_valid
  ,output                             mr_wu_ie_wdata_end

  ,input                                          ocecc_en
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in MEMC_INLINE_ECC-UMCTL2_OCPAR_OR_OCECC_EN_1 configs only, but input should always exist for debug purposes.
  ,input                                          ocecc_poison_pgen_mr_ecc
  ,input                                          ocecc_uncorr_err_intr_clr
//spyglass enable_block W240

// ocecc err outputs
  ,output                                         ocecc_mr_rd_corr_err
  ,output                                         ocecc_mr_rd_uncorr_err
  ,output [CORE_DATA_WIDTH/OCECC_MR_RD_GRANU-1:0] ocecc_mr_rd_byte_num
,output [CORE_DCERRBITS-1:0]                      mr_ph_dbg_dfi_ecc_corrupt0
,output [CORE_DCERRBITS-1:0]                      mr_ph_dbg_dfi_ecc_corrupt1
,output [CORE_DCERRBITS-1:0]                      mr_ph_dbg_dfi_rmw_ucerr_corrupt
,output [4-1:0]                                   mr_ph_dbg_dfi_ecc_dram_beat_1_9_pos
,output [DFI_KBD_WIDTH-1:0]                       mr_ph_dbg_dfi_ecc_wdata_kbd
,output [CORE_METADATA_WIDTH-1:0]                 mr_ph_wdata_meta                                                                  
// ,output                                           mr_ph_dbg_dfi_poison_advecc_kbd

,output [0:0]                                    mr_crc_bc_second_ras_model 
);

//---------------------------- PARAMETERS --------------------------------------

//------------------------------------------------------------
//unused parot, tobe removed, 
//keep it just for avoiding re-numbering or number mismatch.

  assign mr_me_re_last          = 1'b0;
   assign mr_re_wdata_lsb_sel = 1'b0;
  assign mr_te_half_clear_en = 1'b0;
      

  assign mr_wu_ie_rmw_type      = {2{1'b0}};         
  assign mr_wu_ie_wr_ram_addr   = {WRDATA_RAM_ADDR_WIDTH{1'b0}};         
  assign mr_wu_ie_wdata         = {CORE_DATA_WIDTH{1'b0}};         
  assign mr_wu_ie_wdata_mask_n  = {(CORE_DATA_WIDTH/8){1'b0}};         
  assign mr_wu_ie_wdatapar      = {CORE_MASK_WIDTH{1'b0}};         
  assign mr_wu_ie_wdata_valid   = {1{1'b0}};         
  assign mr_wu_ie_wdata_end     = {1{1'b0}};         
//-------------------------------- WIRES ---------------------------------------
   wire                                          ram_data_vld;           // data out of the write data RAM is valid
   wire                                          ram_data_vld_upper_lane;// data out of the write data RAM is valid for prog freq ratio 1:1



  wire [CORE_DATA_WIDTH-1:0]     me_mr_rdata_mux;     //mux between ECC and Data 
  wire [CORE_MASK_WIDTH-1:0]     me_mr_rdatamask_mux; //mux between ECC and Data
  wire [CORE_MASK_WIDTH-1:0]     me_mr_rdatapar_mux;  //mux between ECC and Data
  wire                           wr_ecc_vld;
  wire [CORE_DATA_WIDTH-1:0]     ecc_wdata;
  wire [CORE_MASK_WIDTH-1:0]     ecc_wdata_par;
  wire [CORE_DATA_WIDTH/8-1:0]   ecc_wdata_mask_n;

   // signals from mr_ram_rd_pipeline
   wire                          mr_ram_rd_cmd; // from mr_ram_rd_pipeline // a new command
   wire [WRDATA_RAM_ADDR_WIDTH-1:0] mr_me_raddr_ie;    // read address to write data RAM
   wire                          ie_mwr_flag; // from mr_ram_rd_pipeline // mwr_flag
   // TE to MR for receive data
   wire  [BT_BITS-1:0]           i_te_mr_ie_bt;  //from mr_ram_rd_pipeline to ie_wdata_ctl
   wire  [BWT_BITS-1:0]          i_te_mr_ie_bwt;  //from mr_ram_rd_pipeline to ie_wdata_ctl
   wire  [BRT_BITS-1:0]          i_te_mr_ie_brt;  //from mr_ram_rd_pipeline to ie_wdata_ctl
   wire                          i_te_mr_ie_brt_vld;  //from mr_ram_rd_pipeline to ie_wdata_ctl
   wire  [IE_WR_TYPE_BITS-1:0]   i_te_mr_ie_wr_type;  //from mr_ram_rd_pipeline to ie_wdata_ctl
   wire  [IE_BURST_NUM_BITS-1:0] i_te_mr_ie_blk_burst_num;    //from mr_ram_rd_pipeline to ie_wdata_ctl //only for the Data command
   wire                          ram_data_vld_early;
   wire                          i_te_mr_eccap;
   //----------------------- drive undriven outputs -----------------------------
  assign mr_wu_cerr_addr = {WRDATA_RAM_ADDR_WIDTH{1'b0}};

   wire  [CORE_DATA_WIDTH-1:0]     mr_rdata;
   wire  [CORE_MASK_WIDTH-1:0]     mr_rdatamask;
   wire  [CORE_MASK_WIDTH-1:0]     mr_rdatapar;

  wire                            wdata_par_err_w;

   assign wdata_par_err = wdata_par_err_w; 



   assign mr_wr_empty_per_rank    = {NUM_RANKS{1'b1}};

//`ifdef MEMC_FREQ_RATIO_4
wire [1:0]  wr_ph;
//`endif // MEMC_FREQ_RATIO_4

// mr_crc_bc_second_ras_model is to RAS verification model, customer not use this signal 
// mr_crc_bc_second is two clock eariler than WRDATA to RAS verification model
// if we use RAS verification model, MEMC_DDR5 must be enable, because we use it only in DDR5 mode
    assign mr_crc_bc_second_ras_model = 1'd0;

   assign ddrc_reg_crc_poison_inject_complete = 1'b0;



reg [CMD_DELAY_BITS-1:0]    dfi_cmd_delay_1d;
reg [CMD_DELAY_BITS-1:0]    dfi_cmd_delay_2d;

always @ (posedge co_yy_clk or negedge core_ddrc_rstn)
begin
   if(~core_ddrc_rstn) begin
      dfi_cmd_delay_1d <= {CMD_DELAY_BITS{1'b0}};
      dfi_cmd_delay_2d <= {CMD_DELAY_BITS{1'b0}};
   end else begin
      if (dfi_cmd_delay_1d != dfi_cmd_delay) begin
         dfi_cmd_delay_1d <= dfi_cmd_delay;
      end
      if (dfi_cmd_delay_2d != dfi_cmd_delay_1d) begin
         dfi_cmd_delay_2d <= dfi_cmd_delay_1d;
      end
   end
end

assign ddrc_reg_dfi_cmd_delay = dfi_cmd_delay_2d;


   //----------------------- COMPONENT INSTANTIATIONS -----------------------------
    mr_latency_calc
     #(
        .MAX_CMD_DELAY                          (MAX_CMD_DELAY),
        .CMD_DELAY_BITS                         (CMD_DELAY_BITS)
    )
    mr_latency_calc (

        .co_yy_clk                              (co_yy_clk),
        .core_ddrc_rstn                         (core_ddrc_rstn),

        .dh_mr_frequency_ratio                  (dh_mr_frequency_ratio),
        .dh_mr_en_2t_timing_mode                (dh_mr_en_2t_timing_mode),
        .reg_ddrc_lpddr4                        (dh_mr_lpddr4),
        .reg_ddrc_lpddr5                        (reg_ddrc_lpddr5),
        .reg_ddrc_dfi_twck_en_rd                (reg_ddrc_dfi_twck_en_rd),
        .reg_ddrc_dfi_twck_en_wr                (reg_ddrc_dfi_twck_en_wr),
        .reg_ddrc_wck_on                        (reg_ddrc_wck_on),
        .reg_ddrc_active_ranks                  (reg_ddrc_active_ranks),
        .reg_ddrc_dfi_twck_en_fs                (reg_ddrc_dfi_twck_en_fs),
        .reg_ddrc_extra_gap_for_dfi_lp_data     (reg_ddrc_extra_gap_for_dfi_lp_data),
        .reg_ddrc_wr_link_ecc_enable            (reg_ddrc_wr_link_ecc_enable),
        .reg_ddrc_dfi_t_rddata_en               (reg_ddrc_dfi_t_rddata_en),
        .reg_ddrc_dfi_tphy_wrlat                (reg_ddrc_dfi_tphy_wrlat),
        .reg_ddrc_dfi_tphy_wrdata               (reg_ddrc_dfi_tphy_wrdata),
        .reg_ddrc_dfi_lp_en_data                (reg_ddrc_dfi_lp_en_data),
//`ifdef MEMC_FREQ_RATIO_4
        .gs_mr_write_ph                         (gs_mr_write_ph),
        .gs_mr_read_ph                          (gs_mr_read_ph),
//`endif // MEMC_FREQ_RATIO_4
        .dfi_cmd_delay                          (dfi_cmd_delay),
        .mr_lp_data_rd                          (mr_lp_data_rd),
        .mr_lp_data_wr                          (mr_lp_data_wr),
        .mr_t_wrlat_add_sdr                     (mr_t_wrlat_add_sdr),
        .mr_t_wrlat                             (mr_t_wrlat),
        .mr_t_wrdata_add_sdr                    (mr_t_wrdata_add_sdr),
        .mr_t_wrdata                            (mr_t_wrdata),
        .mr_t_rddata_en_add_sdr                 (mr_t_rddata_en_add_sdr),
        .mr_t_rddata_en                         (mr_t_rddata_en)

);


   // Take write indicator from TE, generate timing and control for reading
   //  the data out of the write data RAM
   mr_ram_rd_pipeline
    #(
               .WRCAM_ADDR_WIDTH       (WRCAM_ADDR_WIDTH)
              ,.WRCAM_ADDR_WIDTH_IE    (WRCAM_ADDR_WIDTH_IE)
              ,.WRDATA_RAM_ADDR_WIDTH  (WRDATA_RAM_ADDR_WIDTH)
              ,.WRDATA_CYCLES          (WRDATA_CYCLES)
              ,.CMD_LEN_BITS           (CMD_LEN_BITS)
              ,.NUM_RANKS              (NUM_RANKS)
              ,.WDATARAM_RD_LATENCY    (WDATARAM_RD_LATENCY)
              ,.PARTIAL_WR_BITS        (PARTIAL_WR_BITS)
              ,.PARTIAL_WR_BITS_LOG2   (PARTIAL_WR_BITS_LOG2)
              ,.PW_WORD_CNT_WD_MAX     (PW_WORD_CNT_WD_MAX)
              ,.BT_BITS                (BT_BITS          )
              ,.BWT_BITS               (BWT_BITS         )
              ,.BRT_BITS               (BRT_BITS         )
              ,.IE_WR_TYPE_BITS        (IE_WR_TYPE_BITS  )
              ,.IE_BURST_NUM_BITS      (IE_BURST_NUM_BITS)
              ,.CORE_DATA_WIDTH        (CORE_DATA_WIDTH    )
              ,.CORE_MASK_WIDTH        (CORE_MASK_WIDTH    )
              ,.WRSRAM_DATA_WIDTH      (WRSRAM_DATA_WIDTH  )
              ,.WRSRAM_MASK_WIDTH      (WRSRAM_MASK_WIDTH  )
              ,.CORE_DCERRBITS         (CORE_DCERRBITS     )
              ,.OCECC_EN               (OCECC_EN           )
              ,.OCECC_MR_RD_GRANU      (OCECC_MR_RD_GRANU  )
              ,.WDATA_PAR_WIDTH        (WDATA_PAR_WIDTH    )
              ,.WDATA_PAR_WIDTH_EXT    (WDATA_PAR_WIDTH_EXT)
)
   mr_ram_rd_pipeline (
                       
                       // Outputs
                       .mr_me_raddr                       (mr_me_raddr[WRDATA_RAM_ADDR_WIDTH-1:0]),
                       .mr_me_re                          (mr_me_re),
                       .mr_wu_raddr                       (mr_wu_raddr),
                       .ram_data_vld                      (ram_data_vld),
                       .ram_data_vld_early                (ram_data_vld_early),
                       .ram_data_vld_upper_lane           (ram_data_vld_upper_lane),
                       .mr_yy_free_wr_entry               (mr_yy_free_wr_entry[WRCAM_ADDR_WIDTH_IE-1:0]),
                       .mr_yy_free_wr_entry_valid         (mr_yy_free_wr_entry_valid),
                       .mr_gs_empty                       (mr_gs_empty),
                       
                       // Inputs
                       .co_yy_clk                         (co_yy_clk),
                       .core_ddrc_rstn                    (core_ddrc_rstn),
                       .ddrc_cg_en                        (ddrc_cg_en),
                       .mr_t_wrdata                       (mr_t_wrdata),
                       .dh_mr_frequency_ratio             (dh_mr_frequency_ratio)
                      ,.reg_ddrc_wr_link_ecc_enable       (reg_ddrc_wr_link_ecc_enable)
                       ,.reg_ddrc_lpddr4                  (dh_mr_lpddr4)
                       ,.ts_pi_mwr                        (ts_pi_mwr)
                       ,.gs_mr_write                      (gs_mr_write)
//`ifdef MEMC_FREQ_RATIO_4
                       ,.mr_t_wrdata_add_sdr              (mr_t_wrdata_add_sdr)
                       ,.wr_ph                            (wr_ph)
//`endif // MEMC_FREQ_RATIO_4
                       ,.te_mr_wr_ram_addr                (te_mr_wr_ram_addr[WRCAM_ADDR_WIDTH_IE-1:0])
                       ,.te_pi_wr_word_valid              (te_pi_wr_word_valid)
                       ,.te_mr_ram_raddr_lsb_first        (te_mr_ram_raddr_lsb_first)
                       ,.te_mr_pw_num_beats_m1            (te_mr_pw_num_beats_m1)

//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
                       ,.reg_ddrc_burst_rdwr              (reg_ddrc_burst_rdwr)
                       ,.mr_ram_rd_cmd           (mr_ram_rd_cmd          ) 
                       ,.mr_me_raddr_ie          (mr_me_raddr_ie         ) 
                       ,.ie_mwr_flag             (ie_mwr_flag                ) 
                       ,.te_mr_ie_bt             (te_mr_ie_bt             )
                       ,.te_mr_ie_bwt            (ih_mr_lkp_bwt           )
                       ,.te_mr_ie_brt            (ih_mr_lkp_brt           )
                       ,.te_mr_ie_brt_vld        (ih_mr_lkp_brt_vld       )
                       ,.te_mr_ie_wr_type        (te_mr_ie_wr_type        )
                       ,.te_mr_ie_blk_burst_num  (te_mr_ie_blk_burst_num  )//only for the Data command
                       ,.i_te_mr_ie_bt           (i_te_mr_ie_bt           )
                       ,.i_te_mr_ie_bwt          (i_te_mr_ie_bwt          )
                       ,.i_te_mr_ie_brt          (i_te_mr_ie_brt          ) //from mr_ram_rd_pipeline to ie_wdata_ctl
                       ,.i_te_mr_ie_brt_vld      (i_te_mr_ie_brt_vld      )
                       ,.i_te_mr_ie_wr_type      (i_te_mr_ie_wr_type      ) //from mr_ram_rd_pipeline to ie_wdata_ctl
                       ,.i_te_mr_ie_blk_burst_num(i_te_mr_ie_blk_burst_num) //from mr_ram_rd_pipeline to ie_wdata_ctl //only for the Data command
                       ,.te_mr_eccap             (te_mr_eccap)
                       ,.i_te_mr_eccap           (i_te_mr_eccap) 

                       ,.me_mr_rdata             (me_mr_rdata           )
                       ,.me_mr_rdatamask         (me_mr_rdatamask       )
                       ,.me_mr_rdatapar          (me_mr_rdatapar        )
                       ,.mr_rdata                (mr_rdata           )
                       ,.mr_rdatamask            (mr_rdatamask       )
                       ,.mr_rdatapar             (mr_rdatapar        )
                       ,.ocecc_en                (ocecc_en)
                       ,.ocecc_mr_rd_corr_err    (ocecc_mr_rd_corr_err)
                       ,.ocecc_mr_rd_uncorr_err  (ocecc_mr_rd_uncorr_err)
                       ,.ocecc_mr_rd_byte_num    (ocecc_mr_rd_byte_num)
                       );
      
   // Steer data to output from appropriate ECC encoder
   // uses 256 input bits (of 288 provided); output is 288 or 144 bits, depending on data_bus_width
   mr_data_steering
    #(
                      .CORE_DATA_WIDTH     (CORE_DATA_WIDTH),      // assumes core data can drive ECC bits
                      .CORE_MASK_WIDTH     (CORE_MASK_WIDTH),      // assumes core data can drive ECC bits
                      .CORE_METADATA_WIDTH (CORE_METADATA_WIDTH),      // assumes core data can drive ECC bits
                      .OCPAR_EN            (OCPAR_EN),
                      .OCECC_EN            (OCECC_EN),
                      .ECC_POISON_REG_WIDTH(ECC_POISON_REG_WIDTH),
                      .CORE_DCERRBITS      (CORE_DCERRBITS),
                      .DRAM_BYTE_NUM       (DRAM_BYTE_NUM)
                     ,.DFI_KBD_WIDTH          (DFI_KBD_WIDTH)
                      )

   mr_data_steering (
                     
                     // Outputs
                     .mr_ph_wdata                   (mr_ph_wdata[PHY_DATA_WIDTH-1:0]),
                     .dfi_wrdata_ecc                (dfi_wrdata_ecc),
                     .ddrc_reg_wr_linkecc_poison_complete (ddrc_reg_wr_linkecc_poison_complete),
                     .mr_ph_wdatamask               (mr_ph_wdatamask[PHY_MASK_WIDTH-1:0]),
                     .mr_ph_wdatavld_early          (mr_ph_wdatavld_early),
                     .mr_ph_wdata_retry             (mr_ph_wdata_retry[PHY_DATA_WIDTH-1:0]),
                     .mr_ph_wdatamask_retry         (mr_ph_wdatamask_retry[PHY_MASK_WIDTH-1:0]),
                     .mr_ph_wdatavld_early_retry    (mr_ph_wdatavld_early_retry),
                     
                     // Inputs
                     .co_yy_clk                     (co_yy_clk),
                     .core_ddrc_rstn                (core_ddrc_rstn),
                     .ddrc_cg_en                    (ddrc_cg_en),
                     .dh_mr_frequency_ratio         (dh_mr_frequency_ratio),
                     .dh_mr_data_bus_width          (dh_mr_data_bus_width),
                     .me_mr_rdata                   (me_mr_rdata_mux[CORE_DATA_WIDTH-1:0]),    // read data with no ecc

                     .reg_ddrc_wr_link_ecc_enable       (reg_ddrc_wr_link_ecc_enable),
                     .reg_ddrc_linkecc_poison_byte_sel  (reg_ddrc_linkecc_poison_byte_sel),
                     .reg_ddrc_linkecc_poison_dmi_sel   (reg_ddrc_linkecc_poison_dmi_sel),
                     .reg_ddrc_linkecc_poison_rw        (reg_ddrc_linkecc_poison_rw),
                     .reg_ddrc_linkecc_poison_type      (reg_ddrc_linkecc_poison_type),
                     .reg_ddrc_linkecc_poison_inject_en (reg_ddrc_linkecc_poison_inject_en),
                     .oc_parity_en                  (oc_parity_en),
                     .oc_parity_type                (oc_parity_type),
                     
                     .ocecc_en                      (ocecc_en),

                     .wr_ecc_vld                    (wr_ecc_vld),
                     .wdata_par_err                 (wdata_par_err_w),
                     .wdata_par_err_vec             (wdata_par_err_vec),

                     .reg_ddrc_phy_dbi_mode         (reg_ddrc_phy_dbi_mode),
                     .reg_ddrc_wr_dbi_en            (reg_ddrc_wr_dbi_en),
                     .reg_ddrc_dm_en                (reg_ddrc_dm_en),
                     .reg_ddrc_lpddr4               (dh_mr_lpddr4),
                     .reg_ddrc_lpddr5               (reg_ddrc_lpddr5),
                     .reg_ddrc_lp_optimized_write   (reg_ddrc_lp_optimized_write),
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
                     .ram_data_vld                  (ram_data_vld),
                     .ram_data_vld_upper_lane       (ram_data_vld_upper_lane),
//`ifdef MEMC_FREQ_RATIO_4
                     .wr_ph                         (wr_ph),
//`else  // MEMC_FREQ_RATIO_4
//                     .mr_t_wrdata_add_sdr           (mr_t_wrdata_add_sdr),
//`endif // MEMC_FREQ_RATIO_4
                     
                     .mr_ph_dbg_dfi_ecc_corrupt0      (mr_ph_dbg_dfi_ecc_corrupt0),
                     .mr_ph_dbg_dfi_ecc_corrupt1      (mr_ph_dbg_dfi_ecc_corrupt1),
                     .mr_ph_dbg_dfi_ecc_wdata_kbd     (mr_ph_dbg_dfi_ecc_wdata_kbd),
                     .mr_ph_dbg_dfi_rmw_ucerr_corrupt (mr_ph_dbg_dfi_rmw_ucerr_corrupt),
                     .mr_ph_dbg_dfi_ecc_dram_beat_1_9_pos (mr_ph_dbg_dfi_ecc_dram_beat_1_9_pos),
                     .mr_ph_wdata_meta                (mr_ph_wdata_meta),
                     // .mr_ph_dbg_dfi_poison_advecc_kbd (mr_ph_dbg_dfi_poison_advecc_kbd),
                     .me_mr_rdatamask               (me_mr_rdatamask_mux[CORE_MASK_WIDTH-1:0]),
                     .me_mr_rdatapar                (me_mr_rdatapar_mux[CORE_MASK_WIDTH-1:0]));

//MUX between wdata of ECC command and wdata of other commands
   assign me_mr_rdata_mux     = wr_ecc_vld ? ecc_wdata        : mr_rdata;
   assign me_mr_rdatapar_mux  = wr_ecc_vld ? ecc_wdata_par    : mr_rdatapar; 
   assign me_mr_rdatamask_mux = wr_ecc_vld ? ecc_wdata_mask_n : mr_rdatamask;

   assign mr_ih_lkp_bwt_by_bt = te_mr_ie_bt;
   assign mr_ih_lkp_brt_by_bt = te_mr_ie_bt;
//---------------------------------------
// Instantiate IE_WDATA_CTL
//--------------------------------------
mr_ie_wdata_ctl

#(
    .CORE_DATA_WIDTH       (CORE_DATA_WIDTH      ) 
   ,.CORE_MASK_WIDTH       (CORE_MASK_WIDTH      ) 
   ,.WRCAM_ADDR_WIDTH      (WRCAM_ADDR_WIDTH     ) 
   ,.WRDATA_RAM_ADDR_WIDTH (WRDATA_RAM_ADDR_WIDTH) 
   ,.NO_OF_BWT             (NO_OF_BWT            )
   ,.BT_BITS               (BT_BITS              ) 
   ,.BWT_BITS              (BWT_BITS             ) 
   ,.BRT_BITS              (BRT_BITS             ) 
   ,.ECC_RAM_ADDR_BITS     (ECC_RAM_ADDR_BITS    )
   ,.ECC_ERR_RAM_ADDR_BITS (ECC_ERR_RAM_ADDR_BITS)
   ,.ECC_ERR_RAM_WIDTH     (ECC_ERR_RAM_WIDTH    )
   ,.IE_WR_TYPE_BITS       (IE_WR_TYPE_BITS      ) 
   ,.IE_BURST_NUM_BITS     (IE_BURST_NUM_BITS    ) 

)
mr_ie_wdata_ctl
(  
    .core_ddrc_core_clk   (co_yy_clk)
   ,.core_ddrc_rstn       (core_ddrc_rstn)
   ,.ddrc_cg_en           (ddrc_cg_en)
   ,.reg_ddrc_lpddr4      (dh_mr_lpddr4)
   ,.reg_ddrc_lpddr5      (reg_ddrc_lpddr5)
   ,.reg_ddrc_burst_rdwr  (reg_ddrc_burst_rdwr)
   ,.dh_mr_frequency_ratio(dh_mr_frequency_ratio)
   ,.dh_mr_data_bus_width (dh_mr_data_bus_width)
   ,.wdata_par_err        (wdata_par_err_ie)
   // signals from mr_ram_rd_pipeline
   ,.new_ram_rd_cmd          (mr_ram_rd_cmd          )  // a new command
   ,.ie_mwr_flag             (ie_mwr_flag            ) 
   ,.free_wr_entry_valid     (mr_yy_free_wr_entry_valid)  // a new command is done
   ,.mr_me_raddr             (mr_me_raddr_ie         )  // read address to write data RAM
   ,.mr_me_re                (mr_me_re               )  // read enable to write data RAM
   ,.ram_data_vld            (ram_data_vld           )  // data from write data RAM is valid
   ,.ram_data_vld_early      (ram_data_vld_early     )
   ,.me_mr_rdata             (mr_rdata               )  // write data read from write data RAM
   ,.me_mr_rdatamask         (mr_rdatamask           )  // write data read from write data RAM
   ,.me_mr_rdatapar          (mr_rdatapar            )

   ,.te_mr_ie_bt             (i_te_mr_ie_bt          )
   ,.te_mr_ie_bwt            (i_te_mr_ie_bwt         )
   ,.te_mr_ie_brt            (i_te_mr_ie_brt         )
   ,.te_mr_ie_brt_vld        (i_te_mr_ie_brt_vld     )
   ,.te_mr_ie_wr_type        (i_te_mr_ie_wr_type     )
   ,.te_mr_ie_blk_burst_num  (i_te_mr_ie_blk_burst_num)  //only for the Data command
   ,.te_mr_eccap             (i_te_mr_eccap          )
   ,.ih_mr_ie_brt            (ih_mr_ie_brt           )
   ,.ih_mr_ie_brt_vld        (ih_mr_ie_brt_vld       )
   ,.ih_mr_ie_bwt            (ih_mr_ie_bwt           )
   ,.ih_mr_ie_wr_cnt_dec_vct (ih_mr_ie_wr_cnt_dec_vct)
   ,.ih_mr_ie_wr_cnt_inc     (ih_mr_ie_wr_cnt_inc    )
   ,.ih_mr_ie_blk_wr_end     (ih_mr_ie_blk_wr_end    )
   ,.mr_ih_free_bwt_vld      (mr_ih_free_bwt_vld     )
   ,.mr_ih_free_bwt          (mr_ih_free_bwt         )
   ,.rd_mr_free_brt_vld      (rd_mr_free_brt_vld     )
   ,.rd_mr_free_brt          (rd_mr_free_brt         )
// ECC ACC and ECC RAM interface
   ,.mr_ecc_acc_flush_en     (mr_ecc_acc_flush_en    )
   ,.mr_ecc_acc_flush_addr   (mr_ecc_acc_flush_addr  )
   ,.mr_ecc_acc_wr           (mr_ecc_acc_wr          )
   ,.mr_ecc_acc_waddr        (mr_ecc_acc_waddr       )
   ,.mr_ecc_acc_wdata        (mr_ecc_acc_wdata       )
   ,.mr_ecc_acc_wdata_par    (mr_ecc_acc_wdata_par   )
   ,.mr_ecc_acc_wdata_mask_n (mr_ecc_acc_wdata_mask_n)
   ,.mr_ecc_acc_rd           (mr_ecc_acc_rd          )
   ,.mr_ecc_acc_raddr        (mr_ecc_acc_raddr       )
   ,.ecc_acc_mr_rdata        (ecc_acc_mr_rdata       )
   ,.ecc_acc_mr_rdata_par    (ecc_acc_mr_rdata_par   )
   ,.ecc_acc_mr_rdata_mask_n (ecc_acc_mr_rdata_mask_n)
   ,.mr_ecc_ram_raddr_2      (mr_ecc_ram_raddr_2     )
   ,.ecc_ram_mr_rdata_2      (ecc_ram_mr_rdata_2     )
   ,.ecc_ram_mr_rdata_par_2  (ecc_ram_mr_rdata_par_2 )
   ,.mr_ecc_err_rd           (mr_ecc_err_rd          )
   ,.mr_ecc_err_raddr        (mr_ecc_err_raddr       )
   ,.ecc_err_mr_rdata        (ecc_err_mr_rdata       )
   // wdata of ECC to MR
   ,.wr_ecc_vld              (wr_ecc_vld      )
   ,.ecc_wdata               (ecc_wdata       )
   ,.ecc_wdata_par           (ecc_wdata_par   )
   ,.ecc_wdata_mask_n        (ecc_wdata_mask_n)
);

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON
// ih_mr_lkp_bwt_vld should be 1
property p_bwt_vld;
  @(negedge co_yy_clk) disable iff (~core_ddrc_rstn)
  (gs_mr_write & te_mr_ie_wr_type== `IE_WR_TYPE_WD_E) |-> (ih_mr_lkp_bwt_vld);
endproperty
a_bwt_vld: assert property (p_bwt_vld)
else $error("%m @ %t Error : bwt is not valid during write data", $time);
`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS
endmodule // mr

