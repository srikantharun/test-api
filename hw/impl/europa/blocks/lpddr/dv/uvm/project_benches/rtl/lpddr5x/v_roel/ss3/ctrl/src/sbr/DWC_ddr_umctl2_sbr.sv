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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/sbr/DWC_ddr_umctl2_sbr.sv#8 $
// -------------------------------------------------------------------------
// Description:
//----------------------------------------------------------------------
// Filename    : DWC_ddr_umctl2_sbr.v
// Description : ECC scrubber top level
//               
//----------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module DWC_ddr_umctl2_sbr
import DWC_ddrctl_reg_pkg::*;
  #(
    parameter CHANNEL_NUM                            = 0,
    parameter DDR4_DUAL_CHANNEL                      = 0,
    parameter DATA_CHANNEL_INTERLEAVE                = 0,
    parameter SELFREF_TYPE_WIDTH                     = 1,
    parameter SELFREF_SW_WIDTH                       = 1,
    parameter REG_SCRUB_INTERVALW                    = 13,
    parameter A_DW                                   = 32, // Application data width
    parameter A_STRBW                                = 4, // Application strobe width
    parameter A_PARW                                 = 20,
    parameter M_DW                                   = 32,
    parameter FREQ_RATIO                             = 1,
    parameter AXI_QOSW                               = 4,  // AXI a*qos width
    parameter MEMC_BURST_LENGTH                      = 8,
    parameter MEMC_TAGBITS                           = 16,
    parameter EXA_PYLD_W                             = 32,
    parameter A_NPORTS_LG2                           = 1,
    parameter A_PORT_NUM                             = 0,  // static instantiation port number
    parameter IDW                                    = 8,
    parameter MEMC_NO_OF_ENTRY                       = 64,
    parameter MEMC_WDATA_PTR_BITS                    = 8,
    parameter CMD_LEN_BITS                           = 1,
    parameter MEMC_INLINE_ECC                        = 0,
    parameter OCPAR_EN                               = 0,
    parameter OCCAP_EN                               = 0,
    parameter OCCAP_PIPELINE_EN                      = 0,    
    parameter ECC_RM_WIDTH                           = 7,
    parameter ECC_RMG_WIDTH                          = 2,
    parameter ECC_H3_WIDTH                           = 6,
    parameter NBEATS                                 = 4,
    parameter BRDWR                                  = 4,
    parameter HIF_ADDR_WIDTH                         = `MEMC_HIF_ADDR_WIDTH,
    parameter RMW_FIFO_DEPTH                         = 4,
    parameter N_PORTS                                = 1,
    parameter DBW                                    = 2,
    parameter NRANKS                                 = 2,
    parameter AMCSW                                  = 6)
    (
     input                                      clk,
     input                                      rst_n,

     // HIF Read Address channel
     output [AXI_QOSW-1:0]                      sbr_arqos, // SBR read address qos
     output [HIF_ADDR_WIDTH-1:0]                sbr_araddr, // SBR read address 
     output                                     sbr_arvalid, // SBR read address valid
     input                                      hif_arready, // HIF read address ready
     // HIF Write Address channel
     output [AXI_QOSW-1:0]                      sbr_awqos, // SBR write address qos
     output                                     sbr_awrmw,
     output [HIF_ADDR_WIDTH-1:0]                sbr_awaddr, // SBR write address 
     output                                     sbr_awvalid, // SBR write address valid
     output                                     sbr_arpagematch, // SBR read page match
     output                                     sbr_awpagematch, // SBR write page match
     output [CMD_LEN_BITS-1:0]                  sbr_rxcmd_wlength,
     input                                      hif_awready, // HIF write address ready
     output [EXA_PYLD_W-1:0]                    sbr_rexa_pyld, // Exclusive Read Payload - set to all zeros
     output [MEMC_TAGBITS-1:0]                  sbr_rxcmd_token,          
     output [CMD_LEN_BITS-1:0]                  sbr_rxcmd_rlength,
     
     // HIF Read Data Channel
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Intentionally left unconnected.
     input                                      hif_rerror, // HIF read data error - NOT USED
     input [A_DW-1:0]                           hif_hif_rdata, // HIF read data - NOT USED
//spyglass enable_block W240
     input                                      hif_rlast_pkt, // HIF read paket data last
     input [N_PORTS-1:0]                        hif_rvalid, // HIF read data valid
     input [MEMC_TAGBITS-1:0]                   hif_resp_token,
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block
     input                                      hif_corr_ecc_err,
//spyglass enable_block W240
     // HIF Write Data Channel
     output [A_DW-1:0]                          sbr_wdata, // XPI write data
     output [A_STRBW-1:0]                       sbr_wstrb, // XPI write data strobe
     output                                     sbr_wlast, // XPI write data last
     output                                     sbr_wvalid, // XPI write data valid
     input                                      hif_wready, // HIF write data ready
     output [A_PARW-1:0]                        sbr_wdatapar,
     output [MEMC_WDATA_PTR_BITS-1:0]           sbr_wdata_ptr,
     output                                     sbr_wlast_pkt, // XPI write last beat of the packet
     output [NBEATS-1:0]                        sbr_wdata_mask_full,

     // Address range from PM block
     input [HIF_ADDR_WIDTH-1:0]                 sbr_address_range,
     input [HIF_ADDR_WIDTH-1:0]                 lpddr34_6gb_12gb_mask,
     input [`MEMC_HIF_ADDR_WIDTH_MAX-1:0]       sbr_address_range_mask,
     input [`MEMC_HIF_ADDR_WIDTH_MAX-1:0]       sbr_address_start_mask,
     input [HIF_ADDR_WIDTH-1:0]                 data_channel_addrmap_mask,
     
     // Low power
     output                                     cactive_out, // Internal busy status, to drive DDRC cactive_in 

     // HWFFC signal
     input                                      dis_sbr_req,
     output                                     dis_sbr_ack, 

     //Parity Output
     output                                     occap_sbr_par_err,
     // Registers
     input [BRDWR-1:0]                          reg_ddrc_burst_rdwr,
     input [DBW-1:0]                            reg_ddrc_data_bus_width,
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block
     input                                      reg_ddrc_oc_parity_type,
//spyglass enable_block W240
     input                                      reg_ddrc_occap_en,
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: This signals is not used in DDRCTL but required by uMCTL2
     input                                      reg_arb_bl_exp_mode,
//spyglass enable_block W240
     input                                      reg_arb_scrub_en,
     input [REG_SCRUB_INTERVALW-1:0]            reg_arb_scrub_interval,
    input [SCRUB_BURST_LENGTH_LP_WIDTH-1:0]     reg_arb_scrub_burst_length_lp_port0,
    input [SCRUB_BURST_LENGTH_NM_WIDTH-1:0]     reg_arb_scrub_burst_length_nm_port0,
     input                                      reg_arb_scrub_during_lowpower,
     input [31:0]                               reg_arb_scrub_pattern0,

     input [SCRUB_CMD_TYPE_WIDTH-1:0]           reg_arb_scrub_cmd_type_port0,
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block
     input [SBR_CORRECTION_MODE_WIDTH-1:0]      reg_arb_scrub_correction_mode_port0,
//spyglass enable_block W240
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block
     input                                      reg_ddrc_ecc_type,
     input [2:0]                                reg_ddrc_ecc_mode,
     input [ECC_RM_WIDTH-1:0]                   reg_ddrc_ecc_region_map,
     input                                      reg_ddrc_ecc_region_map_other,
//spyglass enable_block W240
     input [SELFREF_SW_WIDTH-1:0]               reg_ddrc_selfref_sw,               //0-SW exit from SR, 1-SW entry to SR
     input [ECC_RMG_WIDTH-1:0]                  reg_ddrc_ecc_region_map_granu,

     output                                     arb_reg_scrub_done,
     output                                     arb_reg_scrub_busy,
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block
     input [HIF_ADDR_WIDTH-1:0]                 l3_iecc_col_mask,         
//spyglass enable_block W240

     input [ECC_H3_WIDTH-1:0]                   h3_iecc_col_mask,
     // In order to detect low power operation
     input  [2:0]                               ddrc_reg_operating_mode,  //000-init, 001-normal, 010-PD, 011-SR, 1XX-DPD/MPSM
     input [SELFREF_TYPE_WIDTH-1:0]             ddrc_reg_selfref_type,    //00-SDRAM is not in SR, 11-SDRAM is in SR (automatic only), 10-SDRAM is in SR (SW or HW LP if)
     // Interrupt


     input                                                 reg_ddrc_ddr5,

`ifndef SYNTHESIS
    //sbr_periodic_rmw output port indicates if the current RMW transaction is a correction RMW vs a periodic RMW.
    //It is used by the Testbench to differentiate between the two.
    //This signal is only added as an output port for simulations. During synthesis, port gets optimized out.
    output                                                   sbr_periodic_rmw,
`endif //SYNTHESIS
    output                                                   sbr_done_intr

     );


   localparam SCRUBI_GRANULARITY = (MEMC_INLINE_ECC == 1) ? 9 : 8;

   localparam DDRCTL_LUT_ADDRMAP_EN = 0;
   wire reg_addrmap_lut_bypass;

   localparam SCRUBI_CNTW = REG_SCRUB_INTERVALW + SCRUBI_GRANULARITY;

   localparam SAQW = HIF_ADDR_WIDTH;
   localparam SAQD = 8;
   localparam SAQD_LG2 = `UMCTL_LOG2(SAQD);
   localparam OUTS_RDW = 10;
   localparam OUTS_WRW = 10;  

   localparam SKPCNTW = 10;
   localparam SKPCNTWP1 = SKPCNTW+1;
   localparam BRSTCNTW = 11;

   localparam TOKEN_WIDTH          = (MEMC_NO_OF_ENTRY==64) ? 7 : 6; 

   localparam ADDR_BUFF_DEPTH      = 1<<TOKEN_WIDTH;

   localparam [HIF_ADDR_WIDTH-1:0] LPDDR3_ROW_SHIFT_BASE = 1 << (`UMCTL2_AM_ROW_BASE + 13);

    // Scrubber FSM
   localparam ST_SBR_SIZE = 3;
   
   localparam [ST_SBR_SIZE-1:0] ST_SBR_DIS = 3'b001;   // Disabled
   localparam [ST_SBR_SIZE-1:0] ST_SBR_NM  = 3'b010;   // Normal operating mode
   localparam [ST_SBR_SIZE-1:0] ST_SBR_LP  = 3'b100;   // HW Controlled LP mode

   // State bitfields
   localparam [ST_SBR_SIZE-1:0] STBF_SBR_DIS = 0;
   localparam [ST_SBR_SIZE-1:0] STBF_SBR_NM  = 1;
   localparam [ST_SBR_SIZE-1:0] STBF_SBR_LP  = 2;

   // ocpar related
   localparam OCPAR_SL_DW = A_DW/A_STRBW;

   // inline ECC
      //
   localparam BL_MASKW           = 7;
   localparam REG_ID_WIDTH       = 3;

      // corr FSM
   localparam CORR_ST_WIDTH  = 3;
   localparam [CORR_ST_WIDTH-1:0] CORR_NO_ERR    = 3'b000;
   localparam [CORR_ST_WIDTH-1:0] CORR_ERR_DET   = 3'b001;
   localparam [CORR_ST_WIDTH-1:0] CORR_WAIT_RD   = 3'b011;
   localparam [CORR_ST_WIDTH-1:0] CORR_WRITE     = 3'b010;
   localparam [CORR_ST_WIDTH-1:0] CORR_WAIT_WR   = 3'b110;

      // cmd_length generation
   localparam FULL_BURST      = 0;
   localparam HALF_BURST      = (MEMC_BURST_LENGTH==16) ? 2 : 1;
   localparam QUARTER_BURST   = 3;

   localparam BL2 = 1;
   localparam BL4 = 2;
   localparam BL8 = 4;
   localparam BL16 = 8;

   localparam FBW = 0;
   localparam HBW = 1;
   localparam QBW = 2;

   localparam M_STRBW = M_DW/8;
   localparam M_STRBW_HBW = (M_DW>8)  ? M_STRBW/2 : M_STRBW;
   localparam M_STRBW_QBW = (M_DW>16) ? M_STRBW/4 : M_STRBW_HBW;

   localparam SBR_VEC_WIDTH      = 1+1+1+1+OUTS_RDW*2+BRDWR*2+HIF_ADDR_WIDTH+SCRUBI_CNTW+BRSTCNTW+SKPCNTW+1+1+ST_SBR_SIZE+HIF_ADDR_WIDTH;
   localparam SBR_VEC_RESVAL     = {{(SBR_VEC_WIDTH-HIF_ADDR_WIDTH-ST_SBR_SIZE){1'b0}},ST_SBR_DIS,LPDDR3_ROW_SHIFT_BASE};

   localparam SBR_IE_VEC_WIDTH   = CORR_ST_WIDTH+TOKEN_WIDTH+1;
   localparam SBR_IE_VEC_RESVAL  = {CORR_NO_ERR,{(TOKEN_WIDTH+1){1'b1}}};

   localparam SBR_SBE_VEC_WIDTH  = 1+HIF_ADDR_WIDTH+ SCRUB_DROP_CNT_WIDTH;
   localparam SBR_SBE_VEC_RESVAL = {(SBR_SBE_VEC_WIDTH){1'b0}};
   
   localparam RMW_FIFOW          = HIF_ADDR_WIDTH; 
   localparam RMW_FIFOD          = RMW_FIFO_DEPTH; 
   localparam RMWD_LG2           = `UMCTL_LOG2(RMW_FIFOD);
   localparam RESP_TOKEN_WIDTH   = (MEMC_TAGBITS-(TOKEN_WIDTH+IDW+A_NPORTS_LG2+3));
   localparam NRANKS_LG2 = `UMCTL_LOG2(NRANKS);


     localparam RSRVD_WDATA_PTR_BITS = (MEMC_WDATA_PTR_BITS-(A_NPORTS_LG2+3)) ;

   genvar gv;

   wire [TOKEN_WIDTH-1:0] atoken;
   wire [HIF_ADDR_WIDTH-1:0] sbr_address_range_int;
   wire [HIF_ADDR_WIDTH-1:0] sbr_address_start_int;

   wire [SBR_VEC_WIDTH-1:0] sbr_vec_i, sbr_vec_r;

   wire sbr_vec_parity_err, sbr_ie_vec_parity_err;
   
   // If the range limiter input is driven (for debug purposes) from the interface, use it instead of the internal automated one.
   assign sbr_address_range_int = (|sbr_address_range_mask[HIF_ADDR_WIDTH-1:0]) ? sbr_address_range_mask[HIF_ADDR_WIDTH-1:0] :
                                                                                  sbr_address_range;

   // if start mask not set, use 0 by default
   assign sbr_address_start_int = (|sbr_address_start_mask[HIF_ADDR_WIDTH-1:0]) ? sbr_address_start_mask[HIF_ADDR_WIDTH-1:0] :
                                                                                  {HIF_ADDR_WIDTH{1'b0}};
   
   wire [SCRUBI_CNTW - 1:0] tscrubi_cnt;
   reg [SCRUBI_CNTW - 1:0] tscrubi_cnt_nxt;
   wire                    tscrubi_cntzero;
   wire                    dis_tscrubi_cnt;

   wire                    saq_wr,saq_rd,saq_full,saq_empty,saq_wr_masked;      // SAQ handshake
   wire [SAQW-1:0]         saq_d, saq_q;
   wire [SAQD_LG2:0]       saq_wcount_unused;
   wire                    send_scrub;
   wire                    send_scrub_en;
   
   wire                    active_reads;
   wire [OUTS_RDW-1:0]     outstanding_reads, outstanding_reads_nxt;
   wire                    active_writes;
   wire [OUTS_WRW-1:0]     outstanding_writes, outstanding_writes_nxt;
  
   wire [BRSTCNTW-1:0]     scrub_burst_decoded;
   wire [BRSTCNTW-1:0]     scrub_burst_cnt;
   reg [BRSTCNTW-1:0]      scrub_burst_cnt_nxt;
   wire                    scrub_burst_cntzero;
   wire                    scrub_burst_single;

   wire [SKPCNTW-1:0]      scrub_skip_cnt;
   reg [SKPCNTW-1:0]       scrub_skip_cnt_nxt;
   wire                    scrub_skip_cntzero;
   wire [SKPCNTWP1-1:0]    scrub_skip_cnt_load;
   
   reg                     burst_started_nxt, burst_first_nxt;
   wire                    burst_started, burst_first;
   wire                    sbr_accepted;
 
   
   wire [HIF_ADDR_WIDTH-1:0] addr_cnt;
   wire [HIF_ADDR_WIDTH-1:0] addr_cnt_next;
   reg  [HIF_ADDR_WIDTH:0]   addr_cnt_next_wider;
   wire [BRDWR+1-1:0]       addr_cnt_incr;
   wire [BRDWR+1-1:0]       addr_cnt_incr_m1;
   wire [HIF_ADDR_WIDTH-1:0] address_range_mask, address_start_mask, max_addr_cnt, max_addr_cnt_tmp, start_addr, start_addr_tmp;
   wire [HIF_ADDR_WIDTH-1:0] addr_row_shift_nxt;
   wire [HIF_ADDR_WIDTH-1:0] addr_row_shift;
   wire [HIF_ADDR_WIDTH-1:0] addr_dch_incr;

   wire                    addr_cnt_in_range;
   
   wire                    ctl_in_normal_mode, ctl_in_hw_controlled_lp_mode, ctl_in_sw_controlled_lp_mode;
   wire [2:0]              ddrc_reg_operating_mode_int;

   wire [BRDWR-1:0]        burst_rdwr_bus_width;
   wire [BRDWR-1:0]        reg_ddrc_burst_rdwr_mod;
   wire [BRDWR-1:0]        reg_ddrc_burst_rdwr_mod_m1, reg_ddrc_burst_rdwr_mod_m1_nxt;
   wire [BRDWR-1:0]        reg_ddrc_burst_rdwr_mod_bl;

   wire [BRDWR-1:0]        beat_cnt, beat_cnt_nxt;
  
   wire [M_DW-1:0]         m_wdata; // DDR write data

   wire                    scrubber_dis, scrubber_in_lp, scrubber_in_nm, addr_in_range, lpddr3_row13_14, lpddr3_6gb_12gb_en;
   wire                    addr_cnt_valid;
   wire                    saq_d_in_range, saq_q_in_range;

   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Code only used in certain configurations.  
   wire                    rcmd_vld_ie, rcmd_end_ie;
   //spyglass enable_block W528

   wire                    wcmd_vld_ie, wcmd_end_ie;

   wire                    iecc_burst_en;

   wire                    tq_par_err, saq_par_err, address_ram_par_err;

   wire                    iecc_cmd_valid;
   reg [HIF_ADDR_WIDTH-1:0] iecc_region_incr; 
   wire [HIF_ADDR_WIDTH-1:0]iecc_region_mask;

   wire                    dis_sbr_keep_addr;

   wire                    outstanding_reads_incr, outstanding_reads_decr;
   wire                    outstanding_writes_incr, outstanding_writes_decr;

   wire [A_NPORTS_LG2-1:0] port_num;
   wire [IDW-1:0]          arid;
   wire                    arlast;
   wire                    dis_sbr_ack_nxt;
   wire [ST_SBR_SIZE-1:0]  st_sbr;
   reg [ST_SBR_SIZE-1:0]   st_sbr_nxt;

   reg                     arb_reg_scrub_done_nxt;
   wire                    arb_reg_scrub_busy_nxt;
   wire [NBEATS-1:0]       sbr_wdata_mask_full_full, sbr_wdata_mask_full_half, sbr_wdata_mask_full_quarter;

   wire                    write_mode_done;
   reg                     write_mode_done_nxt;

//Adding register stage to hif_r* signals. 
//hif_rdata_addr requires hif_rvalid_int. 
//hif_rvalid_int drives all other signal
     logic                                      hif_rlast_pkt_int; // HIF read paket data last
     logic [N_PORTS-1:0]                        hif_rvalid_int; // HIF read data valid
     logic [MEMC_TAGBITS-1:0]                   hif_resp_token_int;
     logic                                      hif_corr_ecc_err_int;

  

   // response token
   wire [TOKEN_WIDTH-1:0] rtoken;
   wire [A_NPORTS_LG2-1:0] pnum; 
   wire [IDW-1:0] rrid;
   wire rlast;
   wire iecc_rvld, iecc_rend;
   // token manager signals
   wire tm_empty;
   wire tm_empty_red_unused;
   wire occap_tm_par_err;
   wire gen_token;
   wire release_token;

   wire                    iecc_hole;
   logic [2:0]             reg_arb_scrub_burst;
   assign reg_arb_scrub_burst = ((st_sbr_nxt == ST_SBR_DIS) || (st_sbr_nxt == ST_SBR_NM)) ? reg_arb_scrub_burst_length_nm_port0 : reg_arb_scrub_burst_length_lp_port0; 

   wire [RESP_TOKEN_WIDTH-1:0]         resp_token_msb;
   wire                                sbr_rmw_parity_err;
   wire                                rmw_par_err;
   wire                                sbr_addr_log_par_err;

   logic scrub_en_int;
   logic sbr_stop_req_latched,sbr_stop_req_latched_d1;
   assign scrub_en_int = reg_arb_scrub_en;
   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Used in generate block (unused in inline ECC)
   assign sbr_stop_req_latched = 1'b0;
   //spyglass enable_block W528

   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Used in generate block
   wire ctl_fbw   = (reg_ddrc_data_bus_width==FBW) ? 1'b1 : 1'b0;
   wire ctl_hbw   = (reg_ddrc_data_bus_width==HBW) ? 1'b1 : 1'b0;
   wire ctl_qbw   = (reg_ddrc_data_bus_width==QBW) ? 1'b1 : 1'b0;
   wire ddrc_bl16 = (reg_ddrc_burst_rdwr==BL16) ? 1'b1 : 1'b0;
   wire ctl_bl2   = (burst_rdwr_bus_width==BL2) ? 1'b1 : 1'b0;
   wire ctl_bl4   = (burst_rdwr_bus_width==BL4) ? 1'b1 : 1'b0;
   wire ctl_bl8   = (burst_rdwr_bus_width==BL8) ? 1'b1 : 1'b0;
   wire ctl_bl16  = (burst_rdwr_bus_width==BL16) ? 1'b1 : 1'b0;
   //spyglass enable_block W528

   reg  skip_current_rank,skip_current_rank_l;
   logic current_rank_invalid;
   wire [HIF_ADDR_WIDTH:0]   next_rank_valid_addr;
   wire [HIF_ADDR_WIDTH-1:0] mask_lower_addr;
   wire [HIF_ADDR_WIDTH-1:0] masked_addr_incr;
   wire scrub_restore_latched_nxt;
   wire scrub_restore_latched_r;

   // occap error assign
   assign occap_sbr_par_err = tq_par_err | saq_par_err | address_ram_par_err | sbr_vec_parity_err | sbr_ie_vec_parity_err | occap_tm_par_err | sbr_rmw_parity_err | rmw_par_err | sbr_addr_log_par_err;

   // parity vector assign
   assign sbr_vec_i = {arb_reg_scrub_done_nxt,arb_reg_scrub_busy_nxt,write_mode_done_nxt,dis_sbr_ack_nxt,outstanding_reads_nxt,outstanding_writes_nxt,reg_ddrc_burst_rdwr_mod_m1_nxt,beat_cnt_nxt,addr_cnt_next,tscrubi_cnt_nxt,scrub_burst_cnt_nxt,scrub_skip_cnt_nxt,burst_started_nxt,burst_first_nxt // insert new signals at the MSB and update SBR_VEC_WIDTH and SBR_VEC_RESVAL accordingly
                        /*DON'T TOUCH START*/,st_sbr_nxt,addr_row_shift_nxt};/*DONT'T TOUCH END*/
   assign {arb_reg_scrub_done,arb_reg_scrub_busy,write_mode_done,dis_sbr_ack,outstanding_reads,outstanding_writes,reg_ddrc_burst_rdwr_mod_m1,beat_cnt,addr_cnt,tscrubi_cnt,scrub_burst_cnt,scrub_skip_cnt,burst_started,burst_first // insert new signals at MSB, see above
                        /*DON'T TOUCH START*/,st_sbr,addr_row_shift}/*DONT'T TOUCH END*/ = sbr_vec_r; // keep st_sbr and addr_row_shift at the LSB

   localparam MIN_M_STRBW_4 = (M_STRBW<4) ? M_STRBW : 4;
   localparam MIN_M_STRBW_8 = (M_STRBW<8) ? M_STRBW : 8;
   
   assign ddrc_reg_operating_mode_int = ddrc_reg_operating_mode;

   wire ctl_nm = (ddrc_reg_operating_mode_int==3'b001) ? 1'b1 : 1'b0;
   wire ctl_pd = (ddrc_reg_operating_mode_int==3'b010) ? 1'b1 : 1'b0;
   wire ctl_sr = (ddrc_reg_operating_mode_int==3'b011) ? 1'b1 : 1'b0;
   wire ctl_lp = ddrc_reg_operating_mode_int[2];
   wire ddr5_all_ranks_in_scrub_dis_or_unpopulated;
   wire ctl_in_hw_controlled_lp_mode_ddr5;
   wire ctl_in_sw_controlled_lp_mode_ddr5;
   wire ctl_in_normal_mode_ddr5;
  assign ddr5_all_ranks_in_scrub_dis_or_unpopulated = 1'b0;
  assign ctl_in_hw_controlled_lp_mode_ddr5 = 1'b0;
  assign ctl_in_sw_controlled_lp_mode_ddr5 = 1'b0;
  assign ctl_in_normal_mode_ddr5 = 1'b0;
   wire sr_auto = (ddrc_reg_selfref_type == {{($bits(ddrc_reg_selfref_type)-2){1'b0}},2'b11}) ? 1'b1 : 1'b0;
   wire sr_all  = (ddrc_reg_selfref_type == {{($bits(ddrc_reg_selfref_type)-2){1'b0}},2'b10}) ? 1'b1 : 1'b0;
   assign ctl_in_hw_controlled_lp_mode = ctl_pd | (ctl_sr & sr_auto) | (ctl_sr & sr_all & ~reg_ddrc_selfref_sw);
   assign ctl_in_sw_controlled_lp_mode = (ctl_sr & sr_all & reg_ddrc_selfref_sw) | ctl_lp;
   
   assign ctl_in_normal_mode           = ctl_nm;

   assign saq_d_in_range   = (saq_d<max_addr_cnt) ? 1'b1 : 1'b0;
   assign saq_q_in_range   = (saq_q<max_addr_cnt) ? 1'b1 : 1'b0;

   // inline ECC address buffer
   wire corr_write_mode, send_corr_burst, read_corr_burst;
   wire [HIF_ADDR_WIDTH-1:0] corr_addr;
 
   //Sideband ECC
   wire [HIF_ADDR_WIDTH-1:0]           rcvd_rmw_addr;
   wire                                same_addr;
   wire [SBR_SBE_VEC_WIDTH-1:0]        sbr_rmw_vec_i;
   wire [SBR_SBE_VEC_WIDTH-1:0]        sbr_rmw_vec_r;
 
   reg  [HIF_ADDR_WIDTH-1:0]           rcvd_rmw_addr_r;
   wire [HIF_ADDR_WIDTH-1:0]           rcvd_rmw_addr_int;
   wire                                valid_rmw; 

   // decode response token
   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Used in generate block or unused, but kept to decode hif_resp_token_int
generate if (MEMC_INLINE_ECC==1) begin : IECC_RESP_TOKEN
   assign {rtoken,resp_token_msb,iecc_rvld,iecc_rend,rlast,rrid,pnum}               = hif_resp_token_int;
end else begin
   //spyglass disable_block W164b 
   //SMD:LHS: '{rtoken ,resp_token_msb ,iecc_rvld ,iecc_rend ,rlast ,rrid ,pnum}' width is greater than RHS: 'hif_resp_token_int' width in assignment  
   //SJ: RHS width is based on the CHB Tag Bits. This field can be removed as it is not used in this scenario. 
   assign {rtoken,resp_token_msb,iecc_rvld,iecc_rend,rlast,rrid,pnum}               = hif_resp_token_int;
   //spyglass enable_block W164b

   assign rcvd_rmw_addr     = {HIF_ADDR_WIDTH{1'b0}};
   assign rcvd_rmw_addr_int = (valid_rmw) ? rcvd_rmw_addr : rcvd_rmw_addr_r;
end
endgenerate
   //spyglass enable_block W528


   logic                               scrub_dis_to_enab;
   logic                               reg_arb_scrub_en_r;
   wire [SCRUB_DROP_CNT_WIDTH-1:0]     drop_scrub_cnt_nxt;
   reg  [SCRUB_DROP_CNT_WIDTH-1:0]     drop_scrub_cnt;
   wire                                generate_rmw;
   wire                                rmw_wr;
   wire                                rmw_rd;
   wire [RMW_FIFOW-1:0]                rmw_d;         
   wire [RMW_FIFOW-1:0]                rmw_q;         
   wire [RMWD_LG2+1-1:0]               rmw_fifo_wcount_unsed;
   wire                                rmw_fifo_full;
   wire                                rmw_fifo_empty;
   wire                                tq_empty;
  reg                                  write_data_valid;

generate if (MEMC_INLINE_ECC==0) begin : SBECC_PAR

   assign sbr_rmw_vec_i = {scrub_en_int,drop_scrub_cnt_nxt,rcvd_rmw_addr_int};
   assign {reg_arb_scrub_en_r,drop_scrub_cnt,rcvd_rmw_addr_r} = sbr_rmw_vec_r;
   assign arb_reg_scrub_drop_cnt = drop_scrub_cnt; 
// parity register
   DWC_ddr_umctl2_par_reg
   

   #(
      .DW                   (SBR_SBE_VEC_WIDTH),
      .OCCAP                (OCCAP_EN),
      .OCCAP_PIPELINE_EN    (OCCAP_PIPELINE_EN),
      .REG_EN               (0),
      .SL_W                 (8),
      .RESVAL               (SBR_SBE_VEC_RESVAL))
   U_sbr_rcvd_rmw_addr
   (  .clk        (clk),
      .rst_n      (rst_n),
      .data_in    (sbr_rmw_vec_i),
      .reg_set    (1'b0),
      .parity_en  (reg_ddrc_occap_en),
      .poison_en  (1'b0),
      .data_out   (sbr_rmw_vec_r),
      .parity_err (sbr_rmw_parity_err));

  //same_addr - is required to avoid multiple writes to the RMW FIFO.
  //valid_rmw - must be asserted, to compare current & previous. 
  //generate_rmw - based on the register prog. determine if RMW can be done or
  //not.
 
  
  assign valid_rmw           = ((hif_corr_ecc_err_int ) & generate_rmw);
  assign same_addr           =  valid_rmw  ? ((~(|({rcvd_rmw_addr_r}^{rcvd_rmw_addr_int}))) & ~rmw_fifo_empty) : 1'b0;

end
else begin
  assign sbr_rmw_parity_err     = 1'b0;
  assign rmw_par_err            = 1'b0;
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate block 
  assign rcvd_rmw_addr          = {HIF_ADDR_WIDTH{1'b0}};
  assign same_addr              = 1'b0;
  assign sbr_rmw_vec_i          = {SBR_SBE_VEC_WIDTH{1'b0}};
  assign sbr_rmw_vec_r          = {SBR_SBE_VEC_WIDTH{1'b0}};
//spyglass enable_block W528
end
endgenerate

   // DDR4 Dual Channel 
   wire sbr_wrong_channel;
   assign  addr_dch_incr = data_channel_addrmap_mask;
generate
  if (DATA_CHANNEL_INTERLEAVE==1) begin: data_ch_intrlv
    if(CHANNEL_NUM==0) begin : SBR_WORNG_CHANNEL_0
      assign sbr_wrong_channel = |(addr_cnt & data_channel_addrmap_mask); 
    end
    else begin : SBR_WORNG_CHANNEL_1
      assign sbr_wrong_channel = ~|(addr_cnt & data_channel_addrmap_mask); 
    end
  end else begin: n_data_ch_intrlv
    assign sbr_wrong_channel = 1'b0;
  end
endgenerate 

         reg  [BRSTCNTW-1:0]       ie_scrub_burst_decoded;
         reg                       ie_scrub_burst_single;
         wire                      ie_addr_cnt_valid;
         
         wire                      ie_corr_write_mode;
         wire                      ie_read_corr_burst;
         wire                      nonie_read_corr_burst;
         wire                      ie_send_corr_burst;
         wire [HIF_ADDR_WIDTH-1:0] ie_corr_addr;
         wire                      ie_tq_par_err;
         wire                      ie_address_ram_par_err;
         wire                      ie_iecc_cmd_valid;
         wire                      ie_sbr_ie_vec_parity_err;
         wire                      ie_iecc_hole;
         wire [NBEATS-1:0]         ie_sbr_wdata_mask_full_full;
         wire [NBEATS-1:0]         ie_sbr_wdata_mask_full_half;
         wire [NBEATS-1:0]         ie_sbr_wdata_mask_full_quarter;
         wire [HIF_ADDR_WIDTH-1:0] ie_address_range_mask;
         wire [HIF_ADDR_WIDTH-1:0] ie_address_start_mask;
         wire                      ie_rcmd_vld_ie;
         wire                      ie_rcmd_end_ie;
         wire                      ie_wcmd_vld_ie;
         wire                      ie_wcmd_end_ie;
         wire                      ie_iecc_burst_en;
         wire [CMD_LEN_BITS-1:0]   ie_sbr_rxcmd_wlength;

   generate
      if (MEMC_INLINE_ECC==1) begin: IECC_EN
         wire [HIF_ADDR_WIDTH-1:0] addr_in, addr_out;
         wire addr_wr;
         wire [TOKEN_WIDTH-1:0] rtoken_err;
         wire corr_logic_en;
         reg corr_write_mode_r, send_corr_burst_r, read_corr_burst_r;
         wire [REG_ID_WIDTH-1:0] iecc_region_id;
         wire iecc_en;
         wire ext_hbits_vld;
         wire tq_wr, tq_full, tq_rd;
         wire [TOKEN_WIDTH-1:0] tq_d, tq_q;
         wire [TOKEN_WIDTH:0] tq_wcount_unused;

         wire [TOKEN_WIDTH:0] token_last;
         wire [TOKEN_WIDTH:0] token_last_nxt;
         wire [TOKEN_WIDTH:0] token_in;
         wire same_token;

         wire [CORR_ST_WIDTH-1:0] corr_state_reg;
         reg [CORR_ST_WIDTH-1:0] corr_state_next;

         wire [SBR_IE_VEC_WIDTH-1:0] sbr_ie_vec_i, sbr_ie_vec_r;

         assign sbr_ie_vec_i = {corr_state_next,token_last_nxt}; // insert new signals at MSB and update  SBR_IE_VEC_WIDTH and SBR_IE_VEC_RESVAL accordingly
         assign {corr_state_reg,token_last} = sbr_ie_vec_r;

         assign iecc_en   = |reg_ddrc_ecc_mode & reg_ddrc_ecc_type;
         //In inline ECC case, there is no RMW FIFO
         assign rmw_fifo_empty = 1'b1;
         //not updated for periodic RMW.
         //This logic is inline ECC specific. It is not updated for Periodic RMW. there is no requirement currently.
         assign corr_logic_en = (reg_arb_scrub_cmd_type_port0==2'b00) & ~dis_tscrubi_cnt & iecc_en; // disable logic when in write mode or scrub_interval=0

         assign ie_iecc_burst_en   = corr_logic_en;

         assign addr_wr = gen_token;
         assign addr_in = sbr_araddr;

         // Store output addresses in a memory. Address can be retrieved via the returned token
         DWC_ddrctl_bcm_wrap_mem_array
         
         #( .DATA_WIDTH         (HIF_ADDR_WIDTH),
            .DEPTH              (ADDR_BUFF_DEPTH),
            .MEM_MODE           (0), // no pre or post retiming
            .ADDR_WIDTH         (TOKEN_WIDTH),
            .OCCAP_EN           (OCCAP_EN),
            .OCCAP_PIPELINE_EN  (OCCAP_PIPELINE_EN)          
          )
         U_address_ram
         (
            // Outputs
            .data_out                            (addr_out),
            .par_err                             (ie_address_ram_par_err),
            // Inputs
            .clk                                 (clk),
            .rst_n                               (rst_n),
            .init_n                              (1'b1),            
            .wr_n                                (~addr_wr),
            .data_in                             (addr_in),
            .wr_addr                             (atoken),
            .rd_addr                             (rtoken_err),
            .par_en                              (reg_ddrc_occap_en)
         );

         assign tq_wr      = hif_corr_ecc_err_int & hif_rvalid_int[N_PORTS-1] & corr_logic_en & ~same_token;
         assign tq_d       = rtoken;
         assign rtoken_err = tq_q;

         assign ie_corr_addr = addr_out;

         // FIFO stores token for commans which returned correctable error
         DWC_ddr_umctl2_gfifo
         
         #(
            .WIDTH           (TOKEN_WIDTH),
            .DEPTH           (ADDR_BUFF_DEPTH),
            .ADDR_WIDTH      (TOKEN_WIDTH),
            //spyglass disable_block SelfDeterminedExpr-ML
            //SMD: Self determined expression '(TOKEN_WIDTH + 1)' found in module 'DWC_ddr_umctl2_sbr'
            //SJ: This coding style is acceptable and there is no plan to change it.
            .COUNT_WIDTH     (TOKEN_WIDTH+1),
            //spyglass enable_block SelfDeterminedExpr-ML
            .OCCAP_EN        (OCCAP_EN),
            .OCCAP_PIPELINE_EN (OCCAP_PIPELINE_EN)
         ) 
         U_tq
         (
            .clk             (clk),
            .rst_n           (rst_n),
            .wr              (tq_wr),
            .d               (tq_d),
            .rd              (tq_rd),  
            .par_en          (reg_ddrc_occap_en),
            .init_n          (1'b1),
            //spyglass disable_block W528
            //SMD: A signal or variable is set but never read
            //SJ: Used in RTL assertion
            .ff              (tq_full),
            //spyglass enable_block W528
            .wcount          (tq_wcount_unused), 
            .q               (tq_q),
            .fe              (tq_empty),
            .par_err         (ie_tq_par_err)
            `ifdef SNPS_ASSERT_ON
            `ifndef SYNTHESIS
            ,.disable_sva_fifo_checker_rd (1'b0)
            ,.disable_sva_fifo_checker_wr (1'b0)
            `endif // SYNTHESIS
            `endif // SNPS_ASSERT_ON
         );

         assign token_in = {1'b0,tq_d};
         assign same_token = (~|(token_in^token_last)) & (~tq_empty); // prevent the FIFO to be filled in case the same burst returns an error for multiple cycles

         assign token_last_nxt = (tq_wr) ? token_in : token_last;

 `ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
   
   
   // Check that TQ FIFO does not overflow
   property p_tq_fifo_overflow;
      @(posedge clk) disable iff(!rst_n) 
      (tq_wr) |-> (!tq_full);
   endproperty  

  //SNPS_XVP_DESC: Check if the Return token FIFO has an overflow
  a_tq_fifo_overflow : assert property (p_tq_fifo_overflow) else 
    $display("-> %0t ERROR: SBR Return Token FIFO overflow !!!", $realtime);

      `endif
   `endif

         // FSM detects correctable error token pushed in the queue (tq)
         always @(*) begin: corr_FSM_COMB
            corr_state_next      = corr_state_reg;
            corr_write_mode_r    = 1'b0;
            send_corr_burst_r    = 1'b0;
            read_corr_burst_r    = 1'b0;
            case (corr_state_reg)
               CORR_NO_ERR: begin // detect an error
                     if (~tq_empty & corr_logic_en) corr_state_next = CORR_ERR_DET;
                  end
               CORR_ERR_DET: begin // wait the end of the burst
                     if (~corr_logic_en) corr_state_next = CORR_NO_ERR;
                     else if (~send_scrub) corr_state_next = CORR_WAIT_RD;
                  end
               CORR_WAIT_RD: begin // wait until all pending reads have been sent to the HIF
                     corr_write_mode_r  = 1'b1;
                     if (saq_empty & ~active_reads) begin
                        read_corr_burst_r = 1'b1;
                        corr_state_next   = CORR_WRITE;
                     end
                  end
               CORR_WRITE: begin // generate write(s) by reading the tokens in from the queue and muxing the address
                     corr_write_mode_r = 1'b1;
                     read_corr_burst_r = 1'b1;
                     if (tq_empty) begin
                        corr_state_next   = CORR_WAIT_WR;
                     end
                     else begin
                        send_corr_burst_r = send_scrub_en;
                     end
                  end
               default: begin // CORR_WAIT_WR: wait until all writes have been sent
                     corr_write_mode_r   = 1'b1;
                     if (saq_empty & ~active_writes) begin
                        corr_state_next = CORR_NO_ERR;
                     end
                     else begin
                        read_corr_burst_r = 1'b1;
                     end
                  end
            endcase
         end

         assign ie_corr_write_mode  = corr_write_mode_r;
         assign ie_read_corr_burst  = read_corr_burst_r;
         assign nonie_read_corr_burst = 1'b0;
         assign ie_send_corr_burst  = send_corr_burst_r;
         assign tq_rd            = send_corr_burst_r;

         always @(*) begin: ie_scrub_burst_decoded_COMB_PROC
            ie_scrub_burst_decoded = {BRSTCNTW{1'b0}};
            ie_scrub_burst_single  = 1'b0;
            case (reg_arb_scrub_burst)
               3'b010: ie_scrub_burst_decoded = 11'b000_0001_0000;  // 16 scrubs, 2 blocks
               3'b011: ie_scrub_burst_decoded = 11'b000_0010_0000;  // 32 scrubs, 4 blocks
               default: ie_scrub_burst_decoded = 11'b000_0000_1000;  // 8 scrubs, 1 block
            endcase 
         end

         // address mask (start/end address)
         assign ie_address_range_mask  = {{(HIF_ADDR_WIDTH-BRDWR-1){1'b1}}, ~addr_cnt_incr_m1};
         assign ie_address_start_mask  = corr_logic_en ? (ie_address_range_mask & ~l3_iecc_col_mask) : ie_address_range_mask;

         // region detect
         wire [7:0] ecc_region_map_ext; // extend ECC_RM_WIDTH to 8 bits to avoid X state.
         wire       ecc_region_map_bit7;
         wire       ecc_region_lower;
         wire       ecc_region_other;

         assign ecc_region_map_bit7 = ~|reg_ddrc_ecc_region_map_granu ? 1'b0 : reg_ddrc_ecc_region_map_other;
         assign ecc_region_map_ext = { ecc_region_map_bit7, reg_ddrc_ecc_region_map};


     
     
     localparam  ADDRW = 2**(ECC_H3_WIDTH); 
     logic [ADDRW-1:0] addr_cnt_iecc_col_mask;
     assign addr_cnt_iecc_col_mask = {{(ADDRW-HIF_ADDR_WIDTH){1'b0}},{addr_cnt}};

         assign ext_hbits_vld   = reg_ddrc_ecc_region_map_granu==2'b01 ? ~|addr_cnt_iecc_col_mask[h3_iecc_col_mask -: 1] :
                                  reg_ddrc_ecc_region_map_granu==2'b10 ? ~|addr_cnt_iecc_col_mask[h3_iecc_col_mask -: 2] :
                                  reg_ddrc_ecc_region_map_granu==2'b11 ? ~|addr_cnt_iecc_col_mask[h3_iecc_col_mask -: 3] :
                                                                         1'b1;
         //spyglass disable_block SelfDeterminedExpr-ML
         //SMD: Self determined expression '(h3_iecc_col_mask - reg_ddrc_ecc_region_map_granu)' found in module 'DWC_ddr_umctl2_sbr'
         //SJ: No suitable (better) re-coding found
         assign iecc_region_id   = addr_cnt_iecc_col_mask[(h3_iecc_col_mask-reg_ddrc_ecc_region_map_granu)-:REG_ID_WIDTH];
         //spyglass enable_block SelfDeterminedExpr-ML
         assign ie_iecc_hole        = &addr_cnt_iecc_col_mask[h3_iecc_col_mask-:REG_ID_WIDTH] & iecc_en;


         assign ecc_region_lower = ext_hbits_vld & ecc_region_map_ext[iecc_region_id];
         assign ecc_region_other = reg_ddrc_ecc_region_map_other & ~ie_iecc_hole & (
                                   reg_ddrc_ecc_region_map_granu==2'b01 ? |addr_cnt_iecc_col_mask[h3_iecc_col_mask -: 1] :
                                   reg_ddrc_ecc_region_map_granu==2'b10 ? |addr_cnt_iecc_col_mask[h3_iecc_col_mask -: 2] :
                                   reg_ddrc_ecc_region_map_granu==2'b11 ? |addr_cnt_iecc_col_mask[h3_iecc_col_mask -: 3] :
                                                                  1'b0
                                   );

         assign ie_iecc_cmd_valid   = (ecc_region_lower | ecc_region_other) | ~corr_logic_en;

         assign ie_addr_cnt_valid   = ~lpddr3_row13_14 & ie_iecc_cmd_valid & ~sbr_wrong_channel & addr_in_range & ~current_rank_invalid;

         wire iecc_vld, iecc_cmd_end_unused;

         DWC_ddr_umctl2_xpi_iecc_info
         
         #(
            .M_ADDRW       (HIF_ADDR_WIDTH),
            .REG_ID_WIDTH  (3),
            .BRW           (BRDWR),
            .ECC_H3_WIDTH  (ECC_H3_WIDTH),
            .ECC_RM_WIDTH  (ECC_RM_WIDTH),
            .ECC_RMG_WIDTH (ECC_RMG_WIDTH)
         )
         U_iecc_info
         (
            .addr_in             (saq_q),
            .ecc_region_map      (reg_ddrc_ecc_region_map),
            .ecc_region_map_granu(reg_ddrc_ecc_region_map_granu),
            .ecc_region_map_other(reg_ddrc_ecc_region_map_other),
            .reg_xpi_burst_rdwr  (reg_ddrc_burst_rdwr_mod),
            .h3_iecc_col_mask    (h3_iecc_col_mask),
            .ecc_en              (iecc_en),
            .ecc_blk_valid       (iecc_vld),
            .ecc_blk_end         (iecc_cmd_end_unused) // not used
         );
         assign ie_rcmd_end_ie   = 1'b0; // not used
         assign ie_rcmd_vld_ie   = iecc_vld & sbr_arvalid;

         assign ie_wcmd_vld_ie   = iecc_vld & sbr_awvalid;

         assign ie_wcmd_end_ie   = 1'b0; // not used

         assign ie_sbr_wdata_mask_full_full = {NBEATS{1'b1}};
         assign ie_sbr_wdata_mask_full_half = {{(NBEATS/2){1'b0}},{(NBEATS/2){1'b1}}};
         
         if ((MEMC_BURST_LENGTH==16) 
            ) begin: MBL16_wlen
            assign ie_sbr_rxcmd_wlength = reg_ddrc_burst_rdwr_mod_m1==NBEATS-1   ? FULL_BURST :
                                          reg_ddrc_burst_rdwr_mod_m1==NBEATS/2-1 ? HALF_BURST : QUARTER_BURST;

            assign ie_sbr_wdata_mask_full_quarter = {{(3*NBEATS/4){1'b0}},{(NBEATS/4){1'b1}}};

         end
         else begin: MBLlt16_wlen

            assign ie_sbr_rxcmd_wlength = reg_ddrc_burst_rdwr_mod_m1==NBEATS-1   ? FULL_BURST : HALF_BURST;

            assign ie_sbr_wdata_mask_full_quarter = ie_sbr_wdata_mask_full_half;

         end

         // parity register
         DWC_ddr_umctl2_par_reg
         
         #(
            .DW                 (SBR_IE_VEC_WIDTH),
            .OCCAP              (OCCAP_EN),
            .OCCAP_PIPELINE_EN  (OCCAP_PIPELINE_EN),
            .REG_EN             (0),
            .SL_W               (8),
            .RESVAL             (SBR_IE_VEC_RESVAL))
         U_sbr_ie_vec_r
         (  .clk        (clk),
            .rst_n      (rst_n),
            .data_in    (sbr_ie_vec_i),
            .reg_set    (1'b0),
            .parity_en  (reg_ddrc_occap_en),
            .poison_en  (1'b0),
            .data_out   (sbr_ie_vec_r),
            .parity_err (ie_sbr_ie_vec_parity_err));
  

      end
      else begin: IECC_NEN
        
         always @(*) begin: ie_scrub_burst_decoded_COMB_PROC
            ie_scrub_burst_decoded = {BRSTCNTW{1'b0}};
            ie_scrub_burst_single  = 1'b0;                   
         end


         assign ie_addr_cnt_valid              = 1'b0;

         assign ie_corr_write_mode             = 1'b0;
 
         assign ie_read_corr_burst             = 1'b0;
         assign nonie_read_corr_burst          = ~rmw_fifo_empty;
   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Used in generate block
         assign ie_send_corr_burst             = 1'b0;
         assign ie_corr_addr                   = {HIF_ADDR_WIDTH{1'b0}};
   //spyglass enable_block W528
         assign ie_tq_par_err                  = 1'b0;
         assign ie_address_ram_par_err         = 1'b0;
         assign ie_iecc_cmd_valid              = 1'b1;
         assign ie_sbr_ie_vec_parity_err       = 1'b0;
         assign ie_iecc_hole                   = 1'b0;
         assign ie_sbr_wdata_mask_full_full    = {NBEATS{1'b1}};
         assign ie_sbr_wdata_mask_full_half    = {NBEATS{1'b1}};
         assign ie_sbr_wdata_mask_full_quarter = {NBEATS{1'b1}};
         assign ie_address_range_mask          = {HIF_ADDR_WIDTH{1'b0}};
         assign ie_address_start_mask          = {HIF_ADDR_WIDTH{1'b0}};
         assign ie_rcmd_vld_ie                 = 1'b0;
         assign ie_rcmd_end_ie                 = 1'b0;
         assign ie_wcmd_vld_ie                 = 1'b0;
         assign ie_wcmd_end_ie                 = 1'b0;
         assign ie_iecc_burst_en               = 1'b0;
         assign ie_sbr_rxcmd_wlength           = {CMD_LEN_BITS{1'b0}};

         assign generate_rmw  =  (((reg_arb_scrub_correction_mode_port0== 2'b11) &&  (|hif_rvalid_int)) || 
                                  ((reg_arb_scrub_correction_mode_port0== 2'b01) &&  hif_rvalid_int[N_PORTS-1]) || 
                                  ((reg_arb_scrub_correction_mode_port0== 2'b10) && (|hif_rvalid_int[N_PORTS-2:0])));

 
         //One write for each response.   
         //once there is a correctable error the additional writes must be
         //blocked.
         //transaction may have corr error on one lane & uncorr on another. 
         //SBR will generate RMW in such a case.
         assign rmw_wr        = (hif_corr_ecc_err_int ) && ~same_addr && generate_rmw && ~sbr_stop_req_latched;
         assign rmw_d         = rcvd_rmw_addr; 
         assign rmw_rd        = sbr_awvalid && hif_awready && ~rmw_fifo_empty;
   
         //It is valid to assign FIFO empty to this signal rather than
         //corr_write_mode. This signal must be asserted as
         //long as RMW request must be transferred.    
          
                      
         //RMW FIFO Instantiation.
         //GFIFO doesn't have an option of combinatorial empty op. 
         //empty must be registered.rmw_rd expects that.
         //rmw_fifo_full_ununsed must also be registered. 
         DWC_ddr_umctl2_gfifo
          
         #(
          .WIDTH       (RMW_FIFOW),
          .DEPTH       (RMW_FIFOD),
          .ADDR_WIDTH  (RMWD_LG2),
          .COUNT_WIDTH (RMWD_LG2 + 1),
          .OCCAP_EN    (OCCAP_EN),
          .OCCAP_PIPELINE_EN  (OCCAP_PIPELINE_EN)
          )
         rmw_fifo (
             .clk             (clk),
             .rst_n           (rst_n),
             .wr              (rmw_wr && ~rmw_fifo_full),
             .d               (rmw_d),
             .rd              (rmw_rd),
             .par_en          (reg_ddrc_occap_en),
             .init_n          (1'b1),
             .ff              (rmw_fifo_full),
   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Used in generate block
             .wcount          (rmw_fifo_wcount_unsed),
   //spyglass enable_block W528
             .q               (rmw_q),
             .fe              (rmw_fifo_empty),
             .par_err         (rmw_par_err)
             `ifndef SYNTHESIS
             `ifdef SNPS_ASSERT_ON
             ,.disable_sva_fifo_checker_rd (1'b0)
             ,.disable_sva_fifo_checker_wr (1'b0)
             `endif // SNPS_ASSERT_ON
             `endif // SYNTHESIS
         );
 
        //Scrubber Dropped transaction counter
        //this counter will hold its value once it reaches max.
        //
        //If correction is only for on-demand reads, the drop count can change even when scrubber is not enabled.
        //so, when such a count is present, it will get cleared when the
        //scrubber is going from disable to enable. This is expected behavior. 

        assign scrub_dis_to_enab  = scrub_en_int && ~reg_arb_scrub_en_r;

        assign drop_scrub_cnt_nxt =  
                                    ((rmw_wr & rmw_fifo_full && ~(&drop_scrub_cnt)) ? (drop_scrub_cnt + 1) : 
                                                                                      ((scrub_dis_to_enab) ? {SCRUB_DROP_CNT_WIDTH{1'b0}}: drop_scrub_cnt));
   

      end
   endgenerate

   wire [HIF_ADDR_WIDTH-1:0] addr_cnt_alt_unused;
   wire [1:0]                addr_cnt_alt_cs;
   wire                      addr_cnt_alt_valid;

   
   // 
   reg [BRSTCNTW-1:0] nonie_scrub_burst_decoded;
   reg nonie_scrub_burst_single;

   always @(*) begin: nonie_scrub_burst_decoded_COMB_PROC
      nonie_scrub_burst_decoded = {BRSTCNTW{1'b0}};
      nonie_scrub_burst_single  = 1'b0;
      case (reg_arb_scrub_burst)
         3'b001: begin 
             nonie_scrub_burst_decoded = 11'b000_0000_0001;  // 1 scrub (don't skip timeout)
             nonie_scrub_burst_single  = 1'b1;
         end
         3'b010:  nonie_scrub_burst_decoded = 11'b000_0000_0100;  // 4 scrubs (skip 3 timeouts)
         3'b011:  nonie_scrub_burst_decoded = 11'b000_0001_0000;  // 16 scrubs (skip 15 timeouts)
         3'b100:  nonie_scrub_burst_decoded = 11'b000_0100_0000;  // 64 scrubs (skip 63 timeouts)
         3'b101:  nonie_scrub_burst_decoded = 11'b001_0000_0000;  // 256 scrubs (skip 255 timeouts)
         default: /* 3'b110 */  nonie_scrub_burst_decoded = 11'b100_0000_0000;  // 1024 scrubs (skip 1023 timeouts)
      endcase 
   end

   wire nonie_addr_cnt_valid   = ~lpddr3_row13_14 & ~sbr_wrong_channel & addr_in_range & ~current_rank_invalid;
   

   // MUX  between IE and NONIE cases based on ecc_type
   assign scrub_burst_decoded = (reg_ddrc_ecc_type) ?  ie_scrub_burst_decoded : nonie_scrub_burst_decoded;
   assign scrub_burst_single  = (reg_ddrc_ecc_type) ?  ie_scrub_burst_single : nonie_scrub_burst_single;
   assign addr_cnt_valid      = (reg_ddrc_ecc_type) ? ie_addr_cnt_valid : nonie_addr_cnt_valid;
   
   assign corr_write_mode     = (reg_ddrc_ecc_type) ? ie_corr_write_mode : 1'b0;
   assign read_corr_burst     = (reg_ddrc_ecc_type) ? ie_read_corr_burst : nonie_read_corr_burst;
   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Used in generate block
   assign send_corr_burst     = (reg_ddrc_ecc_type) ? ie_send_corr_burst : 1'b0;
   assign corr_addr           = (reg_ddrc_ecc_type) ? ie_corr_addr : {HIF_ADDR_WIDTH{1'b0}};
   //spyglass enable_block W528
   assign tq_par_err          = (reg_ddrc_ecc_type) ? ie_tq_par_err : 1'b0;
   assign address_ram_par_err = (reg_ddrc_ecc_type) ? ie_address_ram_par_err : 1'b0;
   assign iecc_cmd_valid      = (reg_ddrc_ecc_type) ? ie_iecc_cmd_valid : 1'b1;
   assign sbr_ie_vec_parity_err  = (reg_ddrc_ecc_type) ? ie_sbr_ie_vec_parity_err : 1'b0;
   assign iecc_hole           = (reg_ddrc_ecc_type) ? ie_iecc_hole : 1'b0;
   
   assign sbr_wdata_mask_full_full   = (reg_ddrc_ecc_type) ? ie_sbr_wdata_mask_full_full : {NBEATS{1'b1}};
   assign sbr_wdata_mask_full_half    = (reg_ddrc_ecc_type) ? ie_sbr_wdata_mask_full_half : {NBEATS{1'b1}};
   assign sbr_wdata_mask_full_quarter = (reg_ddrc_ecc_type) ? ie_sbr_wdata_mask_full_quarter : {NBEATS{1'b1}};

   
   // address mask (start/end address)
   assign address_range_mask  = (reg_ddrc_ecc_type) ? ie_address_range_mask : {{(HIF_ADDR_WIDTH-BRDWR-1){1'b1}}, ~addr_cnt_incr_m1};
   assign address_start_mask  = (reg_ddrc_ecc_type) ? ie_address_start_mask: address_range_mask;
   assign rcmd_vld_ie         = (reg_ddrc_ecc_type) ? ie_rcmd_vld_ie : 1'b0; 
   assign rcmd_end_ie         = (reg_ddrc_ecc_type) ? ie_rcmd_end_ie : 1'b0;
   assign wcmd_vld_ie         = (reg_ddrc_ecc_type) ? ie_wcmd_vld_ie : 1'b0; 
   assign wcmd_end_ie         = (reg_ddrc_ecc_type) ? ie_wcmd_end_ie : 1'b0;
   assign iecc_burst_en       = (reg_ddrc_ecc_type) ? ie_iecc_burst_en : 1'b0;
   assign sbr_rxcmd_wlength   = (reg_ddrc_ecc_type) ? ie_sbr_rxcmd_wlength : 0;

   // End of MUX between IE and NONIE cases based on ecc_type
         
   //end


   //spyglass disable_block W415a
   //SMD: Signal is being assigned multiple times in same always block. 
   //SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
   always @(*) begin: IE_reg_incr_gen
      integer i;
      iecc_region_incr = {HIF_ADDR_WIDTH{1'b0}};
      for (i=0; i<HIF_ADDR_WIDTH; i=i+1) begin
         //spyglass disable_block SelfDeterminedExpr-ML
         //SMD: Self determined expression '(h3_iecc_col_mask - reg_ddrc_ecc_region_map_granu)' found in module 'DWC_ddr_umctl2_sbr'
         //SJ: No suitable (better) re-coding found
         if (i == (h3_iecc_col_mask-reg_ddrc_ecc_region_map_granu-REG_ID_WIDTH)) iecc_region_incr[i] = 1'b1;
         //spyglass enable_block SelfDeterminedExpr-ML
      end
   end
   //spyglass enable_block W415a

   //assign iecc_region_incr = {{(REG_ID_WIDTH-1){1'b0}},1'b1,{(HIF_ADDR_WIDTH-REG_ID_WIDTH){1'b0}}};
   assign iecc_region_mask = {{REG_ID_WIDTH{1'b1}},{(HIF_ADDR_WIDTH-REG_ID_WIDTH){1'b0}}};

   // Scrubber FSM combinatorial
   always @(*) begin: st_sbr_nxt_COMB_PROC
      st_sbr_nxt = ST_SBR_DIS;
      case (st_sbr)
        ST_SBR_NM: begin
           if (~scrub_en_int | dis_sbr_req | ddr5_all_ranks_in_scrub_dis_or_unpopulated)
             st_sbr_nxt = ST_SBR_DIS;
//ST_SBR_NM -> ST_SBR_LP is based on the burst_length programmed.
//From Normal Mode to LP, the burst may have already started. If it has started, wait till the burst is completed.
//If burst has not yet started change states. 
           else if (((((scrub_burst_cntzero & saq_wr) | skip_current_rank) & burst_first & ~saq_full) | (~(burst_first))) & ((ctl_in_hw_controlled_lp_mode&~reg_ddrc_ddr5) | (ctl_in_hw_controlled_lp_mode_ddr5&reg_ddrc_ddr5)))  
             st_sbr_nxt = ST_SBR_LP;
           else
             st_sbr_nxt = ST_SBR_NM;
        end

        ST_SBR_LP: begin
           if (~scrub_en_int | dis_sbr_req | ddr5_all_ranks_in_scrub_dis_or_unpopulated)
             st_sbr_nxt = ST_SBR_DIS;
           else if (((((scrub_burst_cntzero & saq_wr) | skip_current_rank) & burst_first & ~saq_full) | (~burst_first)) & ((ctl_in_normal_mode&~reg_ddrc_ddr5) | (ctl_in_normal_mode_ddr5&reg_ddrc_ddr5) | (ctl_in_sw_controlled_lp_mode&~reg_ddrc_ddr5) | (ctl_in_sw_controlled_lp_mode_ddr5&reg_ddrc_ddr5)))
             st_sbr_nxt = ST_SBR_NM;
           else
             st_sbr_nxt = ST_SBR_LP;         
        end

        default: begin   // ST_SBR_DIS
           if (~scrub_en_int | dis_sbr_req | ddr5_all_ranks_in_scrub_dis_or_unpopulated)
             st_sbr_nxt = ST_SBR_DIS;
           else if (dis_sbr_keep_addr & ~dis_sbr_req)
             st_sbr_nxt = ST_SBR_NM;
           else if ((ctl_in_normal_mode&~reg_ddrc_ddr5) | (ctl_in_normal_mode_ddr5&reg_ddrc_ddr5) | (ctl_in_sw_controlled_lp_mode&~reg_ddrc_ddr5) | (ctl_in_sw_controlled_lp_mode_ddr5&reg_ddrc_ddr5))
             st_sbr_nxt = ST_SBR_NM;
           else if ((ctl_in_hw_controlled_lp_mode&~reg_ddrc_ddr5) | (ctl_in_hw_controlled_lp_mode_ddr5&reg_ddrc_ddr5))
             st_sbr_nxt = ST_SBR_LP;
           else
             st_sbr_nxt = ST_SBR_DIS;  // keep disabled during init
        end
      endcase
   end
   

   assign dis_sbr_keep_addr = dis_sbr_ack | dis_sbr_req;

   assign scrubber_dis       = st_sbr[STBF_SBR_DIS];
   assign scrubber_in_lp     = st_sbr[STBF_SBR_LP];
   assign scrubber_in_nm     = st_sbr[STBF_SBR_NM];
   assign scrub_restore_latched_nxt = 1'b0;
   wire [HIF_ADDR_WIDTH-1:0] reg_arb_scrub_restore_address;
   assign reg_arb_scrub_restore_address = {HIF_ADDR_WIDTH{1'b0}};

   assign skip_current_rank_l = skip_current_rank & ~saq_full;
   // address next calc
   always @(*) begin: addr_cnt_COMB_PROC
      addr_cnt_next_wider = addr_cnt;
      casez ({scrub_restore_latched_nxt,scrubber_dis,dis_sbr_keep_addr,skip_current_rank_l,lpddr3_row13_14,sbr_wrong_channel,iecc_cmd_valid,saq_wr,addr_in_range,corr_write_mode})
         10'b11????????: addr_cnt_next_wider = {1'b0,(reg_arb_scrub_restore_address & address_range_mask)};
         10'b011???????: addr_cnt_next_wider = addr_cnt;
         10'b010???????: addr_cnt_next_wider = start_addr;
         10'b00??????0?: addr_cnt_next_wider = start_addr;
         10'b00??1???1?: addr_cnt_next_wider = addr_cnt + addr_row_shift;
         10'b00??01??1?: addr_cnt_next_wider = addr_cnt + addr_dch_incr;
         10'b00?100??1?: addr_cnt_next_wider = next_rank_valid_addr[HIF_ADDR_WIDTH-1:0];
         10'b00?0000?1?: addr_cnt_next_wider = (addr_cnt + iecc_region_incr) & iecc_region_mask;
         10'b00?0001110: addr_cnt_next_wider = addr_cnt + addr_cnt_incr;
         default: addr_cnt_next_wider = addr_cnt;
      endcase
   end
   
   assign addr_cnt_next = addr_cnt_next_wider[HIF_ADDR_WIDTH-1:0];

  assign next_rank_valid_addr = {(HIF_ADDR_WIDTH+1){1'b0}};
  assign skip_current_rank = 1'b0;
  assign current_rank_invalid = 1'b0;
  assign sbr_addr_log_par_err = 1'b0;

   // Scrub burst counter
   // 1. Scrubber is disabled, load from the register & keep.
   // 2. SBR is in LP But no during_lp = 1. Load Zero. 
   // 3. Inline ECC, Normal mode - load full burst size.
   // 4. SBR in LP or IECC, Read Mode, Decrement Counter.  For LP, there is 
   // an assumed case that, burst_count !=0.
   // 5. In Sideband ECC, Normal Mode - load the counter, burst size.
   // 5. there is no check that, the Counter value = 1, so if the register is
   // loaded with other values, it will work.
   // (before 6. was added).In case of LP, the first condition will ensure, that scrub_burst_decoded
   // is loaded. 
   // 6. will ensure that the scrub_burst_length_lp will be picked when lp
   // mode is enabled.
   // If DIS->LP Occurs, the burst_length_lp will be picked once the state
   // moves into LP.
   // If NM->LP occur, the burst_length_lp is picked after the current burst
   // is finished.
   logic scrub_burst_update;
   assign scrub_burst_update = (((st_sbr == ST_SBR_DIS) && (st_sbr_nxt == ST_SBR_NM)) || ((st_sbr == ST_SBR_DIS) && (st_sbr_nxt == ST_SBR_LP)) || 
                                ((st_sbr == ST_SBR_NM)  && (st_sbr_nxt == ST_SBR_LP)) || ((st_sbr == ST_SBR_LP)  && (st_sbr_nxt == ST_SBR_NM))) ;
 
   always @(*) begin: scrub_burst_cnt_COMB_PROC
      scrub_burst_cnt_nxt = scrub_burst_cnt;
      if (scrubber_dis | (scrub_burst_update && ~(tscrubi_cntzero && scrub_skip_cntzero))) begin //1.
        scrub_burst_cnt_nxt = (scrub_burst_decoded - 1'b1);
      end else if (scrub_burst_update && (tscrubi_cntzero && scrub_skip_cntzero)) begin //
        scrub_burst_cnt_nxt = (scrub_burst_decoded - 2'b10);
      end else if (scrubber_in_lp & ~reg_arb_scrub_during_lowpower) begin //2.
        scrub_burst_cnt_nxt = {BRSTCNTW{1'b0}};
      end else if ((scrubber_in_lp & reg_arb_scrub_during_lowpower) & (skip_current_rank | (saq_wr & scrub_burst_cntzero)) & ~saq_full) begin //6.
        scrub_burst_cnt_nxt = (scrub_burst_decoded - 1'b1);
      end else if ((scrubber_in_nm & iecc_burst_en) & (skip_current_rank | (saq_wr & scrub_burst_cntzero)) & ~saq_full) begin //6.
        scrub_burst_cnt_nxt = (scrub_burst_decoded - 1'b1);
      end else if ((scrubber_in_lp | iecc_burst_en) & ~scrub_burst_cntzero & ~corr_write_mode) begin //4.
        if (saq_wr) scrub_burst_cnt_nxt = scrub_burst_cnt - 1'b1;
      end else if (scrubber_in_nm & ~iecc_burst_en) begin //5.
        scrub_burst_cnt_nxt = (scrub_burst_decoded - 1'b1);
      end
   end

   assign scrub_burst_cntzero = ~|scrub_burst_cnt;
   
   assign dis_tscrubi_cnt     = ~|reg_arb_scrub_interval;
  
   // Scrub interval counter

   // Note: There is no point to pause the timer if the FIFO is full. If cannot push, the
   // address will not increment, but the scrub period will increase.
 
   always @(*) begin: tscrubi_cnt_COMB_PROC
      tscrubi_cnt_nxt = tscrubi_cnt;
      if (scrubber_dis)
        tscrubi_cnt_nxt = {reg_arb_scrub_interval, {(SCRUBI_GRANULARITY){1'b0}}} - 1'b1;
      else if (dis_tscrubi_cnt & ~corr_write_mode)
        tscrubi_cnt_nxt = {SCRUBI_CNTW{1'b0}};
      else if (~tscrubi_cntzero & ~corr_write_mode)
        tscrubi_cnt_nxt = tscrubi_cnt - 1'b1;
      else if (tscrubi_cntzero)
        tscrubi_cnt_nxt = {reg_arb_scrub_interval, {(SCRUBI_GRANULARITY){1'b0}}} - 1'b1;
   end   

   assign tscrubi_cntzero     = ~|tscrubi_cnt;
  //Will re-load when Scrubber's mode changes 
   assign scrub_skip_cnt_load = scrub_burst_decoded - 1'b1;
   
   // Scrub interval skip counter
   always @(*) begin: scrub_skip_cnt_COMB_PROC
      scrub_skip_cnt_nxt = scrub_skip_cnt;
      if (scrubber_dis | dis_tscrubi_cnt)
        scrub_skip_cnt_nxt = {SKPCNTW{1'b0}};                         // scrub_burst is ignored during normal operation
  //Will re-load when Scrubber's mode changes 
      else if ((scrubber_in_lp | iecc_burst_en ) & burst_started)
        scrub_skip_cnt_nxt = scrub_skip_cnt_load[SKPCNTW-1:0]; // initial load value
      else if (~scrub_skip_cntzero & tscrubi_cntzero & ~corr_write_mode)
        scrub_skip_cnt_nxt = scrub_skip_cnt - 1'b1;
   end

   assign scrub_skip_cntzero = ~|scrub_skip_cnt;
   
   always @(*) begin: burst_started_COMB_PROC
      burst_started_nxt = burst_started;
      burst_first_nxt   = burst_first;
      if (scrubber_dis) begin
         burst_started_nxt = 1'b0;
         burst_first_nxt   = 1'b0;
      end
      else if ((scrubber_in_lp | iecc_burst_en) & ~burst_first & ~scrub_burst_single & ~corr_write_mode & (saq_wr|skip_current_rank)) begin
         if (saq_wr) begin
           burst_first_nxt   = 1'b1;
           burst_started_nxt = 1'b1;
         end else if (skip_current_rank) begin
           burst_started_nxt = 1'b1;
         end
      end 
      else if (((scrub_burst_cntzero & saq_wr) | skip_current_rank) & ~saq_full) begin
         burst_first_nxt   = 1'b0;
         burst_started_nxt = 1'b0;
      end 
      else begin
         burst_started_nxt = 1'b0;
      end
   end

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS

   property p_burst_started_pulse_w;
   @(posedge clk) disable iff(!rst_n)
     (burst_started==1'b1) |-> (burst_started_nxt==1'b0); 
   endproperty
   //SNPS_XVP_DESC: Check to ensure that burst_started is a pulse with 1 clk width.    
   a_burst_started_pulse_w : assert property (p_burst_started_pulse_w) else 
   $display("-> %0t ERROR: burst_started should be a pulse with 1 clock period of width ", $realtime);

`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON

   // SBR outputs  
   assign port_num   = A_PORT_NUM;
   assign arid       = {IDW{1'b0}};
   assign arlast     = 1'b0;

   // Token counter
   assign release_token = hif_rvalid_int[N_PORTS-1] & hif_rlast_pkt_int;
   assign gen_token     = sbr_arvalid & hif_arready;

   DWC_ddr_umctl2_xpi_tm
   
   #(.USE2RAQ     (0),
     .NTOKENS     (1<<TOKEN_WIDTH),  
     .NTOKENS_LG2 (TOKEN_WIDTH),
     .READ_DATA_INTERLEAVE_EN (0), //dummy value
     .OCCAP_EN    (OCCAP_EN),
     .OCCAP_PIPELINE_EN  (OCCAP_PIPELINE_EN),
     .RDWR_ORDERED(0), //dummy value
     .NUM_CH_LG2  (5), //dummy value
     .NUM_VIR_CH  (32), //dummy value
     .SBR         (1))
   U_sbr_tm
   (
      // Outputs
   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Used in generate block
     .token            (atoken),
   //spyglass enable_block W528
   //spyglass disable_block W528
   //SMD: A signal or variable is set but never read
   //SJ: Used in generate block
     .empty_blue       (tm_empty),
   //spyglass enable_block W528
     .empty_red        (tm_empty_red_unused),
     .occap_xpi_tm_par_err  (occap_tm_par_err),
     // Inputs      
     .clk              (clk),          // clock
     .rst_n            (rst_n),        // asynchronous reset
     .gen_token_blue   (gen_token),  // generate a new token
     .gen_token_red    (1'b0),
     .release_token    (release_token),
     .rtoken           (rtoken),
     .locked_ch_raq_red(1'b0),
     .arvalid_blue     (1'b0),
     .arvalid_red      (1'b0),
     .rrb_is_locked    (1'b0),
     .locked_ch        (5'h0),
     .ch_arlast_received(32'h0),
     .reg_rdwr_ordered_en(1'b0),
     .reg_ddrc_occap_en(reg_ddrc_occap_en));

   assign sbr_rxcmd_token  = {atoken, {(MEMC_TAGBITS-(TOKEN_WIDTH+IDW+A_NPORTS_LG2+3)){1'b0}}, rcmd_vld_ie, rcmd_end_ie, arlast, arid, port_num};

  `ifndef SYNTHESIS
    assign sbr_periodic_rmw = sbr_awvalid && (reg_arb_scrub_cmd_type_port0 == 2'b10) && ~read_corr_burst; 
  `endif //SYNTHESIS
 
  assign sbr_wdata_ptr = { 1'b0,wcmd_vld_ie,wcmd_end_ie,{(RSRVD_WDATA_PTR_BITS){1'b0}}, port_num};

   generate
      if (MEMC_BURST_LENGTH==16) begin: MBL16        
         // If reg_arb_bl_exp_mode is set, burst length depends also on data_bus_width
          assign burst_rdwr_bus_width      =  reg_ddrc_burst_rdwr;
         
         assign sbr_rxcmd_rlength[0]      = (ctl_bl2 | ctl_bl4) ? 1'b1 : 1'b0;
         assign sbr_rxcmd_rlength[1]      = (ctl_bl2 | ctl_bl4 | ctl_bl8) ? 1'b1 : 1'b0;
         assign reg_ddrc_burst_rdwr_mod   = burst_rdwr_bus_width;

      end
      else if (MEMC_BURST_LENGTH==8) begin: MBL8
         // If reg_arb_bl_exp_mode is set, burst length depends also on data_bus_width
         assign burst_rdwr_bus_width      = (~reg_arb_bl_exp_mode | ctl_fbw) ? reg_ddrc_burst_rdwr : BL4;

         assign sbr_rxcmd_rlength         = (ctl_bl2 | ctl_bl4) ? 1'b1 : 1'b0;
         // if BL8 controller and burst_rdwr is greater than BL8 set burst_rdwr to BL8
         assign reg_ddrc_burst_rdwr_mod   = (ctl_bl16) ? BL8 : burst_rdwr_bus_width;
      end
      else begin: MBL4 // MEMC_BURST_LENGTH==4
         // If reg_arb_bl_exp_mode is set, burst length depends also on data_bus_width
         assign burst_rdwr_bus_width      = (~reg_arb_bl_exp_mode | ctl_fbw) ? reg_ddrc_burst_rdwr : BL2;

         assign sbr_rxcmd_rlength         = ctl_bl2;
         // if BL8 controller and burst_rdwr is greater than BL8 set burst_rdwr to BL8
         assign reg_ddrc_burst_rdwr_mod   = (ctl_bl8 | ctl_bl16) ? BL4 : burst_rdwr_bus_width;
      end
   endgenerate


   //Calculate the address increment (double the calculated burst_rdwr)
   assign addr_cnt_incr = {reg_ddrc_burst_rdwr_mod,1'b0};
   assign addr_cnt_incr_m1 = addr_cnt_incr - 1'b1;
   
   // Align the maximum range to increment boundaries
   assign max_addr_cnt_tmp    = sbr_address_range_int & address_range_mask;
   assign start_addr_tmp      = sbr_address_start_int & address_start_mask;
   generate
     if(DDR4_DUAL_CHANNEL==1 && DATA_CHANNEL_INTERLEAVE==1) begin: DualChannel_intrlv
    //spyglass disable_block W164a
    //SMD: LHS: 'max_addr_cnt' width 34 is less than RHS: '(max_addr_cnt_tmp + addr_dch_incr)' width 35 in assignment / LHS: 'max_addr_cnt' width 34 is less than RHS: '((max_addr_cnt_tmp << 1) + addr_dch_incr)' width 36 in assignment
    //SJ: 1) for '(max_addr_cnt_tmp - addr_dch_incr)' : The "DCH bit" is set in both the signals - max_addr_cnt_tmp, data_channel_addrmap_mask; max_addr_cnt_tmp is greater than addr_dch_incr( = data_channel_addrmap_mask); max_addr_cnt_tmp is 36 bit. addr_dch_incr can go up only till bit position 32; Hence the subtraction will not result in a borrow bit.
    //    2) for '(max_addr_cnt_tmp + addr_dch_incr)' : Here, the addition will occur only if "DCH bit" is not set in the max_addr_cnt_tmp. Hence the value of max_addr_cnt_tmp is within the Channel 0 address space. The addition is to move it into the Channel 1 address space. It won't result in any overflow.
       if (CHANNEL_NUM==0) begin : SBR_MAX_ADDR_CNT_CHANNEL_0 
     // In dual channel config, always dch_bit need to be set "0".
          assign max_addr_cnt   = (~|data_channel_addrmap_mask)                     ? max_addr_cnt_tmp :
                                  (max_addr_cnt_tmp == data_channel_addrmap_mask)   ? max_addr_cnt_tmp + addr_dch_incr :
                                  (|(max_addr_cnt_tmp & data_channel_addrmap_mask)) ? max_addr_cnt_tmp - addr_dch_incr :
                                                                                      max_addr_cnt_tmp; 
          assign start_addr     = (start_addr_tmp & (~data_channel_addrmap_mask));
       end else begin : SBR_MAX_ADDR_CNT_CHANNEL_1
     // In dual channel config, always dch_bit need to be set "1".
          assign max_addr_cnt   = (~|data_channel_addrmap_mask)                      ? max_addr_cnt_tmp :
                                  (max_addr_cnt_tmp == data_channel_addrmap_mask)    ? (max_addr_cnt_tmp << 1) + addr_dch_incr :
                                  (~|(max_addr_cnt_tmp & data_channel_addrmap_mask)) ? max_addr_cnt_tmp + addr_dch_incr : 
                                                                                       max_addr_cnt_tmp; 
          assign start_addr     = (start_addr_tmp | data_channel_addrmap_mask);
       end
    //spyglass enable_block W164a
     end else begin: nDualChannel_intrlv
         assign max_addr_cnt = max_addr_cnt_tmp;
         assign start_addr   = start_addr_tmp;
     end
   endgenerate

   
   // Address generator
   assign lpddr3_6gb_12gb_en  = |lpddr34_6gb_12gb_mask;

   assign addr_cnt_in_range= (addr_cnt <= max_addr_cnt && addr_cnt >= start_addr) ? 1'b1 : 1'b0;
   assign addr_in_range    = addr_cnt_in_range & ~iecc_hole;
   assign lpddr3_row13_14  = &(addr_cnt | (~lpddr34_6gb_12gb_mask)) & lpddr3_6gb_12gb_en;
//spyglass disable_block W486
//SMD: Rhs width '[RHS_Size]' with shift (Expr: '[RHSExpr]') is more than lhs width '[LHS_Size]'
//SJ: Overflow from shift is expected
   assign addr_row_shift_nxt = (send_scrub & lpddr3_row13_14) ? addr_row_shift<<1 :
                                                     (saq_wr) ? LPDDR3_ROW_SHIFT_BASE : addr_row_shift;
//spyglass enable_block W486
   assign sbr_accepted = ((reg_arb_scrub_cmd_type_port0==2'b01) | (reg_arb_scrub_cmd_type_port0==2'b10)) ? (sbr_awvalid & hif_awready): (sbr_arvalid & hif_arready);

   // Generate "done" signal after one full address range if operating during SW controlled LP mode
   always @(*) begin: arb_reg_scrub_done_COMB_PROC
      arb_reg_scrub_done_nxt = arb_reg_scrub_done;
      if (scrubber_dis | ~dis_tscrubi_cnt)  // only disabling the scrubber or setting the scrub interval
        arb_reg_scrub_done_nxt = 1'b0;                          // to a non-zero value will clear the status
      else if (sbr_accepted & ~saq_q_in_range)
        arb_reg_scrub_done_nxt = 1'b1;
   end

   assign sbr_done_intr = arb_reg_scrub_done;  // interrupt is the same as the register status

   // Prevent write sequence from looping when max address is reached.
   always @(*) begin: write_mode_done_COMB_PROC
      write_mode_done_nxt = write_mode_done;
      if (scrubber_dis)  // Restart write scrubber when disabled
        write_mode_done_nxt = 1'b0;              
      else if (~saq_d_in_range & (reg_arb_scrub_cmd_type_port0==2'b01) & (saq_wr)) // Write sequence is not looping
        write_mode_done_nxt = 1'b1;
   end

  generate if (MEMC_INLINE_ECC == 1) begin 
   assign saq_d         =  (corr_write_mode) ? corr_addr : addr_cnt;
   assign saq_wr        = send_scrub_en & send_scrub;
   assign saq_rd        = ((reg_arb_scrub_cmd_type_port0==2'b01) | (reg_arb_scrub_cmd_type_port0==2'b10)| read_corr_burst) ? hif_awready : hif_arready;
   assign send_scrub    = (burst_first) ? 1'b1 : (tscrubi_cntzero & scrub_skip_cntzero)^send_corr_burst;
  end 
  else begin
   assign saq_d         = addr_cnt;
   assign saq_wr        = send_scrub_en & send_scrub;
   //When both SAQ and RMW FIFO have a write; priority is being given to the
   //RMW FIFO. hence this should not be read out.
   assign saq_rd        = ((reg_arb_scrub_cmd_type_port0==2'b01) | (reg_arb_scrub_cmd_type_port0==2'b10))? (hif_awready & ~rmw_rd) : hif_arready; 
   assign send_scrub    = (burst_first) ? 1'b1 : (tscrubi_cntzero & scrub_skip_cntzero);
  end
endgenerate


   assign send_scrub_en = (scrubber_in_nm  | (scrubber_in_lp & reg_arb_scrub_during_lowpower)) & ~write_mode_done & ~saq_full & addr_cnt_valid;
   
   // When a sbr stop request is initiated, no more writes to saq is allowed.
   assign saq_wr_masked = saq_wr&~sbr_stop_req_latched;

   // Scrubber address queue
   // assumption: saq_empty is registered.
   DWC_ddr_umctl2_gfifo
   
     #(
       .WIDTH           (SAQW),
       .DEPTH           (SAQD),
       .ADDR_WIDTH      (SAQD_LG2),
       //spyglass disable_block SelfDeterminedExpr-ML
       //SMD: Self determined expression '(SAQD_LG2 + 1)' found in module 'DWC_ddr_umctl2_sbr'
       //SJ: This coding style is acceptable and there is no plan to change it
       .COUNT_WIDTH     (SAQD_LG2+1),
       //spyglass enable_block SelfDeterminedExpr-ML
       .OCCAP_EN        (OCCAP_EN),
       .OCCAP_PIPELINE_EN  (OCCAP_PIPELINE_EN)
     ) 
   saq (
        .clk             (clk),
        .rst_n           (rst_n),
        .wr              (saq_wr_masked),
        .d               (saq_d),
        .rd              (saq_rd),
        .par_en          (reg_ddrc_occap_en),
        .init_n          (1'b1),
        .ff              (saq_full),
        .wcount          (saq_wcount_unused),
        .q               (saq_q),
        .fe              (saq_empty),
        .par_err         (saq_par_err)
        `ifdef SNPS_ASSERT_ON
        `ifndef SYNTHESIS
        ,.disable_sva_fifo_checker_rd (1'b0)
        ,.disable_sva_fifo_checker_wr (1'b0)
        `endif // SYNTHESIS
        `endif // SNPS_ASSERT_ON
        );

   assign sbr_arqos        = {AXI_QOSW{1'b0}};
   assign sbr_arpagematch  = 1'b0;
   assign sbr_rexa_pyld    = {EXA_PYLD_W{1'b0}};

   assign sbr_awqos        = {AXI_QOSW{1'b0}};
   assign sbr_awpagematch  = 1'b0;
   assign sbr_awrmw        = read_corr_burst | (reg_arb_scrub_cmd_type_port0 == 2'b10);

   generate if (MEMC_INLINE_ECC == 1) begin
     assign sbr_arvalid      = (reg_arb_scrub_cmd_type_port0==2'b00) & ~saq_empty & ~read_corr_burst & ~tm_empty;
     assign sbr_araddr       = ((reg_arb_scrub_cmd_type_port0==2'b00) & ~read_corr_burst) ? saq_q : {SAQW{1'b0}};
     assign sbr_awaddr       = ((reg_arb_scrub_cmd_type_port0==2'b01) | (reg_arb_scrub_cmd_type_port0==2'b10) | read_corr_burst) ? saq_q : {SAQW{1'b0}};
     assign sbr_awvalid      = ((reg_arb_scrub_cmd_type_port0==2'b01) | (reg_arb_scrub_cmd_type_port0==2'b10) | read_corr_burst) & ~saq_empty;
   end
   else begin 
     //sbr_arvalid/sbr_awvalid should have no dependency on tm_empty here. tokens are not
     //used in this configuration. 
     //read_corr_burst - must generate correction RMW correctly. gen_rmw = 0 - only
     //periodic Read RMWs;
     assign sbr_arvalid      = (reg_arb_scrub_cmd_type_port0==2'b00) & ~saq_empty;
     assign sbr_araddr       = ((reg_arb_scrub_cmd_type_port0==2'b00)) ? saq_q : {SAQW{1'b0}};
    //if there is periodic RMW and Correction RMW together, then correction
    //RMW gets priority.
     assign sbr_awaddr       = (read_corr_burst) ? rmw_q[HIF_ADDR_WIDTH-1:0] : (((reg_arb_scrub_cmd_type_port0==2'b01) ||(reg_arb_scrub_cmd_type_port0==2'b10)) ? saq_q : {SAQW{1'b0}});
     assign sbr_awvalid      = ((((reg_arb_scrub_cmd_type_port0==2'b01) | (reg_arb_scrub_cmd_type_port0==2'b10)) & ~saq_empty) | read_corr_burst) ;
   end 
   endgenerate
  
   assign sbr_wdata_mask_full =                 read_corr_burst ? {NBEATS{1'b0}} : 
                                sbr_rxcmd_wlength == FULL_BURST ? sbr_wdata_mask_full_full :
                                sbr_rxcmd_wlength == HALF_BURST ? sbr_wdata_mask_full_half : sbr_wdata_mask_full_quarter;
 
   // Write data channel
   //
   generate
     if (FREQ_RATIO==1) begin: x2_burst_
       assign reg_ddrc_burst_rdwr_mod_bl = reg_ddrc_burst_rdwr_mod;
     end
     if (FREQ_RATIO==2) begin:X4_burst
       assign reg_ddrc_burst_rdwr_mod_bl = reg_ddrc_burst_rdwr_mod>>1;
     end 
     if (FREQ_RATIO==4) begin:X8_burst
       assign reg_ddrc_burst_rdwr_mod_bl = reg_ddrc_burst_rdwr_mod>>2;
     end
     if (OCPAR_EN==1) begin: OC_PAR_en
     
         wire [A_PARW-1:0] par_in_dummy = {A_PARW{1'b0}};
         wire [A_STRBW-1:0] sbr_parity_corr_unused;

         DWC_ddr_umctl2_ocpar_calc
         
         #(
            .DW      (A_DW),
            .CALC    (1),
            .PAR_DW  (A_PARW),
            .SL_W    (OCPAR_SL_DW)
         )
         U_sbr_wdata_par_gen
         (
            .data_in       (sbr_wdata),
            .parity_en     (1'b1),
            .parity_type   (reg_ddrc_oc_parity_type),
            .parity_in     (par_in_dummy),
            .mask_in       (sbr_wstrb),
            .parity_out    (sbr_wdatapar),
            .parity_corr   (sbr_parity_corr_unused) // not used
         );

     end
     else begin: OC_PAR_nen
         assign sbr_wdatapar = {A_PARW{1'b0}};
     end
   endgenerate
   generate 
     if (FREQ_RATIO==1&&MEMC_INLINE_ECC==1) begin: x2_wdata
       assign sbr_wdata = corr_write_mode ? {A_DW{1'b0}} : {m_wdata,m_wdata};
     end
     else if (FREQ_RATIO==1) begin: x2_wdata_sb
       assign sbr_wdata = (write_data_valid | (reg_arb_scrub_cmd_type_port0  == 2'b10)) ? {A_DW{1'b0}} : {m_wdata,m_wdata};
     end
     else if (FREQ_RATIO==2&&MEMC_INLINE_ECC==1) begin:X4_wdata
       assign sbr_wdata = corr_write_mode ? {A_DW{1'b0}} : {m_wdata,m_wdata,m_wdata,m_wdata};
     end 
     else if (FREQ_RATIO==2) begin:X4_wdata_sb
       assign sbr_wdata = (write_data_valid | (reg_arb_scrub_cmd_type_port0  == 2'b10)) ? {A_DW{1'b0}} : {m_wdata,m_wdata,m_wdata,m_wdata};
     end 
     else if (FREQ_RATIO==4&&MEMC_INLINE_ECC==1) begin:X8_wdata
       assign sbr_wdata = corr_write_mode ? {A_DW{1'b0}} : {m_wdata,m_wdata,m_wdata,m_wdata,m_wdata,m_wdata,m_wdata,m_wdata};
     end
     else if (FREQ_RATIO==4) begin:X8_wdata_sb
       assign sbr_wdata = (write_data_valid | (reg_arb_scrub_cmd_type_port0  == 2'b10)) ? {A_DW{1'b0}} : {m_wdata,m_wdata,m_wdata,m_wdata,m_wdata,m_wdata,m_wdata,m_wdata};
     end
   endgenerate 
   generate
     for(gv=0;gv<MIN_M_STRBW_4;gv=gv+1) begin:WDATA_PATTERN0 
       assign m_wdata[gv*8+:8] = reg_arb_scrub_pattern0[gv*8+:8];     
      
    end
  endgenerate


   generate if (MEMC_INLINE_ECC==1) begin
      assign sbr_wstrb      = corr_write_mode ? (
                                       ctl_hbw ? {2*FREQ_RATIO {{M_STRBW_HBW{1'b1}},{M_STRBW_HBW{1'b0}}}} : 
                                       ctl_qbw ? {2*FREQ_RATIO {{3*(M_STRBW_QBW){1'b1}},{M_STRBW_QBW{1'b0}}}} 
                                                : {A_STRBW{1'b0}} )
                                             : {A_STRBW{1'b1}};
      assign sbr_wvalid     = (reg_arb_scrub_cmd_type_port0==2'b01) | (reg_arb_scrub_cmd_type_port0==2'b10) | corr_write_mode;
   end 
   else begin
      assign sbr_wstrb      = (write_data_valid | (reg_arb_scrub_cmd_type_port0 == 2'b10)) ? (
                                       ctl_hbw ? {2*FREQ_RATIO {{M_STRBW_HBW{1'b1}},{M_STRBW_HBW{1'b0}}}} : 
                                       ctl_qbw ? {2*FREQ_RATIO {{3*(M_STRBW_QBW){1'b1}},{M_STRBW_QBW{1'b0}}}} 
                                                : {A_STRBW{1'b0}} )
                                             : {A_STRBW{1'b1}};
      assign sbr_wvalid     = (reg_arb_scrub_cmd_type_port0==2'b01) | (reg_arb_scrub_cmd_type_port0==2'b10) | write_data_valid;
      always @(posedge clk or negedge rst_n) begin
        if (~rst_n)
          write_data_valid <= 1'b0;
        else if (~rmw_fifo_empty)
          write_data_valid <= 1'b1;
        else if (~active_writes)
          write_data_valid <= 1'b0;
      end
   end
   endgenerate


  assign sbr_wlast      = 1'b1;
  assign sbr_wlast_pkt  = (beat_cnt== reg_ddrc_burst_rdwr_mod_m1) ? 1'b1:1'b0;

   assign reg_ddrc_burst_rdwr_mod_m1_nxt = reg_ddrc_burst_rdwr_mod_bl-1;

   assign beat_cnt_nxt = (sbr_wvalid & hif_wready & sbr_wlast_pkt) ? {BRDWR{1'b0}} :
                         (sbr_wvalid & hif_wready & ~sbr_wlast_pkt) ? beat_cnt + 1 : beat_cnt;
    
   // Read data channel
   // Note: Read data channel is not tracked or monitored (ECC error
   // logging is taken care by DDRC)


   // Port busy (outstanding transaction counter)
   assign outstanding_reads_incr = (sbr_arvalid & hif_arready) & ~(hif_rvalid_int[N_PORTS-1] & hif_rlast_pkt_int);
   assign outstanding_reads_decr = ~(sbr_arvalid & hif_arready) & (hif_rvalid_int[N_PORTS-1] & hif_rlast_pkt_int);

   assign outstanding_reads_nxt  = outstanding_reads_incr ? outstanding_reads + 1'b1 :
                                   outstanding_reads_decr ? outstanding_reads - 1'b1 : outstanding_reads;

   // Port busy (outstanding transaction counter)   
   assign outstanding_writes_incr = (sbr_awvalid & hif_awready) & ~(hif_wready & sbr_wvalid & sbr_wlast_pkt);
   assign outstanding_writes_decr = ~(sbr_awvalid & hif_awready) & (hif_wready & sbr_wvalid & sbr_wlast_pkt);

   assign outstanding_writes_nxt = outstanding_writes_incr ? outstanding_writes + 1'b1 :
                                   outstanding_writes_decr ? outstanding_writes - 1'b1 : outstanding_writes;
     
   assign active_reads  = |outstanding_reads;
   assign active_writes = |outstanding_writes;  

   assign arb_reg_scrub_busy_nxt = active_reads | active_writes
 | ~saq_empty | ~rmw_fifo_empty;

   assign cactive_out = active_reads | sbr_arvalid | active_writes | sbr_awvalid ;
  
   assign dis_sbr_ack_nxt  =  (~scrub_en_int)                  ? (scrubber_dis & dis_sbr_req) :
                              (scrubber_dis & dis_sbr_req)     ? 1'b1 :
                              (~scrubber_dis & ~dis_sbr_req)   ? 1'b0 : dis_sbr_ack;                           
   // parity register
   DWC_ddr_umctl2_par_reg
   
   #(
      .DW                   (SBR_VEC_WIDTH),
      .OCCAP                (OCCAP_EN),
      .OCCAP_PIPELINE_EN    (OCCAP_PIPELINE_EN),
      .REG_EN               (0),
      .SL_W                 (8),
      .RESVAL               (SBR_VEC_RESVAL))
   U_sbr_vec_r
   (  .clk        (clk),
      .rst_n      (rst_n),
      .data_in    (sbr_vec_i),
      .reg_set    (1'b0),
      .parity_en  (reg_ddrc_occap_en),
      .poison_en  (1'b0),
      .data_out   (sbr_vec_r),
      .parity_err (sbr_vec_parity_err));


   
  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      hif_rlast_pkt_int          <= 1'b0;
      hif_rvalid_int             <= {(N_PORTS){1'b0}};
      hif_resp_token_int         <= {(MEMC_TAGBITS){1'b0}};
      hif_corr_ecc_err_int       <= 1'b0;

    end
    else begin
      hif_rlast_pkt_int          <=     hif_rlast_pkt;
      hif_rvalid_int             <=     hif_rvalid;
      hif_resp_token_int         <=     hif_resp_token;

      hif_corr_ecc_err_int       <=     hif_corr_ecc_err;
    end
  end


 `ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS



   logic first_trans_cond; 
   assign first_trans_cond = burst_first_nxt & ~burst_first;
   
    //These scenario will only occur when IECC mode where scrub_burst_length_nm > 1 is allowed.
    //Only if burst_first_nxt is set will these assertions get triggered. 
    //Intention is to check in corner scenario during start of a burst if the ddrc state changes, no extra transactions are being generated.
    //burst_first_nxt is set only if the burst_size > 1; scrubber_in_lp, iecc_burst_en automatically imply that the burst_length>1

    //In SBECC and normal mode, only 1 transaction gets issued. No burst.
    //In SBECC and LP mode, burst gets issued but once the state changes, there is no burst again.   

 
    property p_burst_start_state_change_lp_nm;
       @(posedge clk) disable iff(!rst_n)
         (first_trans_cond & (st_sbr==ST_SBR_LP) & (st_sbr_nxt==ST_SBR_NM)); 
    endproperty
 
   //SNPS_XVP_DESC: coverpoint to ensure burst_change & state change occur together. 
    cp_burst_start_state_change_lp_nm : cover property (@(posedge clk) p_burst_start_state_change_lp_nm);

   //this scenario will only occur when IECC mode where scrub_burst_length_nm > 1 is allowed.
    property p_burst_start_state_change_lp_nm_timer;
    @(posedge clk) disable iff(!rst_n)
         (first_trans_cond & (st_sbr==ST_SBR_LP) & (st_sbr_nxt==ST_SBR_NM) & (tscrubi_cntzero && scrub_skip_cntzero)); 
    endproperty
 
   //SNPS_XVP_DESC: coverpoint to ensure burst_change , timer & state change occur together. 
    cp_burst_start_state_change_lp_nm_timer : cover property (@(posedge clk) p_burst_start_state_change_lp_nm_timer);


    property p_burst_start_state_change_nm_lp;
       @(posedge clk) disable iff(!rst_n)
         (first_trans_cond & (st_sbr==ST_SBR_NM) & (st_sbr_nxt==ST_SBR_LP)); 
    endproperty
 
   //SNPS_XVP_DESC: coverpoint to ensure burst_change & state change occur together. 
    cp_burst_start_state_change_nm_lp : cover property (@(posedge clk) p_burst_start_state_change_nm_lp);

    
    property p_burst_start_state_change_nm_lp_timer;
    @(posedge clk) disable iff(!rst_n)
         (first_trans_cond & (st_sbr==ST_SBR_NM) & (st_sbr_nxt==ST_SBR_LP) & (tscrubi_cntzero && scrub_skip_cntzero)); 
    endproperty
 
   //SNPS_XVP_DESC: coverpoint to ensure burst_change , timer & state change occur together. 
    cp_burst_start_state_change_nm_lp_timer : cover property (@(posedge clk) p_burst_start_state_change_nm_lp_timer);

   

     //Assertions if Valid Burst length values are programmed.
     //In Reads, Sideband ECC, Scrubber must be programmed with only 1.
     //In Reads, Inline ECC, scrubber can have only 8,16,32 
     //These need to be removed when the values are made common.
       property p_scrub_burst_length_nm_invalid_values_in_iecc;
       @(posedge clk) disable iff(!rst_n)
         (reg_arb_scrub_cmd_type_port0==2'b00 && iecc_burst_en && scrubber_in_nm) |-> (reg_arb_scrub_burst_length_nm_port0=={3'b001} || reg_arb_scrub_burst_length_nm_port0=={3'b010} || reg_arb_scrub_burst_length_nm_port0 == {3'b011}); 
       endproperty
       //SNPS_XVP_DESC: Check if scrub burst length normal is programmed to valid values In Inline ECC configurations 
       a_scrub_burst_length_nm_invalid_values_in_iecc : assert property (p_scrub_burst_length_nm_invalid_values_in_iecc) else 
       $display("-> %0t ERROR: SBR - Scrub_burst_length_normal is programmed to invalid Values In Inline ECC", $realtime);
     
       property p_scrub_burst_length_lp_invalid_values_in_iecc;
       @(posedge clk) disable iff(!rst_n)
         (reg_arb_scrub_cmd_type_port0==2'b00 && iecc_burst_en && scrubber_in_lp) |-> (reg_arb_scrub_burst_length_lp_port0=={3'b001} || reg_arb_scrub_burst_length_lp_port0=={3'b010} || reg_arb_scrub_burst_length_lp_port0=={3'b011}); 
       endproperty
       //SNPS_XVP_DESC: Check if scrub burst length lp is programmed to valid values In Inline ECC configurations 
       a_scrub_burst_length_lp_invalid_values_in_iecc : assert property (p_scrub_burst_length_lp_invalid_values_in_iecc) else 
       $display("-> %0t ERROR: SBR - Scrub_burst_length_lp is programmed to invalid Values In Inline ECC", $realtime);
  
   // Outstanding reads counter overflow during increment
   property p_outstanding_reads_overflow;
     @(posedge clk) disable iff(!rst_n) 
       (outstanding_reads_incr) |-> (outstanding_reads<2**OUTS_RDW-1);
   endproperty  
   //SNPS_XVP_DESC: Check if outstanding read counter is overflowing 
   a_outstanding_reads_overflow : assert property (p_outstanding_reads_overflow) else 
     $display("-> %0t ERROR: SBR outstanding reads counter overflow!!!", $realtime);
   
   
   // Outstanding reads counter underflow during decrement
   property p_outstanding_reads_underflow;
      @(posedge clk) disable iff(!rst_n) 
      (outstanding_reads_decr) |-> (outstanding_reads>0);
   endproperty  

   //SNPS_XVP_DESC: Check if outstanding read counter is underflowing 
  a_outstanding_reads_underflow : assert property (p_outstanding_reads_underflow) else 
    $display("-> %0t ERROR: SBR outstanding reads counter underflow !!!", $realtime);   

   // Outstanding writes counter overflow during increment
   property p_outstanding_writes_overflow;
     @(posedge clk) disable iff(!rst_n) 
       (outstanding_writes_incr) |-> (outstanding_writes<2**OUTS_WRW-1);
   endproperty  
   //SNPS_XVP_DESC: Check if outstanding write counter is overflowing 
   a_outstanding_writes_overflow : assert property (p_outstanding_writes_overflow) else 
     $display("-> %0t ERROR: SBR outstanding writes counter overflow!!!", $realtime);
   
   
   // Outstanding writes counter underflow during decrement
   property p_outstanding_writes_underflow;
      @(posedge clk) disable iff(!rst_n) 
      (outstanding_writes_decr) |-> (outstanding_writes>0);
   endproperty  

   //SNPS_XVP_DESC: Check if outstanding read counter is underflowing 
  a_outstanding_writes_underflow : assert property (p_outstanding_writes_underflow) else 
    $display("-> %0t ERROR: SBR outstanding writes counter underflow !!!", $realtime);   


   property p_start_end_mask;
   @(posedge clk) disable iff(!rst_n) 
       (sbr_address_start_int!=0 && reg_arb_scrub_en==1) |-> (sbr_address_start_int < sbr_address_range_int);
   endproperty

   //SNPS_XVP_DESC: Check to ensure start address is always less than end address. 
   a_sbr_start_end_address : assert property (p_start_end_mask) else
      $display("-> %0t ERROR: Start address mask must be set less than the maximum range 'h%0h",$realtime,sbr_address_range_int);

   property p_ctl_nm;
   @(posedge clk) disable iff(!rst_n) 
       (ctl_nm);
   endproperty

   //SNPS_XVP_DESC: coverpoint to ensure normal mode is covered. 
   cp_ctl_nm : cover property (@(posedge clk) p_ctl_nm);

   property p_ctl_pd;
   @(posedge clk) disable iff(!rst_n) 
       (ctl_pd);
   endproperty

   //SNPS_XVP_DESC: coverpoint to ensure pd mode is covered. 
   cp_ctl_pd : cover property (@(posedge clk) p_ctl_pd);

   property p_ctl_lp;
   @(posedge clk) disable iff(!rst_n) 
       (ctl_lp);
   endproperty

   //SNPS_XVP_DESC: coverpoint to ensure lp mode is covered. 
   cp_ctl_lp : cover property (@(posedge clk) p_ctl_lp);

   property p_ctl_sr_auto;
   @(posedge clk) disable iff(!rst_n) 
       (ctl_sr & sr_auto);
   endproperty

   //SNPS_XVP_DESC: coverpoint to ensure auto self refresh mode is covered. 
   cp_ctl_sr_auto : cover property (@(posedge clk) p_ctl_sr_auto);

   property p_ctl_sr_no_sw;
   @(posedge clk) disable iff(!rst_n) 
       (ctl_sr & sr_all & ~reg_ddrc_selfref_sw);
   endproperty

   //SNPS_XVP_DESC: coverpoint to ensure HW self refresh mode is covered. 
   cp_ctl_sr_no_sw : cover property (@(posedge clk) p_ctl_sr_no_sw);

   property p_ctl_sr_sw;
   @(posedge clk) disable iff(!rst_n) 
       (ctl_sr & sr_all & reg_ddrc_selfref_sw);
   endproperty

   //SNPS_XVP_DESC: coverpoint to ensure SW self refresh mode is covered. 
   cp_ctl_sr_sw : cover property (@(posedge clk) p_ctl_sr_sw);

 property p_ctl_burst_cnt_zero_addr_end;
  @(posedge clk) disable iff(!rst_n)
       (scrub_burst_cntzero && ~saq_full && (scrub_burst_decoded>1) && ~addr_cnt_valid);
  endproperty
  
  //SNPS_XVP_DESC: coverpoint to ensure last transaction of burst will have an
  //invalid address.
  cov_p_ctl_burst_cnt_zero_addr_end : cover property (@(posedge clk) p_ctl_burst_cnt_zero_addr_end);



   reg dis_sbr_req_d, dis_sbr_ack_d;
   wire dis_sbr_req_pe, dis_sbr_req_ne;
   wire dis_sbr_ack_pe, dis_sbr_ack_ne;

   always @(posedge clk, negedge rst_n) begin
      if(!rst_n) begin
         dis_sbr_req_d <= 1'b0;
         dis_sbr_ack_d <= 1'b0;
      end
      else begin
         dis_sbr_req_d <= dis_sbr_req;
         dis_sbr_ack_d <= dis_sbr_ack;
      end
    end

   assign dis_sbr_req_pe = dis_sbr_req & ~dis_sbr_req_d;
   assign dis_sbr_req_ne = ~dis_sbr_req & dis_sbr_req_d;
   assign dis_sbr_ack_pe = dis_sbr_ack & ~dis_sbr_ack_d;
   assign dis_sbr_ack_ne = ~dis_sbr_ack & dis_sbr_ack_d;

   property p_sbr_ack_assert_timing_hwffc;
   @(posedge clk) disable iff(!rst_n) 
       dis_sbr_req_pe |-> ##[1:2] dis_sbr_ack_pe;
   endproperty
  
   //SNPS_XVP_DESC: check to ensure SBR enabled dis_sbr_ack when dis_sbr_req is asserted.
  a_sbr_ack_assert_timing_hwffc : assert property (p_sbr_ack_assert_timing_hwffc) else
     $display("-> %0t ERROR : SBR enabled when dis_sbr_req asserted", $realtime); 

   property p_sbr_ack_deassert_timing_hwffc;
   @(posedge clk) disable iff(!rst_n) 
       dis_sbr_req_ne |-> ##[1:2] dis_sbr_ack_ne;
   endproperty
  
   //SNPS_XVP_DESC: check to ensure SBR de-asserted dis_sbr_ack when dis_sbr_req is asserted.
  a_sbr_ack_deassert_timing_hwffc : assert property (p_sbr_ack_deassert_timing_hwffc) else
     $display("-> %0t ERROR : SBR failed to deassert dis_sbr_ack", $realtime); 

  
  // Assertion added to check overflow
  localparam CATEGORY = 5; // Allows groups of assertions to be enabled/disabled at the same time

  //SNPS_XVP_DESC: check to ensure addr_cnt_nxt_overflow doesn't occur. 
  assert_never #(0, 0, "addr_cnt_next overflow", CATEGORY) a_addr_cnt_next_overflow
    (clk, rst_n, (addr_cnt_next_wider[HIF_ADDR_WIDTH]==1'b1));




  `endif // SYNTHESIS
 `endif // SNPS_ASSERT_ON


endmodule // DWC_ddr_umctl2_sbr
