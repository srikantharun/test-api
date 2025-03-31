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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_core_in_if.sv#4 $
// -------------------------------------------------------------------------
// Description:
//
// This is the input interface module of IH. The signals from the DDRC are flopped
// in this module. The flopped input signals get stored in a 2-deep input fifo. 
// The full from this fifo is used to generate the stall signal in ih_core_out_if.v 
// module. There are 3 flavors of the input fifo based on the timing requirement.
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module ih_core_in_if(
  co_ih_clk,
  core_ddrc_rstn,
  hif_cmd_valid,
  hif_cmd_type,
  hif_cmd_addr,
  hif_cmd_token,
  hif_cmd_pri,
  hif_cmd_length,
  hif_cmd_wdata_ptr,
  hif_cmd_autopre,
  hif_cmd_latency,
  input_fifo_full,
  input_fifo_empty,
  ih_in_busy,
  ih_fifo_wr_empty,
  ih_fifo_rd_empty,
  input_fifo_din_ie,
  input_fifo_dout_ie,
  mapped_addr_eccap,
  rxcmd_addr_eccap,
  hif_cmd_stall,
  te_ih_retry,
  wu_ih_flow_cntrl_req,
  reg_ddrc_ecc_type,
  rxcmd_valid,
  rxcmd_addr,
  rxcmd_addr_dup,
  rxcmd_type,
  rxcmd_token,

  rxcmd_pri,
  rxcmd_rd_latency,
  ih_gs_any_vpr_timed_out,
  rxcmd_wr_latency,
  ih_gs_any_vpw_timed_out,
  rxcmd_length,
  rxcmd_autopre,
  rxcmd_wdata_ptr
);


//------------------------------ PARAMETERS ------------------------------------
parameter  ECCAP_DATA_BITS   = (`MEMC_ECCAP_EN & `MEMC_OPT_TIMING_EN)? 1 : 0;
parameter  IE_FIFO_DATA_BITS = `MEMC_INLINE_ECC_EN ? 10 : 0;


parameter  WRCMD_ENTRY_BITS= `MEMC_WRCMD_ENTRY_BITS;  // bits to address all entries in write CAM
parameter  CORE_ADDR_WIDTH = 35;                      // any change may necessitate a change to address map in IC
parameter  IH_TAG_WIDTH    = `MEMC_TAGBITS;           // width of token/tag field from core
parameter  CMD_LEN_BITS    = 1;                       // bits for command length, when used
                                                           //  (partial write, scrub, or none)
parameter  WDATA_PTR_BITS  = `MEMC_WDATA_PTR_BITS;

parameter  REFRESH_EN_BITS = `MEMC_NUM_RANKS;

parameter  CMD_TYPE_BITS   = 2;                       // any change will require RTL modifications in IC
localparam WRDATA_ENTRY_BITS= WRCMD_ENTRY_BITS + 1;   // write data RAM entries
                                                           // (only support 2 datas per command at the moment)

parameter  RD_LATENCY_BITS = `UMCTL2_XPI_RQOS_TW;
parameter  WR_LATENCY_BITS = `UMCTL2_XPI_WQOS_TW;
parameter       WDATA_MASK_FULL_BITS = `MEMC_WRDATA_CYCLES;
parameter       HIF_KEYID_WIDTH      = 0;
parameter       IME_WR_TWEAK_BITS = 0;

// 2-bit command type encodings
localparam CMD_TYPE_BLK_WR   = `MEMC_CMD_TYPE_BLK_WR;
localparam CMD_TYPE_BLK_RD   = `MEMC_CMD_TYPE_BLK_RD;
localparam CMD_TYPE_RMW      = `MEMC_CMD_TYPE_RMW;
localparam CMD_TYPE_RESERVED = `MEMC_CMD_TYPE_RESERVED;

// 2-bit read priority encoding
localparam CMD_PRI_LPR       = `MEMC_CMD_PRI_LPR;
localparam CMD_PRI_VPR       = `MEMC_CMD_PRI_VPR;
localparam CMD_PRI_HPR       = `MEMC_CMD_PRI_HPR;
localparam CMD_PRI_XVPR      = `MEMC_CMD_PRI_XVPR;

// 2-bit write priority encoding
localparam CMD_PRI_NPW       = `MEMC_CMD_PRI_NPW;
localparam CMD_PRI_VPW       = `MEMC_CMD_PRI_VPW;
localparam CMD_PRI_RSVD      = `MEMC_CMD_PRI_RSVD;
localparam CMD_PRI_XVPW      = `MEMC_CMD_PRI_XVPW;


//------------------------------ PARAMETERS ------------------------------------


input                           co_ih_clk;              // clock
input                           core_ddrc_rstn;         // reset

input                           hif_cmd_valid;          // valid command
input   [CMD_TYPE_BITS-1:0]     hif_cmd_type;           // command type:
                                                        //  00 - block write
                                                        //  01 - read
                                                        //  10 - rmw
                                                        //  11 - reserved
input   [CORE_ADDR_WIDTH-1:0]   hif_cmd_addr;           // address
input   [IH_TAG_WIDTH-1:0]      hif_cmd_token;          // read token returned w/ read data
input   [1:0]                   hif_cmd_pri;            // priority:
                                                        //  00 - low priority, 01 - VPR
                                                        //  10 - high priority, 11 - unused
                                                        // For writes: 00 - NPW, 01 - VPW, 10, 11 - reserved
input   [CMD_LEN_BITS-1:0]      hif_cmd_length;         // length (1 word or 2)
                                                        //  1 - 1 word
                                                        //  0 - 2 words
input   [WDATA_PTR_BITS-1:0]    hif_cmd_wdata_ptr;      // 
input                           hif_cmd_autopre;        // auto precharge enable
input   [RD_LATENCY_BITS-1:0]   hif_cmd_latency;
output                          input_fifo_full;        // indication that input fifo is full - used to generate stall
output                          input_fifo_empty;       // indication that input fifo is empty
output                          ih_in_busy;             // stays high when any cmd comes into the controller and the FIFOs are non-empty
                                                        // combinational signal generated from the input cmd valid signal (hif_cmd_valid)
input  [IE_FIFO_DATA_BITS-1:0]  input_fifo_din_ie;
output [IE_FIFO_DATA_BITS-1:0]  input_fifo_dout_ie;

input                           mapped_addr_eccap;
output                          rxcmd_addr_eccap;

input                           hif_cmd_stall;          // Stall from IH to Core


input                           te_ih_retry;
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in !MEMC_IH_TE_PIPELINE configs only, but input should always exist
input                           wu_ih_flow_cntrl_req;   // indication that wu_wdata_if fifo is full
                                                        // all the commands in the fifo are waiting for data_valid
input                           reg_ddrc_ecc_type; 
//spyglass enable_block W240

output                          rxcmd_valid;

output  [CORE_ADDR_WIDTH-1:0]   rxcmd_addr;
output  [CMD_TYPE_BITS-1:0]     rxcmd_type;
output  [IH_TAG_WIDTH-1:0]      rxcmd_token;
output  [1:0]                   rxcmd_pri;
output                          rxcmd_autopre;
output  [CMD_LEN_BITS-1:0]      rxcmd_length;
output  [WDATA_PTR_BITS-1:0]    rxcmd_wdata_ptr;
output  [RD_LATENCY_BITS-1:0]   rxcmd_rd_latency;
output                          ih_gs_any_vpr_timed_out;
output  [WR_LATENCY_BITS-1:0]   rxcmd_wr_latency;
output                          ih_gs_any_vpw_timed_out;
output  [CORE_ADDR_WIDTH-1:0]   rxcmd_addr_dup;

output                          ih_fifo_wr_empty;
output                          ih_fifo_rd_empty;



wire                            ih_fifo_wr_empty;
wire                            ih_fifo_rd_empty;

localparam  LUT_VALID_FIELD_BITS = 0;

localparam  AUTOPRE_FIELD               = 0;
localparam  ADDR_FIELD_LSB              = 1;
localparam  ADDR_FIELD_MSB              = ADDR_FIELD_LSB            + CORE_ADDR_WIDTH      - 1;
localparam  TYPE_FIELD_LSB              = ADDR_FIELD_MSB            + 1;
localparam  TYPE_FIELD_MSB              = TYPE_FIELD_LSB            + CMD_TYPE_BITS        - 1;
localparam  TOKEN_FIELD_LSB             = TYPE_FIELD_MSB            + 1;
localparam  TOKEN_FIELD_MSB             = TOKEN_FIELD_LSB           + IH_TAG_WIDTH         - 1;
localparam  PRI_FIELD_LSB               = TOKEN_FIELD_MSB           + 1;
localparam  PRI_FIELD_MSB               = PRI_FIELD_LSB             + 2                    - 1; // 2-bit priority field
localparam  LEN_FIELD_LSB               = PRI_FIELD_MSB             + 1;
localparam  LEN_FIELD_MSB               = LEN_FIELD_LSB             + CMD_LEN_BITS         - 1;
localparam  WDATA_PTR_FIELD_LSB         = LEN_FIELD_MSB             + 1;
localparam  WDATA_PTR_FIELD_MSB         = WDATA_PTR_FIELD_LSB       + WDATA_PTR_BITS       - 1;
localparam  ECCAP_FIELD_LSB             = WDATA_PTR_FIELD_MSB       + 1;
localparam  ECCAP_FIELD_MSB             = ECCAP_FIELD_LSB           + ECCAP_DATA_BITS      - 1;
localparam  IE_FIELD_LSB                = ECCAP_FIELD_MSB           + 1;
localparam  IE_FIELD_MSB                = IE_FIELD_LSB              + IE_FIFO_DATA_BITS    - 1;
localparam  REFRESH_EN_FIELD_LSB        = IE_FIELD_MSB              + 1;
localparam  REFRESH_EN_FIELD_MSB        = REFRESH_EN_FIELD_LSB      + REFRESH_EN_BITS      - 1;
localparam  WDATA_MASK_FULL_FIELD_LSB   = REFRESH_EN_FIELD_MSB      + 1;
localparam  WDATA_MASK_FULL_FIELD_MSB   = WDATA_MASK_FULL_FIELD_LSB + WDATA_MASK_FULL_BITS - 1;
localparam  LUT_VALID_LSB               = WDATA_MASK_FULL_FIELD_MSB + 1;
localparam  LUT_VALID_MSB               = LUT_VALID_LSB             + LUT_VALID_FIELD_BITS - 1;
localparam  TWEAK_INDEX_LSB             = LUT_VALID_MSB             + 1;
localparam  TWEAK_INDEX_MSB             = TWEAK_INDEX_LSB           + IME_WR_TWEAK_BITS    - 1;
localparam  KEYID_FIELD_LSB             = TWEAK_INDEX_MSB           + 1;
localparam  KEYID_FIELD_MSB             = KEYID_FIELD_LSB           + HIF_KEYID_WIDTH      - 1;

localparam  INPUT_FIFO_WIDTH            = KEYID_FIELD_MSB + 1;



wire                          input_fifo_put;
wire                          input_fifo_get;
wire  [INPUT_FIFO_WIDTH-1:0]  input_fifo_din;
wire  [INPUT_FIFO_WIDTH-1:0]  input_fifo_dout;

wire  [CORE_ADDR_WIDTH:0]     input_fifo_dup_dout;

wire                          ih_in_busy;

wire                          input_fifo_full;
wire                          input_fifo_empty;

wire                          rxcmd_valid;

wire  [CORE_ADDR_WIDTH-1:0]   rxcmd_addr;
wire  [CMD_TYPE_BITS-1:0]     rxcmd_type;
wire  [IH_TAG_WIDTH-1:0]      rxcmd_token;
wire  [1:0]                   rxcmd_pri;
wire                          rxcmd_autopre;
wire  [CMD_LEN_BITS-1:0]      rxcmd_length;
wire  [WDATA_PTR_BITS-1:0]    rxcmd_wdata_ptr;
wire  [RD_LATENCY_BITS-1:0]   rxcmd_rd_latency;

wire  [CORE_ADDR_WIDTH-1:0]   rxcmd_addr_dup;

wire                          i_hif_cmd_valid;

// IH Input module is busy when there is an input command or when the Input FIFO is not empty
assign  i_hif_cmd_valid = hif_cmd_valid && (~hif_cmd_stall);
assign  ih_in_busy      = i_hif_cmd_valid || (~input_fifo_empty);

assign  input_fifo_put  = i_hif_cmd_valid;
//if MEMC_IH_TE_PIPELINE enabled, wu_ih_flow_cntrl_req will be used to stall command at output of ih_te_pipeline for IE case instead
// unused here in IE case
assign  input_fifo_get  = (!te_ih_retry) 
                                         ;

//spyglass disable_block W164b
//SMD: LHS: 'xxx' width mm is greater than RHS: 'yyy' width nn in assignment
//SJ: Functionally identical with padding MSB with 0
assign  input_fifo_din  = {
                             input_fifo_din_ie,
                             mapped_addr_eccap,
                            hif_cmd_wdata_ptr,hif_cmd_length,hif_cmd_pri,
                            hif_cmd_token,hif_cmd_type,hif_cmd_addr,hif_cmd_autopre};
//spyglass enable_block W164b

//if MEMC_IH_TE_PIPELINE enabled, wu_ih_flow_cntrl_req will be used to stall command at output of ih_te_pipeline for IE case instead
// unused here in IE case
assign  rxcmd_valid = (!input_fifo_empty) 
                                         ;

assign  rxcmd_addr  = input_fifo_dout[ADDR_FIELD_MSB:ADDR_FIELD_LSB];
assign  rxcmd_type  = input_fifo_dout[TYPE_FIELD_MSB:TYPE_FIELD_LSB];
assign  rxcmd_token = input_fifo_dout[TOKEN_FIELD_MSB:TOKEN_FIELD_LSB];
assign  rxcmd_pri   = input_fifo_dout[PRI_FIELD_MSB:PRI_FIELD_LSB];
assign  rxcmd_length    = input_fifo_dout[LEN_FIELD_MSB:LEN_FIELD_LSB];
assign  rxcmd_wdata_ptr = input_fifo_dout[WDATA_PTR_FIELD_MSB:WDATA_PTR_FIELD_LSB];
assign  rxcmd_autopre   = input_fifo_dout[AUTOPRE_FIELD];
assign  input_fifo_dout_ie = input_fifo_dout[IE_FIELD_MSB:IE_FIELD_LSB];
assign  rxcmd_addr_eccap = input_fifo_dout[ECCAP_FIELD_MSB:ECCAP_FIELD_LSB];

assign  rxcmd_addr_dup  = input_fifo_dup_dout[ADDR_FIELD_MSB:ADDR_FIELD_LSB];


//-----------------------------------------
// Logic for generating the separate Write and Read FIFO empty signals
//-----------------------------------------

// The width of 2-bits has an assumption that the input FIFO will always be 2-deep
reg [1:0] wr_in_fifo, rd_in_fifo;
wire      fifo_get, fifo_put;
wire      wr_put, wr_get;
wire      rd_put, rd_get;

assign fifo_put = input_fifo_put && (~input_fifo_full);
assign fifo_get = input_fifo_get && (~input_fifo_empty);

assign    wr_put = fifo_put && ((hif_cmd_type == CMD_TYPE_BLK_WR) || (hif_cmd_type == CMD_TYPE_RMW));
assign    wr_get = fifo_get && ((rxcmd_type == CMD_TYPE_BLK_WR)       || (rxcmd_type == CMD_TYPE_RMW));

assign    rd_put = fifo_put && ((hif_cmd_type == CMD_TYPE_BLK_RD) || (hif_cmd_type == CMD_TYPE_RMW));
assign    rd_get = fifo_get && ((rxcmd_type == CMD_TYPE_BLK_RD)       || (rxcmd_type == CMD_TYPE_RMW));

// generation of signals that indicate that there is a read or write 
// command in the input FIFO
always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
       wr_in_fifo <= 2'b00;
       rd_in_fifo <= 2'b00;
   end
   else begin

  //ccx_line_begin:ih_core_in_if_rd; This module is instantiated for read, hence the logic for write should be excluded.
  // generating wr_in_fifo - Increment when WR or RMW command comes in
  // Decrement when WR or RMW command goes out
      if(wr_put & (~wr_get))
             wr_in_fifo <= wr_in_fifo + 2'b01;
      else if(wr_get & (~wr_put))
             wr_in_fifo <= wr_in_fifo - 2'b01;
  //ccx_line_end

  //ccx_line_begin:ih_core_in_if_wr; This module is instantiated for write, hence the logic for read should be excluded.
  // generating rd_in_fifo - Increment when RD or RMW command comes in
  // Decrement when RD or RMW command goes out
      if(rd_put & (~rd_get))
             rd_in_fifo <= rd_in_fifo + 2'b01;
      else if(rd_get & (~rd_put))
             rd_in_fifo <= rd_in_fifo - 2'b01;
  //ccx_line_end

   end
end

assign ih_fifo_wr_empty = (wr_in_fifo == 2'b00);
assign ih_fifo_rd_empty = (rd_in_fifo == 2'b00);



//--------------------------------------
// There are 2 versions of input fifo used here
// If MEMC_OPT_TIMING is defined - then *flopout* version with repeated flop is used
// If it is not defined, then sync_fifo_rst is used
//--------------------------------------

// 2-deep input FIFO
ingot_sync_fifo_flopout_rst_rep #( // this version improves internal timing within the controller
                                    // this has a higher gate count, but no latency penalty
                                    // this version also has some of the flops replicated
  .WIDTH                (INPUT_FIFO_WIDTH),
  //spyglass disable_block SelfDeterminedExpr-ML
  //SMD: Self determined expression '(CORE_ADDR_WIDTH + 1)' found in module 'ih_core_in_if'
  //SJ: This coding style is acceptable and there is no plan to change it.
  .FLOP_REPLICATE_WIDTH (CORE_ADDR_WIDTH + 1), // this parameter determines how many LSB bits of dout flop
                                               // gets replicated
  //spyglass enable_block SelfDeterminedExpr-ML
  .DEPTH_LOG2 (1))
    
    ih_input_fifo (
        .clk    (co_ih_clk),
        .rstb   (core_ddrc_rstn),
        .put    (input_fifo_put),
        .din    (input_fifo_din),
        .get    (input_fifo_get),
        .dout   (input_fifo_dout),
        .dup_dout  (input_fifo_dup_dout),
        .full   (input_fifo_full),
        .empty  (input_fifo_empty)   );


//-----------------------------------------------------
// Logic for storing and decrementing the rd_latency value for VPR commands
// Assumption in the logic below that the Input FIFO depth is 2
//-----------------------------------------------------


  //ccx_line_begin:ih_core_in_if_wr; This module is instantiated for write, hence the logic for read should be excluded.

reg                       fifo_wptr, fifo_rptr;
reg [RD_LATENCY_BITS-1:0] rd_latency_0, rd_latency_1;
wire[RD_LATENCY_BITS-1:0] init_load_rd_latency_value;
wire                      load_vpr_0, load_vpr_1;
wire                      reset_vpr_0, reset_vpr_1;
reg                       ih_gs_any_vpr_timed_out;
wire                      any_vpr_timed_out;
reg                       valid_vpr_0, valid_vpr_1;

always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
     fifo_wptr <= 1'b0;
     fifo_rptr <= 1'b0;
   end
   else begin
     if(fifo_put) fifo_wptr <= ~fifo_wptr;
     if(fifo_get) fifo_rptr <= ~fifo_rptr;
   end
end

assign load_vpr_0 = fifo_put && (fifo_wptr == 1'b0) && (((hif_cmd_type == CMD_TYPE_BLK_RD) && (hif_cmd_pri == CMD_PRI_VPR)) ||
                                                        ((hif_cmd_type == CMD_TYPE_RMW   ) && (hif_cmd_pri == CMD_PRI_VPW))   ) ;

assign load_vpr_1 = fifo_put && (fifo_wptr == 1'b1) && (((hif_cmd_type == CMD_TYPE_BLK_RD) && (hif_cmd_pri == CMD_PRI_VPR)) ||
                                                        ((hif_cmd_type == CMD_TYPE_RMW   ) && (hif_cmd_pri == CMD_PRI_VPW))   ) ;

assign reset_vpr_0 = fifo_get && (fifo_rptr == 1'b0) && (((rxcmd_type == CMD_TYPE_BLK_RD) && (rxcmd_pri == CMD_PRI_VPR)) ||
                                                         ((rxcmd_type == CMD_TYPE_RMW   ) && (rxcmd_pri == CMD_PRI_VPW))   ) ;

assign reset_vpr_1 = fifo_get && (fifo_rptr == 1'b1) && (((rxcmd_type == CMD_TYPE_BLK_RD) && (rxcmd_pri == CMD_PRI_VPR)) ||
                                                         ((rxcmd_type == CMD_TYPE_RMW   ) && (rxcmd_pri == CMD_PRI_VPW))   ) ;


// generating the intial loading value
// if the value is 0 coming in, then keep it as is
// else decrement by 1 and then store in the flop
assign init_load_rd_latency_value = (hif_cmd_latency != {RD_LATENCY_BITS{1'b0}}) ? 
                                         hif_cmd_latency - {{(RD_LATENCY_BITS-1){1'b0}},1'b1} : {RD_LATENCY_BITS{1'b0}};

// read latency counters for both the entries in the input FIFO
always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      rd_latency_0    <= {RD_LATENCY_BITS{1'b1}}; // reset to all 1's as all 0's is the timeout condition
      rd_latency_1    <= {RD_LATENCY_BITS{1'b1}};
      valid_vpr_0     <= 1'b0;
      valid_vpr_1     <= 1'b0;
      ih_gs_any_vpr_timed_out <= 1'b0;
   end
   else begin

      ih_gs_any_vpr_timed_out <= any_vpr_timed_out;

      // If valid write into FIFO && cmd is RD && priority is VPR, then load the unput rd_latency into the 
      // apprpriate register based on fifo_wptr. Keep decrementing the timer every cycle as long as the values is not 0.

      if(load_vpr_0)
         rd_latency_0 <= init_load_rd_latency_value;
      else if(reset_vpr_0)
         rd_latency_0 <= {RD_LATENCY_BITS{1'b1}};
      else if(valid_vpr_0 & (rd_latency_0 != {RD_LATENCY_BITS{1'b0}}))
         rd_latency_0 <= rd_latency_0 - {{(RD_LATENCY_BITS-1){1'b0}},1'b1};

      if(load_vpr_1)
         rd_latency_1 <= init_load_rd_latency_value;
      else if(reset_vpr_1)
         rd_latency_1 <= {RD_LATENCY_BITS{1'b1}};
      else if(valid_vpr_1 & (rd_latency_1 != {RD_LATENCY_BITS{1'b0}}))
         rd_latency_1 <= rd_latency_1 - {{(RD_LATENCY_BITS-1){1'b0}},1'b1};

      if(load_vpr_0)
         valid_vpr_0     <= 1'b1;
      else if(reset_vpr_0)
         valid_vpr_0     <= 1'b0;

      if(load_vpr_1)
         valid_vpr_1     <= 1'b1;
      else if(reset_vpr_1)
         valid_vpr_1     <= 1'b0;


   end
end

//--------------------------
// Generating the timeout signal in IH
// - Either of the VPR latency counters are at 0 AND
// - there is a Write Command in IH FIFO and the Collision indication (te_ih_retry) is high
//
// If Controller is handling a collision case and if it is due to write command, 
// then the vpr_timed_out signal should not be asserted. Otherwise it will cause lock-up condition
// in DDRC where the DDRC would try to flush the write command by going to Write mode, but that is
// prevented by the forceful Read mode due to expired-VPR signal from IH
//
// The consequence of doing this is that, if a command expires while in IH, then indication won't
// go to GS module, until the write collision is cleared.
//--------------------------
assign any_vpr_timed_out = (~(|(rd_latency_0)) || (~(|(rd_latency_1)))) && (~te_ih_retry);

// Output the correct latency value based on fifo_rptr
assign rxcmd_rd_latency = (fifo_rptr == 1'b1) ? rd_latency_1 : rd_latency_0;

  //ccx_line_end




//-----------------------------------------------------
// Logic for storing and decrementing the rd_latency value for VPW commands
// Assumption in the logic below that the Input FIFO depth is 2
//-----------------------------------------------------

  //ccx_line_begin:ih_core_in_if_rd; This module is instantiated for read, hence the logic for write should be excluded.

reg                       fifo_vpw_wptr, fifo_vpw_rptr;
reg [WR_LATENCY_BITS-1:0] wr_latency_0, wr_latency_1;
wire[WR_LATENCY_BITS-1:0] init_load_wr_latency_value;
wire                      load_vpw_0, load_vpw_1;
wire                      reset_vpw_0, reset_vpw_1;
reg                       ih_gs_any_vpw_timed_out;
wire                      any_vpw_timed_out;
reg                       valid_vpw_0, valid_vpw_1;

always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
     fifo_vpw_wptr <= 1'b0;
     fifo_vpw_rptr <= 1'b0;
   end
   else begin
     if(fifo_put) fifo_vpw_wptr <= ~fifo_vpw_wptr;
     if(fifo_get) fifo_vpw_rptr <= ~fifo_vpw_rptr;
   end
end

assign load_vpw_0 = fifo_put && (fifo_vpw_wptr == 1'b0) && ((hif_cmd_type == CMD_TYPE_BLK_WR) || (hif_cmd_type == CMD_TYPE_RMW)) && (hif_cmd_pri == CMD_PRI_VPW);
assign load_vpw_1 = fifo_put && (fifo_vpw_wptr == 1'b1) && ((hif_cmd_type == CMD_TYPE_BLK_WR) || (hif_cmd_type == CMD_TYPE_RMW)) && (hif_cmd_pri == CMD_PRI_VPW);

assign reset_vpw_0 = fifo_get && (fifo_vpw_rptr == 1'b0) && ((rxcmd_type == CMD_TYPE_BLK_WR) || (rxcmd_type == CMD_TYPE_RMW)) && (rxcmd_pri == CMD_PRI_VPW);
assign reset_vpw_1 = fifo_get && (fifo_vpw_rptr == 1'b1) && ((rxcmd_type == CMD_TYPE_BLK_WR) || (rxcmd_type == CMD_TYPE_RMW)) && (rxcmd_pri == CMD_PRI_VPW);

// generating the intial loading value
// if the value is 0 coming in, then keep it as is
// else decrement by 1 and then store in the flop
assign init_load_wr_latency_value = (hif_cmd_latency != {WR_LATENCY_BITS{1'b0}}) ? 
                                         hif_cmd_latency - {{(WR_LATENCY_BITS-1){1'b0}},1'b1} : {WR_LATENCY_BITS{1'b0}};

// read latency counters for both the entries in the input FIFO
always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      wr_latency_0    <= {WR_LATENCY_BITS{1'b1}}; // reset to all 1's as all 0's is the timeout condition
      wr_latency_1    <= {WR_LATENCY_BITS{1'b1}};
      valid_vpw_0     <= 1'b0;
      valid_vpw_1     <= 1'b0;
      ih_gs_any_vpw_timed_out <= 1'b0;
   end
   else begin

      ih_gs_any_vpw_timed_out <= any_vpw_timed_out;

      // If valid write into FIFO && cmd is WR/RMW && priority is VPW, then load the input wr_latency into the 
      // apprpriate register based on fifo_vpw_wptr. Keep decrementing the timer every cycle as long as the values is not 0.

      if(load_vpw_0)
         wr_latency_0 <= init_load_wr_latency_value;
      else if(reset_vpw_0)
         wr_latency_0 <= {WR_LATENCY_BITS{1'b1}};
      else if(valid_vpw_0 & (wr_latency_0 != {WR_LATENCY_BITS{1'b0}}))
         wr_latency_0 <= wr_latency_0 - {{(WR_LATENCY_BITS-1){1'b0}},1'b1};

      if(load_vpw_1)
         wr_latency_1 <= init_load_wr_latency_value;
      else if(reset_vpw_1)
         wr_latency_1 <= {WR_LATENCY_BITS{1'b1}};
      else if(valid_vpw_1 & (wr_latency_1 != {WR_LATENCY_BITS{1'b0}}))
         wr_latency_1 <= wr_latency_1 - {{(WR_LATENCY_BITS-1){1'b0}},1'b1};

      if(load_vpw_0)
         valid_vpw_0     <= 1'b1;
      else if(reset_vpw_0)
         valid_vpw_0     <= 1'b0;

      if(load_vpw_1)
         valid_vpw_1     <= 1'b1;
      else if(reset_vpw_1)
         valid_vpw_1     <= 1'b0;


   end
end

//--------------------------
// Generating the timeout signal in IH
// - Either of the VPW latency counters are at 0 AND
// - the Collision indication (te_ih_retry) is low
//
// If Controller is handling a collision case
// then the vpw_timed_out signal should not be asserted. Otherwise it will cause lock-up condition
// in DDRC where the DDRC would try to flush the write command by going to Write mode, but that is
// prevented by the forceful Read mode due to expired-VPR signal from IH
//
// The consequence of doing this is that, if a command expires while in IH, then indication won't
// go to GS module, until the collision is cleared.
//--------------------------
assign any_vpw_timed_out = (~(|(wr_latency_0)) || (~(|(wr_latency_1)))) && (~te_ih_retry);

// Output the correct latency value based on fifo_vpw_rptr
assign rxcmd_wr_latency = (fifo_vpw_rptr == 1'b1) ? wr_latency_1 : wr_latency_0;

  //ccx_line_end



`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON


ih_rd_wr_fifo_empty: //---------------------------------------------------------
    assert property ( @ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
         (input_fifo_empty |-> (ih_fifo_wr_empty && ih_fifo_rd_empty))) 
    else $error("[%t][%m] ERROR: ih_fifo_rd_empty OR ih_fifo_wr_empty is showing non-empty when input_fifo_empty is showing empty.", $time);

ih_rd_wr_fifo_non_empty: //---------------------------------------------------------
    assert property ( @ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
         (~input_fifo_empty |-> (~ih_fifo_wr_empty || ~ih_fifo_rd_empty))) 
    else $error("[%t][%m] ERROR: ih_fifo_rd_empty AND ih_fifo_wr_empty are both HIGH when input_fifo_empty is low.", $time);

ih_input_fifo_no_wr_when_full:
    assert property ( @ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
         (fifo_put |-> ~input_fifo_full)) 
    else $error("[%t][%m] ERROR: Write into IH Input FIFO when it is FULL.", $time);

ih_input_fifo_no_rd_when_empty:
    assert property ( @ (posedge co_ih_clk) disable iff (~core_ddrc_rstn)
         (fifo_get |-> ~input_fifo_empty)) 
    else $error("[%t][%m] ERROR: Read from IH Input FIFO when it is Empty.", $time);



`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
