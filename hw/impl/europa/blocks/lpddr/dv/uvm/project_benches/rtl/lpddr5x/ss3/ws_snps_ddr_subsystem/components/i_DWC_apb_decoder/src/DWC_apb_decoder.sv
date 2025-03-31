//  ------------------------------------------------------------------------
//  //
//  //                    (C) COPYRIGHT 2022 SYNOPSYS, INC.
//  //                            ALL RIGHTS RESERVED
//  //
//  //  This software and the associated documentation are confidential and
//  //  proprietary to Synopsys, Inc.  Your use or disclosure of this
//  //  software is subject to the terms and conditions of a written
//  //  license agreement between you, or your company, and Synopsys, Inc.
//  //
//  // The entire notice above must be reproduced on all authorized copies.
//  //
//  // Component Name   : DWC_apb_decoder
//  //
//  ------------------------------------------------------------------------
module DWC_apb_decoder
#(

        
      // Name:         pSS_APB_AW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      // Name:         pSS_APB_AW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      parameter pSS_APB_AW = 32,


      // Name:         pSS_APB_DW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      // Name:         pSS_APB_DW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      parameter pSS_APB_DW = 32,


      // Name:         pDDRCTL_APB_AW
      // Default:      24
      // Values:       -2147483648, ..., 2147483647
      // Name:         pDDRCTL_APB_AW
      // Default:      24
      // Values:       -2147483648, ..., 2147483647
      parameter pDDRCTL_APB_AW = 24,


      // Name:         pDDRCTL_APB_DW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      // Name:         pDDRCTL_APB_DW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      parameter pDDRCTL_APB_DW = 32,


      // Name:         pDDRPHY_APB_AW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      // Name:         pDDRPHY_APB_AW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      parameter pDDRPHY_APB_AW = 32,


      // Name:         pDDRPHY_APB_DW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      // Name:         pDDRPHY_APB_DW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      parameter pDDRPHY_APB_DW = 32,


      // Name:         pCSR_APB_AW
      // Default:      24
      // Values:       -2147483648, ..., 2147483647
      // Name:         pCSR_APB_AW
      // Default:      24
      // Values:       -2147483648, ..., 2147483647
      parameter pCSR_APB_AW = 24,


      // Name:         pCSR_APB_DW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      // Name:         pCSR_APB_DW
      // Default:      32
      // Values:       -2147483648, ..., 2147483647
      parameter pCSR_APB_DW = 32
      )
(
    
    
    input pclk,

    input presetn,
    
    // External APB 
    input  wire [pSS_APB_AW-1:0]        paddr,
    
    input  wire [pSS_APB_DW-1:0]        pwdata,
    
    input  wire                         pwrite,
    
    input  wire                         psel,
    
    input  wire                         penable,
    
    output wire                          pready,
    
    output wire  [pSS_APB_DW-1:0]        prdata,
    
    output wire                          pslverr,
    
    input wire   [3:0]                  pstrb,

    input wire   [2:0]                  pprot,

    input wire   [2:0]                  pprot_pin,

    output wire   [3:0]                  prdata_par,

    
    // ddrctl0 APB
    output wire  [pDDRCTL_APB_AW-1:0]    ddrctl0_paddr,
    output wire  [pDDRCTL_APB_DW-1:0]    ddrctl0_pwdata,
    output wire                          ddrctl0_pwrite,
    output wire                          ddrctl0_psel,
    output wire                          ddrctl0_penable,
    input  wire                         ddrctl0_pready,
    input  wire [pDDRCTL_APB_DW-1:0]    ddrctl0_prdata,
    input  wire                         ddrctl0_pslverr,

// DDRPHY APB
    output wire  [pDDRPHY_APB_AW-1:0]    ddrphy_paddr,
    output wire  [pDDRPHY_APB_DW-1:0]    ddrphy_pwdata,
    output wire                          ddrphy_pwrite,
    output wire                          ddrphy_psel,
    output wire                          ddrphy_penable,
    output wire   [3:0]                  ddrphy_pstrb,
    input  wire                          ddrphy_pslverr,
    input  wire                          ddrphy_pready,
    input  wire [pDDRPHY_APB_DW-1:0]     ddrphy_prdata,
    output wire   [2:0]                  ddrphy_pprot,
    output wire   [2:0]                  ddrphy_pprot_pin,
    input wire    [3:0]                  ddrphy_prdata_par
    );

//Internal wires
wire ddrctl0_addr_range_det;
wire ddrphy_addr_range_det;
wire illegal_detect;
wire reserved_detect;
wire err_resp_det;

wire ddrctl0_addr_range_select;
wire ddrphy_addr_range_select;


// Set Active Perifieral for Response Selection
// This  Breaks Feedthrough Paths Externall!
wire ddrctl0_active_nxt;
wire ddrphy_active_nxt;

reg  ddrctl0_active;
reg  ddrphy_active;

wire new_req_det;
wire addr_out_of_range;
wire addr_err_resp_next;
reg  addr_err_resp;
wire err_resp_act;

// New Request Detect
assign new_req_det = (psel && !penable);

// Detect Legal Request Addresses
// Legal Addresses
// PHY:         26'h000_0000 - 26'h1FF_FFFF
// Controller:  26'h200_0000 - 26'h23F_FFFF


// Controller Selected at paddr[25:22] == 0x8
assign ddrctl0_addr_range_det    = (paddr[25:22] == 4'b1000);


// PHY Selected at paddr[25] == 0x0
assign ddrphy_addr_range_det     = (paddr[25] == 1'b0);


// Illegal Detect
assign illegal_detect = (~ddrctl0_addr_range_det && ~ddrphy_addr_range_det );


// Block out of range addresses
// SS: Address Ranges Changed
assign addr_out_of_range = (|paddr[pSS_APB_AW-1:26]);

// Error Response Detect
assign err_resp_det = ((addr_out_of_range || illegal_detect) && new_req_det);

// Slave Address Error Response
assign addr_err_resp_next = err_resp_det ? 1'b1 :
                            pready ? 1'b0 : addr_err_resp;

// Error Response Active
assign err_resp_act = (err_resp_det || addr_err_resp);

// Select Periferal
assign ddrphy_addr_range_select     = (ddrphy_addr_range_det && !err_resp_act);
assign ddrctl0_addr_range_select    = (ddrctl0_addr_range_det && !err_resp_act);


// We Must Register Selected Perifieral For Response Selection
assign ddrphy_active_nxt     = (ddrphy_addr_range_select && new_req_det) ? 1'b1 :
                               pready ? 1'b0 : ddrphy_active;

assign ddrctl0_active_nxt    = (ddrctl0_addr_range_select && new_req_det) ? 1'b1 :
                               pready ? 1'b0 : ddrctl0_active;


// Response Select Registers Breaks Feedthrough Paths From/To IO
always@ (posedge pclk or negedge presetn)
  begin
    if (!presetn) begin
        addr_err_resp     <= 1'b0;
        ddrctl0_active    <= 1'b0;
        ddrphy_active     <= 1'b0;
   end
    else begin
        addr_err_resp     <= addr_err_resp_next;
        ddrctl0_active    <= ddrctl0_active_nxt;
        ddrphy_active     <= ddrphy_active_nxt;
    end
  end


// Assigning the outputs to the different APB slave
// Not using reserved space above 0x3F_FFFF
assign  ddrctl0_paddr[23:0] = {2'b00,paddr[21:0]};

assign  ddrctl0_pwdata      = pwdata  ;
assign  ddrctl0_pwrite      = pwrite  & ddrctl0_addr_range_select ;
assign  ddrctl0_psel        = psel    & ddrctl0_addr_range_select ;
assign  ddrctl0_penable     = penable & ddrctl0_addr_range_select ;

//assign  ddrphy_paddr        = paddr;  //for PHY the address is made byte aligned like 0,4,8,C
assign  ddrphy_paddr        = {2'b00,paddr[pDDRPHY_APB_AW-1:2]};

assign  ddrphy_pwdata       = pwdata  ;
assign  ddrphy_pwrite       = pwrite  & ddrphy_addr_range_select ;
assign  ddrphy_psel         = psel    & ddrphy_addr_range_select ;
assign  ddrphy_penable      = penable & ddrphy_addr_range_select ;
assign  ddrphy_pstrb        = pstrb   ;
assign  ddrphy_pprot        = pprot   ;
assign  ddrphy_pprot_pin    = pprot_pin;
assign  prdata_par          = ddrphy_prdata_par;



// Selecting Response Based On Registered Active to Break Feedthrough Paths From/To IO
// Added Slave Error Response
assign pready =  addr_err_resp       ? 1'b1 :
                 ddrctl0_active      ? ddrctl0_pready :
                 ddrphy_active       ? ddrphy_pready  : 
                 1'b0;
          
assign prdata =  ddrctl0_active      ? ddrctl0_prdata : 
                 ddrphy_active       ? ddrphy_prdata  :
                 {pSS_APB_DW{1'b0}};
          
assign pslverr =  addr_err_resp                ? 1'b1 :
                  ddrctl0_active     ? ddrctl0_pslverr :
                  ddrphy_active      ? ddrphy_pslverr  :
                  1'b0;
    

endmodule //end of module DWC_ddr_ss_apb_decoder 

