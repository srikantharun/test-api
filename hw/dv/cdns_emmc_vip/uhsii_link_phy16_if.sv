//------------------------------------------------------------------------------
//                                                                              
//            CADENCE                    Copyright (c) 2013                     
//                                       Cadence Design Systems, Inc.           
//                                       All rights reserved.                   
//                                                                              
//  This work may not be copied, modified, re-published, uploaded, executed, or 
//  distributed in any way, in any medium, whether in whole or in part, without 
//  prior written permission from Cadence Design Systems, Inc.                  
//------------------------------------------------------------------------------
//                                                                              
//   Author                : (username)@cadence.com                              
//                                                                              
//   Date                  : $Date$
//                                                                              
//   Last Changed Revision : $LastChangedRevision$
// 
//------------------------------------------------------------------------------
//   Description                                                                
//                                                                 
//   interface uhsii_link_phy16_if 
//                                       
//------------------------------------------------------------------------------

`timescale 1ns/100ps

`ifndef UVM
`include "sv_macros.svh"
`endif

interface uhsii_link_phy16_if (
  // *** EXT inputs ***
  input rst_n,                      // asynchronous reset active LOW
  input sclk                        // source CLK for PHY
);

  // *** from LINK ***
  logic [15:0]        td;           // transmit data
  logic [1:0]         tdm;          // TD coding mode
  logic [15:0]        tdr;          // transmit data for RX
  logic [1:0]         tdrm;         // TDR coding mode

  logic [3:0]         pinit_pcmd, pinit_reg,
                      pinit, pcmd;  // PHY init/cmnd
  logic [1:0]         tds, tdrs;    // PHY control (transmission)
  logic               mode;         // PHY power mode

  bit                 force_err;    // inject bit error (card-side only)

  // *** from PHY ***
  logic [15:0]        rd;           // receive data
  logic [1:0]         rdm;          // RD coding mode
  logic [15:0]        rdt;          // receive data for Tx
  logic [1:0]         rdtm;         // RDT coding mode

  logic [1:0]         rds, rdts;    // PHY control (receive)
  logic               det, lock,
                      pack, err;    // PHY status [0..3]
  logic               pclk;         // parallel CLK for LINK
 
  // *** LSS Params ***
  int                 n_lss_dir;
  int                 n_lss_syn;
  int                 n_data_gap;
  bit                 lpm;
  bit                 active;
  bit                 go4reset;
  bit                 go2dormant;

   // addtional PHY PINS
  
  logic               nrst              ;
  logic               det_en            ;
  logic               rclktrmen         ;   
  logic [31:0]        cnfg_r1           ;
  logic [31:0]        cnfg_r2           ;
  logic [31:0]        cnfg_status       ;
  
  // SDIO interrupt UHS-II card output
  
  logic               intr_n;

  modport CORE (output td, tdm, tdr, tdrm,
                       pinit_pcmd, tds, tdrs,
                       mode,
                input  rd, rdm, rdt, rdtm,
                       det, lock, pack, err,
                       rds, rdts, pclk,
                //PHY interface  
                output nrst,                
                output det_en,
                output rclktrmen,
                input  cnfg_status,
                output cnfg_r1,
                output cnfg_r2
               );

  modport LINK (input  rst_n,
                output td, tdm, tdr, tdrm,
                       pinit_pcmd, tds, tdrs,
                       mode,
                input  rd, rdm, rdt, rdtm,
                       det, lock, pack, err,
                       rds, rdts, pclk,
                //CHK 
                output n_lss_dir,
                       n_lss_syn,
                       n_data_gap,
                       lpm,
                       active,
                       go4reset,
                       go2dormant,
                //SLI interface  
                output nrst,                
                output det_en,
                output rclktrmen,
                input  cnfg_status,
                output cnfg_r1,
                output cnfg_r2,
                //ERR generation
                output force_err);

  modport PHY  (input  sclk,
                input  td, tdm, tdr, tdrm,
                       pinit_pcmd, tds, tdrs,
                       mode,
                output rd, rdm, rdt, rdtm,
                       det, lock, pack, err,
                       rds, rdts, pclk,
                //SLI interface 
                input  nrst,                
                input  det_en,
                input  rclktrmen,
                output cnfg_status,
                input  cnfg_r1,
                input  cnfg_r2,
                input  force_err);

  modport CHK  (input rst_n,
                      td, tdm, tdr, tdrm,
                      pinit, pinit_reg, pcmd, tds, tdrs,
                      mode,
                      rd, rdm, rdt, rdtm,
                      det, lock, pack, err,
                      rds, rdts, pclk,
                      n_lss_dir,
                      n_lss_syn,
                      n_data_gap,
                      lpm,
                      active,
                      go4reset,
                      go2dormant,
                      force_err);
                      
  modport INTR (output intr_n);

  assign pinit = pinit_pcmd;
  assign pcmd  = pinit_pcmd;
  
  always @(posedge pclk)
    pinit_reg <= pinit_pcmd;
  
endinterface : uhsii_link_phy16_if
