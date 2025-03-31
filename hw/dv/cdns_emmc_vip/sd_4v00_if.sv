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
//   SD 4.0 slot/card interface
//
//------------------------------------------------------------------------------

`ifndef SD_4V00_IF_SV
`define SD_4V00_IF_SV

`timescale 1ns/100ps

`ifndef UVM
`include "sv_macros.svh"
`endif

interface sd_4v00_if;
  timeunit 100ps; timeprecision 1ps;

  realtime HOST2CARD_DELAY = 0ns;
  realtime CARD2HOST_DELAY = 0ns;

  function void set_line_delays(input int host2card_in_ps,
                                input int card2host_in_ps);
    HOST2CARD_DELAY = host2card_in_ps * 1ps;
    CARD2HOST_DELAY = card2host_in_ps * 1ps;
  endfunction : set_line_delays

  //---------------------------------------------------------------------------

  logic                     rst_n;
  bit                       card_removed;

  // *** SD Interface signals host-side:

  wire                      clk;          // clock signal
  wire                      cmd;          // command/response line
  wire [7:0]                dat;          // data lines
  wire                      ds_i;         // data strobe input on host side

  // *** SD Interface signals card-side with host-card delay:

  logic                     clk_b;
  logic                     clk_d;
  logic                     cmd_b;
  logic                     cmd_d;
  logic [7:0]               dat_b;
  logic [7:0]               dat_d;

  // *** SD Interface signals for card-side outputs:
  // (enable card-host delay modelling as well as procedural assignments from SD XTOR)
  logic                     cmd_o;
  logic [7:0]               dat_o;
  logic                     ds_o;         // data strobe (eMMC v.5)

  logic                     sdcd_n_o;
  logic                     sdwp_n_o;

  logic                     check_emmc; // 0 = SD legacy; 1 = eMMC

  // host -> card delay modelling
  always @(*)  clk_b  <=    clk;
  always @(*)  cmd_b  <=    cmd;
  always @(*)  dat_b  <=    dat;
  always @(*)  clk_d  <=    #HOST2CARD_DELAY clk_b;
  always @(*)  cmd_d  <=    #HOST2CARD_DELAY cmd_b;
  always @(*)  dat_d  <=    #HOST2CARD_DELAY dat_b;

  // card -> host delay modelling

  assign #CARD2HOST_DELAY clk  = 1'bz;
  assign #CARD2HOST_DELAY cmd  = cmd_o;
  assign #CARD2HOST_DELAY dat  = dat_o;
`ifdef GATE_SIM
  assign #CARD2HOST_DELAY ds_i = (ds_o === 1'b1) ? 1'b1 : 1'b0;
`else
  assign #CARD2HOST_DELAY ds_i = ds_o;
`endif

  //---------------------------------------------------------------------------

  wire                      sdcd_n      ; // active low card detect
  wire                      sdwp_n      ; // active low write protect
  logic                     led         ; // led driver
  logic                     cle         ; // current limit error
  wire                      bus_pow     ; // bus power on
  logic [2:0]               bus_volt    ; // bus_voltage_select
  logic                     bus_pow2    ; // bus power on 2
  logic [2:0]               bus_volt2   ; // bus_voltage_select 2
  logic                     bus_lvs     ; // lov voltage signaling

  logic                     ref_sdmclk  ; //sdclk clock reference for frequency divider verification

  // card power on reset
  assign rst_n = bus_pow;

  // error injection flags

  bit                       cmd_tout_error;
  bit                       cmd_crc_error;
  bit                       cmd_end_bit_error;
  bit                       cmd_index_error;
  bit                       dat_tout_error;
  bit                       dat_crc_error;
  bit                       dat_end_bit_error;
//bit                       response_error;

  assign                    sdcd_n   = sdcd_n_o;
  assign                    sdwp_n   = sdwp_n_o;

  // Boot Interface - see implementation spec for full details on what each setting does.

  logic          boot_en;
  logic          boot_ack_en;
  logic          boot_method;
  logic [1:0]    boot_buswidth;
  logic [9:0]    boot_sdclkdiv;
  logic          boot_addrwidth;
  logic [63:0]   boot_addr;
  logic [31:0]   boot_blockcnt;
  logic [11:0]   boot_blocksize;
  logic [2:0]    boot_bvs;
  logic [1:0]    boot_speedmode;
  logic [31:0]   boot_pow_clk_dly;
  logic [31:0]   boot_clk_cmd_dly;
  logic [3:0]    boot_timeout_ack;
  logic [3:0]    boot_timeout_dat;
//  logic [7:0]    boot_phyidly;
//  logic [3:0]    boot_sdcdis;
  logic [31:0]   boot_wr_dly;
  logic [9:0]    boot_io_dly;
  logic [3:0]    boot_exten;
  logic [3:0]    boot_clkadj;
  logic [3:0]    boot_phy_dqstm;
  logic [9:0]    boot_phy_dqtm;
  logic [8:0]    boot_phy_glpbk;
  logic          boot_phy_dllmst;
  logic [15:0]   boot_phy_dllslv;
  logic          boot_setup_mode;
  logic [63:0]   boot_desc_addr;
  logic          boot_ack;
  logic          boot_done;
  logic          boot_err;

  modport CHIP (
   inout  clk,
   inout  cmd, dat,
   input  ds_i,
   input  sdcd_n, sdwp_n,
   input  cle,
   output led,
   inout  bus_pow,
   output bus_volt,bus_lvs,
   output bus_pow2,bus_volt2
  );

  modport CARD_BEH (
    inout  clk,
    inout  cmd, dat,
    output sdcd_n_o, sdwp_n_o,
    inout  bus_pow,
    output card_removed,
    output check_emmc
  );

  modport CARD_SLOT (
    inout  clk,
    inout  cmd, dat,
    output ds_i,
    output sdcd_n, sdwp_n,
    output cle,
    input  led,
    inout  bus_pow,
    input  bus_volt,bus_lvs,
    input  bus_pow2,bus_volt2,
    output card_removed
  );

  //---------------------------------------------------------------------------

  modport HOST (output rst_n, inout clk,          cmd,   dat);
  modport CARD (input  rst_n,       clk_d,        cmd_d, dat_d,
                                           output cmd_o, dat_o, ds_o);

  modport CHK  (input  rst_n,       clk,
                                    clk_d,        cmd_d, dat_d,
                                                  cmd_o, dat_o, ds_o,

                input cmd_tout_error, cmd_crc_error, cmd_end_bit_error, cmd_index_error,
                      dat_tout_error, dat_crc_error, dat_end_bit_error/*,response_error*/,
                      card_removed,   check_emmc, ref_sdmclk, bus_pow);

  modport ERR_CTRL (output cmd_tout_error, cmd_crc_error, cmd_end_bit_error, cmd_index_error,
                           dat_tout_error, dat_crc_error, dat_end_bit_error/*,response_error*/);

  // Monitor
  clocking cb_posedge @(posedge clk);
      input cmd;
      input dat;
  endclocking
  clocking cb_negedge @(negedge clk);
      input cmd;
      input dat;
  endclocking
  clocking cb_edge @(clk);
  endclocking
  clocking cb_ds_posedge @(posedge ds_i);
      input dat;
  endclocking
  clocking cb_ds_negedge @(negedge ds_i);
      input dat;
  endclocking
  clocking cb_ds_edge @(ds_i);
      input dat;
  endclocking
  
  
  
   task TunigTimeoutLimiter;
      @(negedge clk_d);
      //force cmd = 1'b0;
      force dat = 8'h0;
      repeat(10) @(negedge clk_d);
      //release cmd ; //<= 1'bZ;
      release dat ; //<= 8'hZZ;
   endtask : TunigTimeoutLimiter
  


endinterface : sd_4v00_if


interface parallel_uhsii_if;

  // -- PHYSICAL LANE:            STB[18], DATA MODE[17:16], DATA[15:0]

  wire                      rclk;     // ref clk I/O
  wire  [18:0]              lane0;    // physical lane 0 (model doesn't include 8b/10b decoder)
  wire  [18:0]              lane1;    // physical lane 1 (model doesn't include 8b/10b decoder)
  int                       error_core_phy;
  int                       error_card_phy;

  modport CORE_PHY (inout rclk, lane0, lane1,  input error_core_phy);
  modport CARD_PHY (inout rclk, lane0, lane1,  input error_card_phy);

endinterface

`endif // SD_4V00_IF_SV
