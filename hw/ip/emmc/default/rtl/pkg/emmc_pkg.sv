// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Bond <andrew.bond@axelera.ai>


/// Simple paremeters for the Cadence SDHC controller
/// Values are hard-coded in IP, but defined here for easier maintenance
///
package emmc_pkg;

    parameter int unsigned CDNS_EMMC_S_AWIDTH   = 13;
    parameter int unsigned CDNS_EMMC_S_DWIDTH   = 32;
    parameter int unsigned CDNS_EMMC_S_BEWIDTH  = (CDNS_EMMC_S_DWIDTH/8);
    parameter int unsigned CDNS_EMMC_M_AWIDTH   = 64;
    parameter int unsigned CDNS_EMMC_M_DWIDTH   = 64;
    parameter int unsigned CDNS_EMMC_M_BEWIDTH  = (CDNS_EMMC_M_DWIDTH/8);
    parameter int unsigned CDNS_EMMC_FIFODEPTH  = 8;
    parameter int unsigned CDNS_EMMC_RAM_DWIDTH = 64;

   // Register -> HW type Struct for Registers Driving into emmc
   typedef struct packed{
     logic[31:0] s0_hwinit_srs16; // 32 bit write reg emmc Capability register 1
     logic[31:0] s0_hwinit_srs17; // 32 bit write reg emmc Capability register 2
     logic[31:0] s0_hwinit_srs18; // 32 bit write reg emmc Capability register 3
     logic[31:0] s0_hwinit_srs19; // 32 bit write reg emmc Capability register 4
     logic[31:0] s0_hwinit_srs24; // 32 bit write reg emmc Capability register 5
     logic[31:0] s0_hwinit_srs25; // 32 bit write reg emmc Capability register 6
     logic[31:0] s0_hwinit_srs26; // 32 bit write reg emmc Capability register 7
     logic[31:0] s0_hwinit_srs27; // 32 bit write reg emmc Capability register 8
     logic[3:0] hwinit_itcfmul;   // Clock Multiplier
     logic[9:0] hwinit_itcfval;   // Clock Multiplier value
     logic[4:0] hwinit_itcfsel;   // Clock Multiplier Select
     logic ics;                   // Clock stable enable
    } emmc_outreg_cfg_t;

   // HW -> Register type Struct for Registers Driving out of emmc
   typedef struct packed {
     logic ice;                   // Clock enable output
    } emmc_inreg_cfg_t;


endpackage
