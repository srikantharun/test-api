//------------------------------------------------------------------------------
// Project    : Axelera LPDDR Subsystem
// File Name  : lpddr_subsystem_phy_init_details.sv
// Unit       : lpddr_subsystem_phy_init_details
//------------------------------------------------------------------------------
// Description: This file contains a structure summarizing all steps and
//              associated details required for the PHY Initialization Sequence
//              for the LPDDR Subsystem.
//------------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_PHY_INIT_DETAILS_SV
`define LPDDR_SUBSYSTEM_PHY_INIT_DETAILS_SV

typedef enum {REG_WRITE, POLL, WAIT_DFI, WAIT_FW_DONE} phy_init_step_type_e;

typedef struct {
  phy_init_step_type_e step_type;
  bit [31:0]           reg_addr;
  bit [31:0]           value;
} phy_init_data_t;

//-------------------------------------------------------------------------
// PHY Initialization Sequence
//-------------------------------------------------------------------------

const string phy_init_headings [string] = '{
  "A" : "Bring up VDD, VDDQ, VDD2H and VAA",
  "B" : "Start Clocks and Reset the PHY",
  "C" : "Initialize PHY Configuration",
  "D" : "Load the IMEM Memory",
  "E" : "Set the PHY input clocks to the desired frequency",
  "F" : "Write the Message Block parameters for the training firmware",
  "G" : "Execute the Training Firmware",
  "H" : "Read the Message Block results",
  "I" : "Load PHY Init Engine Image",
  "J" : "Initialize the PHY to Mission Mode through DFI Initialization",
  "K" : "PHY is ready for Mission Mode transactions"
};
const string ddrctl_init_headings [string] = '{
  "A" : "snps ctrl initial"
};

`include "phy_init_details/phy_init_skiptrain_details.sv"
`include "phy_init_details/phy_init_devinit_skiptrain_details.sv"
`include "phy_init_details/phy_init_train_details.sv"
`include "phy_init_details/snps_ddrctl_init.sv"
`include "phy_init_details/ddr_init2.sv"
`include "phy_init_details/snps_phy_init_details.sv"

`endif // LPDDR_SUBSYSTEM_PHY_INIT_DETAILS_SV
