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
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------

#include "sw_cmd_intf/ddr5/cinit_ddr5_sw_cmd.h"
#include "dwc_ddrctl_cinit_util.h"


typedef struct ddr5_sw_cmd_intf_str_s {
    ddrctl_ddr5_sw_cmd_intf_t   sw_cmd;
    char*                       name;
} ddr5_sw_cmd_intf_str_t;

static const ddr5_sw_cmd_intf_str_t ddr5_sw_cmd_intf_str_table[] = {
    {SW_CTRL_INTF_MRW        , "MRW"},
    {SW_CTRL_INTF_MRR        , "MRR"},
    {SW_CTRL_INTF_SR_CTRL    , "SR_CTRL"},
    {SW_CTRL_INTF_PD_CTRL    , "PD_CTRL"},
    {SW_CTRL_INTF_RST_CTRL   , "RST_CTRL"},
    {SW_CTRL_INTF_MPC        , "MPC"},
    {SW_CTRL_INTF_PRE        , "PRE"},
    {SW_CTRL_INTF_REF        , "REF"},
    {SW_CTRL_INTF_VREF       , "VREF"},
    {SW_CTRL_INTF_NOP        , "NOP"},
    {SW_CTRL_INTF_DES        , "DES"},
    {SW_CTRL_INTF_DISDQREF   , "DISDQREF"},
    {SW_CTRL_INTF_FORCECS    , "FORCECS"},
    {SW_CTRL_INTF_OPCTRL     , "OPCTRL"},
    {SW_CTRL_INTF_RFM        , "RFM"},
    {SW_CTRL_INTF_ACT        , "ACT"},
    {SW_CTRL_INTF_RD         , "RD"},
    {SW_CTRL_INTF_WR         , "WR"},
    {SW_CTRL_INTF_WRP        , "WRP"},
    {SW_CTRL_INTF_DFIUPD     , "DFIUPD"},
    {SW_CTRL_INTF_DFILP      , "DFILP"},
    {SW_CTRL_INTF_DFIFC      , "DFIFC"},
    {SW_CTRL_INTF_LOCK_CTRL  , "LOCK_CTRL"},
    {SW_CTRL_INTF_DFICLK     , "DFICLK"},
    {SW_CTRL_INTF_DFI_2N_MODE, "DFI_2N_MODE"},
    {SW_CTRL_INTF_REF_FLUSH  , "REF_FLUSH"}
};

const char* ddrctl_cinit_get_ddr5_sw_cmd_str(const ddrctl_ddr5_sw_cmd_intf_t sw_cmd)
{
    uint8_t i;

    for(i = 0; i < GET_ARR_NELEMS(ddr5_sw_cmd_intf_str_table); i++) {
        if(ddr5_sw_cmd_intf_str_table[i].sw_cmd == sw_cmd) {
            return ddr5_sw_cmd_intf_str_table[i].name;
        }
    }

    return "Unknown command";
}
