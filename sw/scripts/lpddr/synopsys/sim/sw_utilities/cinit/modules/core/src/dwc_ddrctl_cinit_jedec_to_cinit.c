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


#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_spd_struct.h"
#include "jedec/ddr5/cinit_ddr5_timing_utils.h"

uint32_t cinit_round_down_only_int_ddr4(uint32_t value_ps, uint32_t tck_ps)
{
    if (0 == tck_ps) {
        return 0;
    }

    return (((value_ps * 1000) / tck_ps) + 974) / 1000;
}


void dwc_ddrctl_cinit_jedec_to_cinit(void)
{
    ddrSpdData_t *memcfg = &(hdlr->spdData_m);

    SNPS_LOG("Overwriting memory configuration");

    for (uint8_t i = 0; i < hdlr->num_pstates; i++) {
        if (SPD.sdram_protocol == DWC_DDR4) {
            SPD.tck_ps[i] = SPD_aux.DDR4.tCKAVGmin_ps;
        }
        if (SPD.sdram_protocol == DWC_DDR5) {
            SPD.tck_ps[i] = SPD_aux.DDR5.tCKAVGmin;
        }
    }
    for (uint8_t i = 0; i < DWC_DDRCTL_DEV_CFG_NUM; i++) {
        SPD.sdram_width_bits[i] = SPD_aux.sdram_width_bits[i]; //!<SDRAM width (bits) [x4, x8, x16, x32]
        SPD.sdram_capacity_mbits[i] = SPD_aux.sdram_capacity_mbits[i]; //!<SDRAM capacity (megabits)
        SPD.sdram_capacity_mbits_lp45_mp[i] = SPD_aux.sdram_capacity_mbits_lp45_mp[i]; //!<SDRAM capacity (megabits)
        SPD.cid_width[i] = SPD_aux.cid_width[i]; //Number of 3DS CIDs in use 1-2H 2-4H per phyisical rank; //Number of 3DS CIDs in use 1-2H 2-4H per phyisical rank
        SPD.dram_raw[i] = SPD_aux.dram_raw[i]; //!<Row address bits
        SPD.dram_caw[i] = SPD_aux.dram_caw[i]; //!<Column address bits
        SPD.dram_baw[i] = SPD_aux.dram_baw[i]; //!<Bank address bits
        SPD.dram_bgw[i] = SPD_aux.dram_bgw[i]; //!<Bank group address bits
    }

    SPD.use_ddr4_tcwl_1st_set = 1;
    SPD.addr_mirror = SPD_aux.addr_mirror; //!<Address mirroring support (0-not supported, 1-supported)

    //The following structure members are calculated for you in the subsys_SetSpd() function. No need to set them

    SPD.num_ranks_per_dimm = SPD_aux.num_ranks_per_dimm; //!<
    SPD.num_ranks = SPD.num_ranks_per_dimm * SPD.num_dimm; //!<Number of ranks
    //uint8_t use_ddr4_tcwl_1st_set; //!< When calculating cwl_x use the lower set of
}


