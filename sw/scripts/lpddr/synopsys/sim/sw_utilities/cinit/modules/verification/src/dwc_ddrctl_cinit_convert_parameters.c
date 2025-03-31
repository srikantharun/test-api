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
#include "dwc_ddrctl_cinit_types.h"
#include "gen_cfg/dwc_ddrctl_cinit_gen_cfg_mr.h"

/**
 * @brief Function to generate .config file with mr, spd amd genericconfguration values from binary struct.
 */

void dwc_ddrctl_cinit_convert_params(SubsysHdlr_t *cfg)
{
    dwc_ddrctl_cinit_gen_cfg_mr(cfg);

    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ENABLE_NON_JEDEC_TCK=%u", CFG->enable_non_jedec_tck);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_PROTOCOL=%u", SPD.sdram_protocol);
    switch(SPD.sdram_protocol)
    {
        case DWC_DDR4:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4=y", NULL);
        break;
        case DWC_DDR5:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5=y", NULL);
        break;
        case DWC_LPDDR4:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR4=y", NULL);
        break;
        case DWC_LPDDR5:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_LPDDR5=y", NULL);
        break;
    }

    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_MODULE_TYPE=%u", SPD.module_type);
    switch(SPD.module_type)
    {
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_MODULE_TYPE_NODIMM=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_MODULE_TYPE_RDIMM=y", NULL);
        break;
        case 3:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_MODULE_TYPE_LRDIMM=y", NULL);
        break;
        case 4:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_MODULE_TYPE_UDIMM=y", NULL);
        break;
    }
#ifdef DDRCTL_LPDDR
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE=%u", SPD.lpddr4_data_rate);
    switch(SPD.lpddr4_data_rate)
    {
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE_533=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE_1066=y", NULL);
        break;
        case 3:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE_1600=y", NULL);
        break;
        case 4:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE_2133=y", NULL);
        break;
        case 5:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE_2667=y", NULL);
        break;
        case 6:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE_3200=y", NULL);
        break;
        case 7:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE_3733=y", NULL);
        break;
        case 8:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR4_DATA_RATE_4267=y", NULL);
        break;
    }

	SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE=%u", SPD.lpddr5_data_rate);
	switch(SPD.lpddr5_data_rate)
	{
		case 1:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_533=y", NULL);
		break;
		case 2:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_1067=y", NULL);
		break;
		case 3:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_1600=y", NULL);
		break;
		case 4:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_2133=y", NULL);
		break;
		case 5:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_2750=y", NULL);
		break;
		case 6:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_3200=y", NULL);
		break;
		case 7:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_3733=y", NULL);
		break;
		case 8:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_4267=y", NULL);
		break;
		case 9:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_4800=y", NULL);
		break;
		case 10:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_5500=y", NULL);
		break;
		case 11:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_6000=y", NULL);
		break;
		case 12:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_6400=y", NULL);
		break;
		case 13:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_7500=y", NULL);
		break;
		case 14:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_8533=y", NULL);
		break;
		case 15:
			SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_DATA_RATE_9600=y", NULL);
		break;
	}
#if UMCTL2_FREQUENCY_NUM > 0
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_0=%u", SPD.lpddr5_bk_bg_org[0]);
    switch(SPD.lpddr5_bk_bg_org[0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_0_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_0_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_0_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 0 */
#if UMCTL2_FREQUENCY_NUM > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_1=%u", SPD.lpddr5_bk_bg_org[1]);
    switch(SPD.lpddr5_bk_bg_org[1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_1_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_1_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_1_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 1 */
#if UMCTL2_FREQUENCY_NUM > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_2=%u", SPD.lpddr5_bk_bg_org[2]);
    switch(SPD.lpddr5_bk_bg_org[2])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_2_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_2_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_2_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 2 */
#if UMCTL2_FREQUENCY_NUM > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_3=%u", SPD.lpddr5_bk_bg_org[3]);
    switch(SPD.lpddr5_bk_bg_org[3])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_3_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_3_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_3_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 3 */
#if UMCTL2_FREQUENCY_NUM > 4
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_4=%u", SPD.lpddr5_bk_bg_org[4]);
    switch(SPD.lpddr5_bk_bg_org[4])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_4_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_4_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_4_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 4 */
#if UMCTL2_FREQUENCY_NUM > 5
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_5=%u", SPD.lpddr5_bk_bg_org[5]);
    switch(SPD.lpddr5_bk_bg_org[5])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_5_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_5_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_5_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 5 */
#if UMCTL2_FREQUENCY_NUM > 6
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_6=%u", SPD.lpddr5_bk_bg_org[6]);
    switch(SPD.lpddr5_bk_bg_org[6])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_6_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_6_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_6_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 6 */
#if UMCTL2_FREQUENCY_NUM > 7
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_7=%u", SPD.lpddr5_bk_bg_org[7]);
    switch(SPD.lpddr5_bk_bg_org[7])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_7_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_7_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_7_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 7 */
#if UMCTL2_FREQUENCY_NUM > 8
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_8=%u", SPD.lpddr5_bk_bg_org[8]);
    switch(SPD.lpddr5_bk_bg_org[8])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_8_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_8_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_8_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 8 */
#if UMCTL2_FREQUENCY_NUM > 9
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_9=%u", SPD.lpddr5_bk_bg_org[9]);
    switch(SPD.lpddr5_bk_bg_org[9])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_9_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_9_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_9_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 9 */
#if UMCTL2_FREQUENCY_NUM > 10
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_10=%u", SPD.lpddr5_bk_bg_org[10]);
    switch(SPD.lpddr5_bk_bg_org[10])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_10_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_10_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_10_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 10 */
#if UMCTL2_FREQUENCY_NUM > 11
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_11=%u", SPD.lpddr5_bk_bg_org[11]);
    switch(SPD.lpddr5_bk_bg_org[11])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_11_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_11_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_11_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 11 */
#if UMCTL2_FREQUENCY_NUM > 12
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_12=%u", SPD.lpddr5_bk_bg_org[12]);
    switch(SPD.lpddr5_bk_bg_org[12])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_12_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_12_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_12_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 12 */
#if UMCTL2_FREQUENCY_NUM > 13
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_13=%u", SPD.lpddr5_bk_bg_org[13]);
    switch(SPD.lpddr5_bk_bg_org[13])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_13_4BK_4BG=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_13_8BK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LPDDR5_BK_BG_13_16BK=y", NULL);
        break;
    }
#endif /* UMCTL2_FREQUENCY_NUM > 13 */

#endif /* DDRCTL_LPDDR */

#ifdef DDRCTL_DDR
    if(SPD.sdram_protocol == DWC_DDR4) {
        SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SPEED_GRADE=%u", SPD.ddr4_sg);
        switch(SPD.ddr4_sg)
        {
            case DWC_DDR4_1600J:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1600J=y", NULL);
            break;
            case DWC_DDR4_1600K:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1600K=y", NULL);
            break;
            case DWC_DDR4_1600L:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1600L=y", NULL);
            break;
            case DWC_DDR4_1866L:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1866L=y", NULL);
            break;
            case DWC_DDR4_1866M:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1866M=y", NULL);
            break;
            case DWC_DDR4_1866N:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1866N=y", NULL);
            break;
            case DWC_DDR4_2133N:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2133N=y", NULL);
            break;
            case DWC_DDR4_2133P:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2133P=y", NULL);
            break;
            case DWC_DDR4_2133R:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2133R=y", NULL);
            break;
            case DWC_DDR4_2400P:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2400P=y", NULL);
            break;
            case DWC_DDR4_2400R:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2400R=y", NULL);
            break;
            case DWC_DDR4_2400T:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2400T=y", NULL);
            break;
            case DWC_DDR4_2400U:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2400U=y", NULL);
            break;
            case DWC_DDR4_2666T:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2666T=y", NULL);
            break;
            case DWC_DDR4_2666U:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2666U=y", NULL);
            break;
            case DWC_DDR4_2666V:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2666V=y", NULL);
            break;
            case DWC_DDR4_2666W:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2666W=y", NULL);
            break;
            case DWC_DDR4_2933V:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2933V=y", NULL);
            break;
            case DWC_DDR4_2933W:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2933W=y", NULL);
            break;
            case DWC_DDR4_2933Y:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2933Y=y", NULL);
            break;
            case DWC_DDR4_2933AA:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2933AA=y", NULL);
            break;
            case DWC_DDR4_3200W:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_3200W=y", NULL);
            break;
            case DWC_DDR4_3200AA:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_3200AA=y", NULL);
            break;
            case DWC_DDR4_3200AC:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_3200AC=y", NULL);
            break;
            case DWC_DDR4_1600J_3DS2B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1600J_3DS2B=y", NULL);
            break;
            case DWC_DDR4_1600K_3DS2B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1600K_3DS2B=y", NULL);
            break;
            case DWC_DDR4_1600L_3DS2B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1600L_3DS2B=y", NULL);
            break;
            case DWC_DDR4_1866L_3DS2B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1866L_3DS2B=y", NULL);
            break;
            case DWC_DDR4_1866M_3DS2B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1866M_3DS2B=y", NULL);
            break;
            case DWC_DDR4_1866N_3DS2B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_1866N_3DS2B=y", NULL);
            break;
            case DWC_DDR4_2133P_3DS2A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2133P_3DS2A=y", NULL);
            break;
            case DWC_DDR4_2133P_3DS3A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2133P_3DS3A=y", NULL);
            break;
            case DWC_DDR4_2133R_3DS4A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2133R_3DS4A=y", NULL);
            break;
            case DWC_DDR4_2400P_3DS3B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2400P_3DS3B=y", NULL);
            break;
            case DWC_DDR4_2400T_3DS2A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2400T_3DS2A=y", NULL);
            break;
            case DWC_DDR4_2400U_3DS2A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2400U_3DS2A=y", NULL);
            break;
            case DWC_DDR4_2400U_3DS4A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2400U_3DS4A=y", NULL);
            break;
            case DWC_DDR4_2666T_3DS3A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2666T_3DS3A=y", NULL);
            break;
            case DWC_DDR4_2666V_3DS3A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2666V_3DS3A=y", NULL);
            break;
            case DWC_DDR4_2666W_3DS4A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2666W_3DS4A=y", NULL);
            break;
            case DWC_DDR4_2933W_3DS3A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2933W_3DS3A=y", NULL);
            break;
            case DWC_DDR4_2933Y_3DS3A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2933Y_3DS3A=y", NULL);
            break;
            case DWC_DDR4_2933AA_3DS43A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_2933AA_3DS43A=y", NULL);
            break;
            case DWC_DDR4_3200W_3DS4A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_3200W_3DS4A=y", NULL);
            break;
            case DWC_DDR4_3200AA_3DS4A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_3200AA_3DS4A=y", NULL);
            break;
            case DWC_DDR4_3200AC_3DS4A:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR4_SG_3200AC_3DS4A=y", NULL);
            break;
            case DWC_DDR4_MONO_FIRST_SG:
            case DWC_DDR4_MONO_LAST_SG:
            case DWC_DDR4_3DS_FIRST_SG:
            case DWC_DDR4_3DS_LAST_SG:
            default:
                SNPS_ERROR("Invalid sg used: %d", SPD.ddr4_sg);
            break;
        }
    }
    if(SPD.sdram_protocol == DWC_DDR5) {
        SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SPEED_GRADE_0=%u", SPD.ddr5_speed_bin[0]);
        switch(SPD.ddr5_speed_bin[0])
        {
            case DWC_DDR5_3200AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3200AN=y", NULL);
            break;
            case DWC_DDR5_3200B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3200B=y", NULL);
            break;
            case DWC_DDR5_3200BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3200BN=y", NULL);
            break;
            case DWC_DDR5_3200C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3200C=y", NULL);
            break;
            case DWC_DDR5_3600AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3600AN=y", NULL);
            break;
            case DWC_DDR5_3600B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3600B=y", NULL);
            break;
            case DWC_DDR5_3600BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3600BN=y", NULL);
            break;
            case DWC_DDR5_3600C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3600C=y", NULL);
            break;
            case DWC_DDR5_4000AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4000AN=y", NULL);
            break;
            case DWC_DDR5_4000B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4000B=y", NULL);
            break;
            case DWC_DDR5_4000BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4000BN=y", NULL);
            break;
            case DWC_DDR5_4000C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4000C=y", NULL);
            break;
            case DWC_DDR5_4400AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4400AN=y", NULL);
            break;
            case DWC_DDR5_4400B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4400B=y", NULL);
            break;
            case DWC_DDR5_4400BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4400BN=y", NULL);
            break;
            case DWC_DDR5_4400C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4400C=y", NULL);
            break;
            case DWC_DDR5_4800AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4800AN=y", NULL);
            break;
            case DWC_DDR5_4800B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4800B=y", NULL);
            break;
            case DWC_DDR5_4800BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4800BN=y", NULL);
            break;
            case DWC_DDR5_4800C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4800C=y", NULL);
            break;
            case DWC_DDR5_5200AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5200AN=y", NULL);
            break;
            case DWC_DDR5_5200B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5200B=y", NULL);
            break;
            case DWC_DDR5_5200BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5200BN=y", NULL);
            break;
            case DWC_DDR5_5200C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5200C=y", NULL);
            break;
            case DWC_DDR5_5600AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5600AN=y", NULL);
            break;
            case DWC_DDR5_5600B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5600B=y", NULL);
            break;
            case DWC_DDR5_5600BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5600BN=y", NULL);
            break;
            case DWC_DDR5_5600C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5600C=y", NULL);
            break;
            case DWC_DDR5_6000AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6000AN=y", NULL);
            break;
            case DWC_DDR5_6000B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6000B=y", NULL);
            break;
            case DWC_DDR5_6000BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6000BN=y", NULL);
            break;
            case DWC_DDR5_6000C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6000C=y", NULL);
            break;
            case DWC_DDR5_6400AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6400AN=y", NULL);
            break;
            case DWC_DDR5_6400B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6400B=y", NULL);
            break;
            case DWC_DDR5_6400BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6400BN=y", NULL);
            break;
            case DWC_DDR5_6400C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6400C=y", NULL);
            break;
            case DWC_DDR5_6800AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6800AN=y", NULL);
            break;
            case DWC_DDR5_6800B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6800B=y", NULL);
            break;
            case DWC_DDR5_6800BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6800BN=y", NULL);
            break;
            case DWC_DDR5_6800C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6800C=y", NULL);
            break;
            case DWC_DDR5_7200AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7200AN=y", NULL);
            break;
            case DWC_DDR5_7200B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7200B=y", NULL);
            break;
            case DWC_DDR5_7200BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7200BN=y", NULL);
            break;
            case DWC_DDR5_7200C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7200C=y", NULL);
            break;
            case DWC_DDR5_7600AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7600AN=y", NULL);
            break;
            case DWC_DDR5_7600B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7600B=y", NULL);
            break;
            case DWC_DDR5_7600BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7600BN=y", NULL);
            break;
            case DWC_DDR5_7600C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7600C=y", NULL);
            break;
            case DWC_DDR5_8000AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8000AN=y", NULL);
            break;
            case DWC_DDR5_8000B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8000B=y", NULL);
            break;
            case DWC_DDR5_8000BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8000BN=y", NULL);
            break;
            case DWC_DDR5_8000C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8000C=y", NULL);
            break;
            case DWC_DDR5_8400AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8400AN=y", NULL);
            break;
            case DWC_DDR5_8400B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8400B=y", NULL);
            break;
            case DWC_DDR5_8400BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8400BN=y", NULL);
            break;
            case DWC_DDR5_8400C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8400C=y", NULL);
            break;
            case DWC_DDR5_8800AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8800AN=y", NULL);
            break;
            case DWC_DDR5_8800B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8800B=y", NULL);
            break;
            case DWC_DDR5_8800BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8800BN=y", NULL);
            break;
            case DWC_DDR5_8800C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8800C=y", NULL);
            break;
            case DWC_DDR5_3200AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3200AN_3DS=y", NULL);
            break;
            case DWC_DDR5_3200B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3200B_3DS=y", NULL);
            break;
            case DWC_DDR5_3200BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3200BN_3DS=y", NULL);
            break;
            case DWC_DDR5_3200C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3200C_3DS=y", NULL);
            break;
            case DWC_DDR5_3600AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3600AN_3DS=y", NULL);
            break;
            case DWC_DDR5_3600B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3600B_3DS=y", NULL);
            break;
            case DWC_DDR5_3600BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3600BN_3DS=y", NULL);
            break;
            case DWC_DDR5_3600C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_3600C_3DS=y", NULL);
            break;
            case DWC_DDR5_4000AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4000AN_3DS=y", NULL);
            break;
            case DWC_DDR5_4000B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4000B_3DS=y", NULL);
            break;
            case DWC_DDR5_4000BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4000BN_3DS=y", NULL);
            break;
            case DWC_DDR5_4000C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4000C_3DS=y", NULL);
            break;
            case DWC_DDR5_4400AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4400AN_3DS=y", NULL);
            break;
            case DWC_DDR5_4400B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4400B_3DS=y", NULL);
            break;
            case DWC_DDR5_4400BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4400BN_3DS=y", NULL);
            break;
            case DWC_DDR5_4400C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4400C_3DS=y", NULL);
            break;
            case DWC_DDR5_4800AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4800AN_3DS=y", NULL);
            break;
            case DWC_DDR5_4800B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4800B_3DS=y", NULL);
            break;
            case DWC_DDR5_4800BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4800BN_3DS=y", NULL);
            break;
            case DWC_DDR5_4800C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_4800C_3DS=y", NULL);
            break;
            case DWC_DDR5_5200AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5200AN_3DS=y", NULL);
            break;
            case DWC_DDR5_5200B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5200B_3DS=y", NULL);
            break;
            case DWC_DDR5_5200BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5200BN_3DS=y", NULL);
            break;
            case DWC_DDR5_5200C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5200C_3DS=y", NULL);
            break;
            case DWC_DDR5_5600AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5600AN_3DS=y", NULL);
            break;
            case DWC_DDR5_5600B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5600B_3DS=y", NULL);
            break;
            case DWC_DDR5_5600BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5600BN_3DS=y", NULL);
            break;
            case DWC_DDR5_5600C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_5600C_3DS=y", NULL);
            break;
            case DWC_DDR5_6000AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6000AN_3DS=y", NULL);
            break;
            case DWC_DDR5_6000B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6000B_3DS=y", NULL);
            break;
            case DWC_DDR5_6000BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6000BN_3DS=y", NULL);
            break;
            case DWC_DDR5_6000C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6000C_3DS=y", NULL);
            break;
            case DWC_DDR5_6400AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6400AN_3DS=y", NULL);
            break;
            case DWC_DDR5_6400B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6400B_3DS=y", NULL);
            break;
            case DWC_DDR5_6400BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6400BN_3DS=y", NULL);
            break;
            case DWC_DDR5_6400C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6400C_3DS=y", NULL);
            break;
            case DWC_DDR5_6800AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6800AN_3DS=y", NULL);
            break;
            case DWC_DDR5_6800B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6800B_3DS=y", NULL);
            break;
            case DWC_DDR5_6800BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6800BN_3DS=y", NULL);
            break;
            case DWC_DDR5_6800C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_6800C_3DS=y", NULL);
            break;
            case DWC_DDR5_7200AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7200AN_3DS=y", NULL);
            break;
            case DWC_DDR5_7200B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7200B_3DS=y", NULL);
            break;
            case DWC_DDR5_7200BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7200BN_3DS=y", NULL);
            break;
            case DWC_DDR5_7200C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7200C_3DS=y", NULL);
            break;
            case DWC_DDR5_7600AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7600AN_3DS=y", NULL);
            break;
            case DWC_DDR5_7600B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7600B_3DS=y", NULL);
            break;
            case DWC_DDR5_7600BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7600BN_3DS=y", NULL);
            break;
            case DWC_DDR5_7600C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_7600C_3DS=y", NULL);
            break;
            case DWC_DDR5_8000AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8000AN_3DS=y", NULL);
            break;
            case DWC_DDR5_8000B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8000B_3DS=y", NULL);
            break;
            case DWC_DDR5_8000BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8000BN_3DS=y", NULL);
            break;
            case DWC_DDR5_8000C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8000C_3DS=y", NULL);
            break;
            case DWC_DDR5_8400AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8400AN_3DS=y", NULL);
            break;
            case DWC_DDR5_8400B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8400B_3DS=y", NULL);
            break;
            case DWC_DDR5_8400BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8400BN_3DS=y", NULL);
            break;
            case DWC_DDR5_8400C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8400C_3DS=y", NULL);
            break;
            case DWC_DDR5_8800AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8800AN_3DS=y", NULL);
            break;
            case DWC_DDR5_8800B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8800B_3DS=y", NULL);
            break;
            case DWC_DDR5_8800BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8800BN_3DS=y", NULL);
            break;
            case DWC_DDR5_8800C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_0_8800C_3DS=y", NULL);
            break;
            case DWC_DDR5_2100:
            case DWC_DDR5_MONO_LAST_SG:
            case DWC_DDR5_3DS_FIRST_SG:
            case DWC_DDR5_3DS_LAST_SG:
            default:
                SNPS_ERROR("Invalid sg used: %d", SPD.ddr5_speed_bin[0]);
            break;
        }
#if DWC_DDRCTL_DEV_CFG_NUM > 1
        SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SPEED_GRADE_1=%u", SPD.ddr5_speed_bin[1]);
        switch(SPD.ddr5_speed_bin[1])
        {
            case DWC_DDR5_3200AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3200AN=y", NULL);
            break;
            case DWC_DDR5_3200B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3200B=y", NULL);
            break;
            case DWC_DDR5_3200BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3200BN=y", NULL);
            break;
            case DWC_DDR5_3200C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3200C=y", NULL);
            break;
            case DWC_DDR5_3600AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3600AN=y", NULL);
            break;
            case DWC_DDR5_3600B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3600B=y", NULL);
            break;
            case DWC_DDR5_3600BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3600BN=y", NULL);
            break;
            case DWC_DDR5_3600C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3600C=y", NULL);
            break;
            case DWC_DDR5_4000AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4000AN=y", NULL);
            break;
            case DWC_DDR5_4000B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4000B=y", NULL);
            break;
            case DWC_DDR5_4000BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4000BN=y", NULL);
            break;
            case DWC_DDR5_4000C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4000C=y", NULL);
            break;
            case DWC_DDR5_4400AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4400AN=y", NULL);
            break;
            case DWC_DDR5_4400B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4400B=y", NULL);
            break;
            case DWC_DDR5_4400BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4400BN=y", NULL);
            break;
            case DWC_DDR5_4400C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4400C=y", NULL);
            break;
            case DWC_DDR5_4800AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4800AN=y", NULL);
            break;
            case DWC_DDR5_4800B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4800B=y", NULL);
            break;
            case DWC_DDR5_4800BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4800BN=y", NULL);
            break;
            case DWC_DDR5_4800C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4800C=y", NULL);
            break;
            case DWC_DDR5_5200AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5200AN=y", NULL);
            break;
            case DWC_DDR5_5200B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5200B=y", NULL);
            break;
            case DWC_DDR5_5200BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5200BN=y", NULL);
            break;
            case DWC_DDR5_5200C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5200C=y", NULL);
            break;
            case DWC_DDR5_5600AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5600AN=y", NULL);
            break;
            case DWC_DDR5_5600B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5600B=y", NULL);
            break;
            case DWC_DDR5_5600BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5600BN=y", NULL);
            break;
            case DWC_DDR5_5600C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5600C=y", NULL);
            break;
            case DWC_DDR5_6000AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6000AN=y", NULL);
            break;
            case DWC_DDR5_6000B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6000B=y", NULL);
            break;
            case DWC_DDR5_6000BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6000BN=y", NULL);
            break;
            case DWC_DDR5_6000C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6000C=y", NULL);
            break;
            case DWC_DDR5_6400AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6400AN=y", NULL);
            break;
            case DWC_DDR5_6400B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6400B=y", NULL);
            break;
            case DWC_DDR5_6400BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6400BN=y", NULL);
            break;
            case DWC_DDR5_6400C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6400C=y", NULL);
            break;
            case DWC_DDR5_6800AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6800AN=y", NULL);
            break;
            case DWC_DDR5_6800B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6800B=y", NULL);
            break;
            case DWC_DDR5_6800BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6800BN=y", NULL);
            break;
            case DWC_DDR5_6800C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6800C=y", NULL);
            break;
            case DWC_DDR5_7200AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7200AN=y", NULL);
            break;
            case DWC_DDR5_7200B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7200B=y", NULL);
            break;
            case DWC_DDR5_7200BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7200BN=y", NULL);
            break;
            case DWC_DDR5_7200C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7200C=y", NULL);
            break;
            case DWC_DDR5_7600AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7600AN=y", NULL);
            break;
            case DWC_DDR5_7600B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7600B=y", NULL);
            break;
            case DWC_DDR5_7600BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7600BN=y", NULL);
            break;
            case DWC_DDR5_7600C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7600C=y", NULL);
            break;
            case DWC_DDR5_8000AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8000AN=y", NULL);
            break;
            case DWC_DDR5_8000B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8000B=y", NULL);
            break;
            case DWC_DDR5_8000BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8000BN=y", NULL);
            break;
            case DWC_DDR5_8000C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8000C=y", NULL);
            break;
            case DWC_DDR5_8400AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8400AN=y", NULL);
            break;
            case DWC_DDR5_8400B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8400B=y", NULL);
            break;
            case DWC_DDR5_8400BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8400BN=y", NULL);
            break;
            case DWC_DDR5_8400C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8400C=y", NULL);
            break;
            case DWC_DDR5_8800AN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8800AN=y", NULL);
            break;
            case DWC_DDR5_8800B:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8800B=y", NULL);
            break;
            case DWC_DDR5_8800BN:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8800BN=y", NULL);
            break;
            case DWC_DDR5_8800C:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8800C=y", NULL);
            break;
            case DWC_DDR5_3200AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3200AN_3DS=y", NULL);
            break;
            case DWC_DDR5_3200B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3200B_3DS=y", NULL);
            break;
            case DWC_DDR5_3200BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3200BN_3DS=y", NULL);
            break;
            case DWC_DDR5_3200C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3200C_3DS=y", NULL);
            break;
            case DWC_DDR5_3600AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3600AN_3DS=y", NULL);
            break;
            case DWC_DDR5_3600B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3600B_3DS=y", NULL);
            break;
            case DWC_DDR5_3600BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3600BN_3DS=y", NULL);
            break;
            case DWC_DDR5_3600C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_3600C_3DS=y", NULL);
            break;
            case DWC_DDR5_4000AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4000AN_3DS=y", NULL);
            break;
            case DWC_DDR5_4000B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4000B_3DS=y", NULL);
            break;
            case DWC_DDR5_4000BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4000BN_3DS=y", NULL);
            break;
            case DWC_DDR5_4000C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4000C_3DS=y", NULL);
            break;
            case DWC_DDR5_4400AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4400AN_3DS=y", NULL);
            break;
            case DWC_DDR5_4400B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4400B_3DS=y", NULL);
            break;
            case DWC_DDR5_4400BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4400BN_3DS=y", NULL);
            break;
            case DWC_DDR5_4400C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4400C_3DS=y", NULL);
            break;
            case DWC_DDR5_4800AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4800AN_3DS=y", NULL);
            break;
            case DWC_DDR5_4800B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4800B_3DS=y", NULL);
            break;
            case DWC_DDR5_4800BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4800BN_3DS=y", NULL);
            break;
            case DWC_DDR5_4800C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_4800C_3DS=y", NULL);
            break;
            case DWC_DDR5_5200AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5200AN_3DS=y", NULL);
            break;
            case DWC_DDR5_5200B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5200B_3DS=y", NULL);
            break;
            case DWC_DDR5_5200BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5200BN_3DS=y", NULL);
            break;
            case DWC_DDR5_5200C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5200C_3DS=y", NULL);
            break;
            case DWC_DDR5_5600AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5600AN_3DS=y", NULL);
            break;
            case DWC_DDR5_5600B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5600B_3DS=y", NULL);
            break;
            case DWC_DDR5_5600BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5600BN_3DS=y", NULL);
            break;
            case DWC_DDR5_5600C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_5600C_3DS=y", NULL);
            break;
            case DWC_DDR5_6000AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6000AN_3DS=y", NULL);
            break;
            case DWC_DDR5_6000B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6000B_3DS=y", NULL);
            break;
            case DWC_DDR5_6000BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6000BN_3DS=y", NULL);
            break;
            case DWC_DDR5_6000C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6000C_3DS=y", NULL);
            break;
            case DWC_DDR5_6400AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6400AN_3DS=y", NULL);
            break;
            case DWC_DDR5_6400B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6400B_3DS=y", NULL);
            break;
            case DWC_DDR5_6400BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6400BN_3DS=y", NULL);
            break;
            case DWC_DDR5_6400C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6400C_3DS=y", NULL);
            break;
            case DWC_DDR5_6800AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6800AN_3DS=y", NULL);
            break;
            case DWC_DDR5_6800B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6800B_3DS=y", NULL);
            break;
            case DWC_DDR5_6800BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6800BN_3DS=y", NULL);
            break;
            case DWC_DDR5_6800C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_6800C_3DS=y", NULL);
            break;
            case DWC_DDR5_7200AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7200AN_3DS=y", NULL);
            break;
            case DWC_DDR5_7200B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7200B_3DS=y", NULL);
            break;
            case DWC_DDR5_7200BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7200BN_3DS=y", NULL);
            break;
            case DWC_DDR5_7200C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7200C_3DS=y", NULL);
            break;
            case DWC_DDR5_7600AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7600AN_3DS=y", NULL);
            break;
            case DWC_DDR5_7600B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7600B_3DS=y", NULL);
            break;
            case DWC_DDR5_7600BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7600BN_3DS=y", NULL);
            break;
            case DWC_DDR5_7600C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_7600C_3DS=y", NULL);
            break;
            case DWC_DDR5_8000AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8000AN_3DS=y", NULL);
            break;
            case DWC_DDR5_8000B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8000B_3DS=y", NULL);
            break;
            case DWC_DDR5_8000BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8000BN_3DS=y", NULL);
            break;
            case DWC_DDR5_8000C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8000C_3DS=y", NULL);
            break;
            case DWC_DDR5_8400AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8400AN_3DS=y", NULL);
            break;
            case DWC_DDR5_8400B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8400B_3DS=y", NULL);
            break;
            case DWC_DDR5_8400BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8400BN_3DS=y", NULL);
            break;
            case DWC_DDR5_8400C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8400C_3DS=y", NULL);
            break;
            case DWC_DDR5_8800AN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8800AN_3DS=y", NULL);
            break;
            case DWC_DDR5_8800B_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8800B_3DS=y", NULL);
            break;
            case DWC_DDR5_8800BN_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8800BN_3DS=y", NULL);
            break;
            case DWC_DDR5_8800C_3DS:
                SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_SG_1_8800C_3DS=y", NULL);
            break;
            case DWC_DDR5_2100:
            case DWC_DDR5_MONO_LAST_SG:
            case DWC_DDR5_3DS_FIRST_SG:
            case DWC_DDR5_3DS_LAST_SG:
            default:
                SNPS_ERROR("Invalid sg used: %d", SPD.ddr5_speed_bin[1]);
            break;
        }
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 1 */
    }
#endif /* DDRCTL_DDR */
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_NUM_RANKS=%u", SPD.num_ranks);
    switch(SPD.num_ranks)
    {
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_NUM_RANKS_1_RANK=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_NUM_RANKS_2_RANK=y", NULL);
        break;
        case 4:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_NUM_RANKS_4_RANK=y", NULL);
        break;
        case 8:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_NUM_RANKS_8_RANK=y", NULL);
        break;
    }

    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_0=%u", SPD.sdram_width_bits[0]);
    switch(SPD.sdram_width_bits[0])
    {
        case 4:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_0_4_BITS=y", NULL);
        break;
        case 8:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_0_8_BITS=y", NULL);
        break;
        case 16:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_0_16_BITS=y", NULL);
        break;
        case 32:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_0_32_BITS=y", NULL);
        break;
    }
#if DWC_DDRCTL_DEV_CFG_NUM > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_1=%u", SPD.sdram_width_bits[1]);
    switch(SPD.sdram_width_bits[1])
    {
        case 4:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_1_4_BITS=y", NULL);
        break;
        case 8:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_1_8_BITS=y", NULL);
        break;
        case 16:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_1_16_BITS=y", NULL);
        break;
        case 32:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_WIDTH_BITS_1_32_BITS=y", NULL);
        break;
    }
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 1 */
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBITS_0=%u", SPD.sdram_capacity_mbits[0]);
    switch(SPD.sdram_capacity_mbits[0])
    {
        case 1024:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_1_GB=y", NULL);
        break;
        case 2048:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_2_GB=y", NULL);
        break;
        case 4096:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_4_GB=y", NULL);
        break;
        case 6144:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_6_GB=y", NULL);
        break;
        case 8192:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_8_GB=y", NULL);
        break;
        case 12288:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_12_GB=y", NULL);
        break;
        case 16384:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_16_GB=y", NULL);
        break;
        case 24576:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_24_GB=y", NULL);
        break;
        case 32768:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_32_GB=y", NULL);
        break;
        case 65536:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_0_64_GB=y", NULL);
        break;
    }
#if DWC_DDRCTL_DEV_CFG_NUM > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBITS_1=%u", SPD.sdram_capacity_mbits[1]);
    switch(SPD.sdram_capacity_mbits[0])
    {
        case 1024:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_1_GB=y", NULL);
        break;
        case 2048:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_2_GB=y", NULL);
        break;
        case 4096:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_4_GB=y", NULL);
        break;
        case 6144:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_6_GB=y", NULL);
        break;
        case 8192:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_8_GB=y", NULL);
        break;
        case 12288:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_12_GB=y", NULL);
        break;
        case 16384:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_16_GB=y", NULL);
        break;
        case 24576:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_24_GB=y", NULL);
        break;
        case 32768:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_32_GB=y", NULL);
        break;
        case 65536:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_CAPACITY_MBIT_1_64_GB=y", NULL);
        break;
    }
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 1 */

    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_COL_ADDRESSES_0=%u", SPD.dram_caw[0]);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ROW_ADDRESSES_0=%u", SPD.dram_raw[0]);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BANK_ADDRESS_0=%u", SPD.dram_baw[0]);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_0=%u", SPD.dram_bgw[0]);

#if DWC_DDRCTL_DEV_CFG_NUM > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_COL_ADDRESSES_1=%u", SPD.dram_caw[1]);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ROW_ADDRESSES_1=%u", SPD.dram_raw[1]);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BANK_ADDRESS_1=%u", SPD.dram_baw[1]);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BANK_GROUP_ADDRESS_1=%u", SPD.dram_bgw[1]);
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 1 */

    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CID_WIDTH_0=%u", SPD.cid_width[0]);
    switch(SPD.cid_width[0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CID_WIDTH_0_NON_3DS=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CID_WIDTH_0_2H=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CID_WIDTH_0_4H=y", NULL);
        break;
    }
#if DWC_DDRCTL_DEV_CFG_NUM > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CID_WIDTH_1=%u", SPD.cid_width[1]);
    switch(SPD.cid_width[1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CID_WIDTH_1_NON_3DS=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CID_WIDTH_1_2H=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CID_WIDTH_1_4H=y", NULL);
        break;
    }
#endif /* DWC_DDRCTL_DEV_CFG_NUM > 1 */

    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_USE_DDR4_TCWL1ST_SET=%u", SPD.use_ddr4_tcwl_1st_set);
    switch(SPD.use_ddr4_tcwl_1st_set)
    {
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_USE_DDR4_TCWL1ST_SET_LOW_SET=y", NULL);
        break;
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_USE_DDR4_TCWL1ST_SET_UPPER_SET=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TAL=%u", SPD.tAL);
    switch(SPD.tAL)
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TAL_0=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TAL_1=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TAL_2=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_NUM_DIMM=%u", SPD.num_dimm);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_0=%u", SPD.tck_ps[0]);

#if UMCTL2_FREQUENCY_NUM > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_1=%u", SPD.tck_ps[1]);
#endif /* UMCTL2_FREQUENCY_NUM > 1 */
#if UMCTL2_FREQUENCY_NUM > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_2=%u", SPD.tck_ps[2]);
#endif /* UMCTL2_FREQUENCY_NUM > 2 */
#if UMCTL2_FREQUENCY_NUM > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_3=%u", SPD.tck_ps[3]);
#endif /* UMCTL2_FREQUENCY_NUM > 3 */
#if UMCTL2_FREQUENCY_NUM > 4
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_4=%u", SPD.tck_ps[4]);
#endif /* UMCTL2_FREQUENCY_NUM > 4 */
#if UMCTL2_FREQUENCY_NUM > 5
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_5=%u", SPD.tck_ps[5]);
#endif /* UMCTL2_FREQUENCY_NUM > 5 */
#if UMCTL2_FREQUENCY_NUM > 6
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_6=%u", SPD.tck_ps[6]);
#endif /* UMCTL2_FREQUENCY_NUM > 6 */
#if UMCTL2_FREQUENCY_NUM > 7
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_7=%u", SPD.tck_ps[7]);
#endif /* UMCTL2_FREQUENCY_NUM > 7 */
#if UMCTL2_FREQUENCY_NUM > 8
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_8=%u", SPD.tck_ps[8]);
#endif /* UMCTL2_FREQUENCY_NUM > 8 */
#if UMCTL2_FREQUENCY_NUM > 9
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_9=%u", SPD.tck_ps[9]);
#endif /* UMCTL2_FREQUENCY_NUM > 9 */
#if UMCTL2_FREQUENCY_NUM > 10
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_10=%u", SPD.tck_ps[10]);
#endif /* UMCTL2_FREQUENCY_NUM > 10 */
#if UMCTL2_FREQUENCY_NUM > 11
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_11=%u", SPD.tck_ps[11]);
#endif /* UMCTL2_FREQUENCY_NUM > 11 */
#if UMCTL2_FREQUENCY_NUM > 12
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_12=%u", SPD.tck_ps[12]);
#endif /* UMCTL2_FREQUENCY_NUM > 12 */
#if UMCTL2_FREQUENCY_NUM > 13
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCK_PS_13=%u", SPD.tck_ps[13]);
#endif /* UMCTL2_FREQUENCY_NUM > 13 */


    SNPS_INPUT("CONFIG_NUM_PSTATES=%u", CFG->num_pstates);

    SNPS_INPUT("CONFIG_CONFIG_NUM_PSTATES_%u=y", CFG->num_pstates);
    SNPS_INPUT("CONFIG_NUM_AMAP=%u", CFG->num_amap);
    SNPS_INPUT("CONFIG_CONFIG_NUM_AMAP_%u=y", CFG->num_amap);
    SNPS_INPUT("CONFIG_NUM_DCH=%u", CFG->num_dch);
    SNPS_INPUT("CONFIG_CONFIG_NUM_DCH_%u=y", CFG->num_dch);
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDRPHYTYPE_M=%u", CFG->ddrPhyType_m);
    switch(CFG->ddrPhyType_m)
    {
        case 1:
            SNPS_INPUT("CONFIG_CONFIG_DWC_DDR54_TYPE_PHY=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_CONFIG_DWC_LPDDR54_TYPE_PHY=y", NULL);
        break;
        case 3:
            SNPS_INPUT("CONFIG_CONFIG_DWC_DDR54_TYPE_PHY_V2=y", NULL);
        break;
        case 4:
            SNPS_INPUT("CONFIG_CONFIG_DWC_LPDDR5X4_TYPE_PHY=y", NULL);
        break;
	case 5:
            SNPS_INPUT("CONFIG_CONFIG_DWC_DDR5_TYPE_PHY=y", NULL);
        break;
	case 6:
            SNPS_INPUT("CONFIG_CONFIG_DWC_3RD_PARTY_TYPE_PHY=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_PHY_TRAINING=%u", CFG->phy_training);
    switch(CFG->phy_training)
    {
        case 0:
            SNPS_INPUT("CONFIG_CONFIG_DWC_FULL_TRAINING=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_CONFIG_DWC_SKIP_TRAINING=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_CONFIG_DWC_DEVICE_PHY=y", NULL);
        break;
    }
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 0
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_0=%u", CFG->lut_entry[0]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_1=%u", CFG->lut_entry[1]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_2=%u", CFG->lut_entry[2]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_3=%u", CFG->lut_entry[3]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 4
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_4=%u", CFG->lut_entry[4]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 5
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_5=%u", CFG->lut_entry[5]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 6
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_6=%u", CFG->lut_entry[6]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 7
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_7=%u", CFG->lut_entry[7]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 8
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_8=%u", CFG->lut_entry[8]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 9
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_9=%u", CFG->lut_entry[9]);
#endif

#if DWC_DDRCTL_MAX_LUT_ENTRIES > 10
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_10=%u", CFG->lut_entry[10]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 11
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_11=%u", CFG->lut_entry[11]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 12
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_12=%u", CFG->lut_entry[12]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 13
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_13=%u", CFG->lut_entry[13]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 14
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_14=%u", CFG->lut_entry[14]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 15
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_15=%u", CFG->lut_entry[15]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 16
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_16=%u", CFG->lut_entry[16]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 17
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_17=%u", CFG->lut_entry[17]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 18
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_18=%u", CFG->lut_entry[18]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 19
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_19=%u", CFG->lut_entry[19]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 20
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_20=%u", CFG->lut_entry[20]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 21
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_21=%u", CFG->lut_entry[21]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 22
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_22=%u", CFG->lut_entry[22]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 23
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_23=%u", CFG->lut_entry[23]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 24
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_24=%u", CFG->lut_entry[24]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 25
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_25=%u", CFG->lut_entry[25]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 26
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_26=%u", CFG->lut_entry[26]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 27
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_27=%u", CFG->lut_entry[27]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 28
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_28=%u", CFG->lut_entry[28]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 29
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_29=%u", CFG->lut_entry[29]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 30
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_30=%u", CFG->lut_entry[30]);
#endif
#if DWC_DDRCTL_MAX_LUT_ENTRIES > 31
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_LUT_ENTRY_31=%u", CFG->lut_entry[31]);
#endif

    SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_WR=%u", PHY_TIMING.pipe_dfi_wr);
    switch(PHY_TIMING.pipe_dfi_wr)
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_WR_NOT_DEFINED=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_WR_DEFINED=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_RD=%u", PHY_TIMING.pipe_dfi_rd);
    switch(PHY_TIMING.pipe_dfi_rd)
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_RD_NOT_DEFINED=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_RD_DEFINED=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_MISC=%u", PHY_TIMING.pipe_dfi_misc);
    switch(PHY_TIMING.pipe_dfi_misc)
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_MISC_NOT_DEFINED=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRPHY_PIPE_DFI_MISC_DEFINED=y", NULL);
        break;
    }

#ifdef DDRCTL_DDR
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_RC0F_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD=%u", CFG->ddr4_cw.rc0f.latency_adder_nladd_to_all_dram_cmd);
    switch(CFG->ddr4_cw.rc0f.latency_adder_nladd_to_all_dram_cmd)
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_RC0F_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD_0=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_RC0F_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD_1=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_RC0F_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD_2=y", NULL);
        break;
        case 3:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_RC0F_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD_3=y", NULL);
        break;
        case 4:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_RC0F_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD_4=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_RW11_LATENCY_ADDER_NLADD_TO_ALL_DRAM_CMD=%u", CFG->ddr5_cw.rw11.latency_adder_nladd_to_all_dram_cmd);

    SNPS_INPUT("DWC_DDRCTL_CINIT_RW00_SDR_MODE=%u", CFG->ddr5_cw.rw00.sdr_mode);
    switch(CFG->ddr5_cw.rw00.sdr_mode)
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_RW00_SDR_MODE1=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_DDR5_RW00_SDR_MODE2=y", NULL);
        break;
    }

    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BASE_TIMER_INTERVAL_US_0=%u", CFG->ddr5_pasdu_en.base_timer_interval_us[0]);
    switch(CFG->ddr5_pasdu_en.base_timer_interval_us[0])
    {
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BASE_TIMER_INTERVAL_US_0_1=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BASE_TIMER_INTERVAL_US_0_2=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BASE_TIMER_INTERVAL_US_1=%u", CFG->ddr5_pasdu_en.base_timer_interval_us[1]);
    switch(CFG->ddr5_pasdu_en.base_timer_interval_us[1])
    {
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BASE_TIMER_INTERVAL_US_1_1=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_BASE_TIMER_INTERVAL_US_1_2=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_0=%u", CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][0]);
    switch(CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_0_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_0_ENABLE=y", NULL);
        break;
    }
#if MEMC_NUM_RANKS > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_1=%u", CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][1]);
    switch(CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_1_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_1_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 1 */
#if MEMC_NUM_RANKS > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_2=%u", CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][2]);
    switch(CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][2])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_2_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_2_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 2 */
#if MEMC_NUM_RANKS > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_3=%u", CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][3]);
    switch(CFG->ddr5_pasdu_en.tcr_dqsosc_en[0][3])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_3_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_0_3_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 3 */
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_0=%u", CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][0]);
    switch(CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_0_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_0_ENABLE=y", NULL);
        break;
    }
#if MEMC_NUM_RANKS > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_1=%u", CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][1]);
    switch(CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_1_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_1_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 1 */
#if MEMC_NUM_RANKS > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_2=%u", CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][2]);
    switch(CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][2])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_2_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_2_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 2 */
#if MEMC_NUM_RANKS > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_3=%u", CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][3]);
    switch(CFG->ddr5_pasdu_en.tcr_dqsosc_en[1][3])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_3_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_TCR_DQSOSC_EN_1_3_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 3 */
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1 */
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ALL_RANK_ZQCAL_EN_0=%u", CFG->ddr5_pasdu_en.all_rank_zqcal_en[0]);
    switch(CFG->ddr5_pasdu_en.all_rank_zqcal_en[0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ALL_RANK_ZQCAL_EN_0_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ALL_RANK_ZQCAL_EN_0_ENABLE=y", NULL);
        break;
    }
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ALL_RANK_ZQCAL_EN_1=%u", CFG->ddr5_pasdu_en.all_rank_zqcal_en[1]);
    switch(CFG->ddr5_pasdu_en.all_rank_zqcal_en[1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ALL_RANK_ZQCAL_EN_1_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_ALL_RANK_ZQCAL_EN_1_ENABLE=y", NULL);
        break;
    }
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1 */
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_0=%u", CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][0]);
    switch(CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_0_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_0_ENABLE=y", NULL);
        break;
    }
#if MEMC_NUM_RANKS > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_1=%u", CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][1]);
        switch(CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_1_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_1_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 1 */
#if MEMC_NUM_RANKS > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_2=%u", CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][2]);
        switch(CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][2])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_2_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_2_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 2 */
#if MEMC_NUM_RANKS > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_3=%u", CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][3]);
    switch(CFG->ddr5_pasdu_en.per_rank_zqcal_en[0][3])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_3_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_0_3_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 3 */
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_0=%u", CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][0]);
    switch(CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_0_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_0_ENABLE=y", NULL);
        break;
    }
#if MEMC_NUM_RANKS > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_1=%u", CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][1]);
    switch(CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_1_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_1_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 1 */
#if MEMC_NUM_RANKS > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_2=%u", CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][2]);
    switch(CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][2])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_2_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_2_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 2 */
#if MEMC_NUM_RANKS > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_3=%u", CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][3]);
    switch(CFG->ddr5_pasdu_en.per_rank_zqcal_en[1][3])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_3_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ZQCAL_EN_1_3_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 3 */
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1 */
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CTLUPD_EN_0=%u", CFG->ddr5_pasdu_en.ctlupd_en[0]);
    switch(CFG->ddr5_pasdu_en.ctlupd_en[0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CTLUPD_EN_0_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CTLUPD_EN_0_ENABLE=y", NULL);
        break;
    }
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CTLUPD_EN_1=%u", CFG->ddr5_pasdu_en.ctlupd_en[1]);
    switch(CFG->ddr5_pasdu_en.ctlupd_en[1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CTLUPD_EN_1_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CTLUPD_EN_1_ENABLE=y", NULL);
        break;
    }
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1 */
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_0=%u", CFG->ddr5_pasdu_en.per_rank_ecs_en[0][0]);
    switch(CFG->ddr5_pasdu_en.per_rank_ecs_en[0][0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_0_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_0_ENABLE=y", NULL);
        break;
    }
#if MEMC_NUM_RANKS > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_1=%u", CFG->ddr5_pasdu_en.per_rank_ecs_en[0][1]);
    switch(CFG->ddr5_pasdu_en.per_rank_ecs_en[0][1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_1_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_1_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 1 */
#if MEMC_NUM_RANKS > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_2=%u", CFG->ddr5_pasdu_en.per_rank_ecs_en[0][2]);
    switch(CFG->ddr5_pasdu_en.per_rank_ecs_en[0][2])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_2_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_2_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 2 */
#if MEMC_NUM_RANKS > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_3=%u", CFG->ddr5_pasdu_en.per_rank_ecs_en[0][3]);
    switch(CFG->ddr5_pasdu_en.per_rank_ecs_en[0][3])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_3_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_0_3_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 3 */
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_0=%u", CFG->ddr5_pasdu_en.per_rank_ecs_en[1][0]);
    switch(CFG->ddr5_pasdu_en.per_rank_ecs_en[1][0])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_0_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_0_ENABLE=y", NULL);
        break;
    }
#if MEMC_NUM_RANKS > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_1=%u", CFG->ddr5_pasdu_en.per_rank_ecs_en[1][1]);
    switch(CFG->ddr5_pasdu_en.per_rank_ecs_en[1][1])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_1_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_1_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 1 */
#if MEMC_NUM_RANKS > 2
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_2=%u", CFG->ddr5_pasdu_en.per_rank_ecs_en[1][2]);
    switch(CFG->ddr5_pasdu_en.per_rank_ecs_en[1][2])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_2_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_2_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 2 */
#if MEMC_NUM_RANKS > 3
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_3=%u", CFG->ddr5_pasdu_en.per_rank_ecs_en[1][3]);
    switch(CFG->ddr5_pasdu_en.per_rank_ecs_en[1][3])
    {
        case 0:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_3_DISABLE=y", NULL);
        break;
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_PER_RANK_ECS_EN_1_3_ENABLE=y", NULL);
        break;
    }
#endif /* MEMC_NUM_RANKS > 3 */
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1 */
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_0_0=%u", CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[0][0]);
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_0_1=%u", CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[0][1]);
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1*/
#if UMCTL2_FREQUENCY_NUM > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_1_0=%u", CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[1][0]);
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_T_CCD_W_OFFSET_1_1=%u", CFG->ddr5_interamble_tccd_offset.t_ccd_w_offset[1][1]);
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1 */
#endif /* UMCTL2_FREQUENCY_NUM > 1*/
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_0_0=%u", CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[0][0]);
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_0_1=%u", CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[0][1]);
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1*/
#if UMCTL2_FREQUENCY_NUM > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_1_0=%u", CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[1][0]);
#if DWC_DDRCTL_NUM_CHANNEL > 1
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_T_CCD_R_OFFSET_1_1=%u", CFG->ddr5_interamble_tccd_offset.t_ccd_r_offset[1][1]);
#endif /* DWC_DDRCTL_NUM_CHANNEL > 1 */
#endif /* UMCTL2_FREQUENCY_NUM > 1*/
#endif /* DDRCTL_DDR */
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_BUS_WIDTH=%u", CFG->memCtrlr_m.sdram_bus_width);
    switch(CFG->memCtrlr_m.sdram_bus_width)
    {
        case 1:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_BUS_WIDTH_FULL=y", NULL);
        break;
        case 2:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_BUS_WIDTH_HALF=y", NULL);
        break;
        case 3:
            SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_SDRAM_BUS_WIDTH_QUARTER=y", NULL);
        break;
    }
    SNPS_INPUT("CONFIG_DWC_DDRCTL_CINIT_CAPAR_RETRY_WINDOW_INTERNAL_DELAY_EXTRA=%u", CFG->capar_retry_window_internal_delay_extra);
}

