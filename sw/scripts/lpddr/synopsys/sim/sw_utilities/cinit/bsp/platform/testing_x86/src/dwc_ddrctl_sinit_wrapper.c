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

void dwc_ddrphy_cinit_cpu_dpi_main(SubsysHdlr_t *phdlr, dwc_ddrctl_cinit_seq_e cinit_seq);


typedef enum ddrctl_seq_e{
    DDRCTL_SEQ_INITIALIZATION           =  1,
    DDRCTL_SEQ_CLK_REMOVAL              =  2,
    DDRCTL_SEQ_PWR_REMOVAL              =  3,
    DDRCTL_SEQ_MPSM                     =  4,
    DDRCTL_SEQ_DDR5_FGR                 =  5,
    DDRCTL_SEQ_LPDDR5_DSM               =  6,
    DDRCTL_SEQ_SWFFC_WITH_FSP           =  7,
    DDRCTL_SEQ_SWFFC_WITH_NO_FSP        =  8,
    DDRCTL_SEQ_LPDDR5_RFM_LEVEL         =  9,
    DDRCTL_SEQ_LPDDR5_SREF_RETRAIN_PPT2 = 10
} ddrctl_seq_t;


static const char *get_ddrctl_seq_str(ddrctl_seq_t seq)
{
    switch (seq) {
        case DDRCTL_SEQ_INITIALIZATION:
            return "DDRCTL_SEQ_INITIALIZATION";
        case DDRCTL_SEQ_CLK_REMOVAL:
            return "DDRCTL_SEQ_CLK_REMOVAL";
        case DDRCTL_SEQ_PWR_REMOVAL:
            return "DDRCTL_SEQ_PWR_REMOVAL";
        case DDRCTL_SEQ_MPSM:
            return "DDRCTL_SEQ_MPSM";
        case DDRCTL_SEQ_DDR5_FGR:
            return "DDRCTL_SEQ_DDR5_FGR";
        case DDRCTL_SEQ_LPDDR5_DSM:
            return "DDRCTL_SEQ_LPDDR5_DSM";
        case DDRCTL_SEQ_SWFFC_WITH_FSP:
            return "DDRCTL_SEQ_SWFFC_WITH_FSP";
        case DDRCTL_SEQ_SWFFC_WITH_NO_FSP:
            return "DDRCTL_SEQ_SWFFC_WITH_NO_FSP";
        case DDRCTL_SEQ_LPDDR5_RFM_LEVEL:
            return "DDRCTL_SEQ_LPDDR5_RFM_LEVEL";
        case DDRCTL_SEQ_LPDDR5_SREF_RETRAIN_PPT2:
            return "DDRCTL_SEQ_LPDDR5_SREF_RETRAIN_PPT2";
        default:
            return "Unknown sequence";
    }
}

ddrctl_error_t seq_test_wrapper(uint32_t seq)
{
    SubsysHdlr_t  *sinit_config;
    ddrctl_error_t rslt;

    rslt = DDRCTL_SUCCESS;
    sinit_config = (SubsysHdlr_t *) calloc(1, sizeof(SubsysHdlr_t));

    SNPS_WARN("DDRCTL CINIT Begin function");
    dwc_ddrctl_cinit_begin(sinit_config);

    SNPS_WARN("DDRCTL Sequence %s start\n", get_ddrctl_seq_str((ddrctl_seq_t) seq));

    switch ((ddrctl_seq_t) seq) {
        case DDRCTL_SEQ_INITIALIZATION:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_INITIALIZATION);
            break;
        case DDRCTL_SEQ_CLK_REMOVAL:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_CLK_REMOVAL);
            break;
        case DDRCTL_SEQ_PWR_REMOVAL:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_PWR_REMOVAL);
            break;
        case DDRCTL_SEQ_MPSM:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_MPSM);
            break;
        case DDRCTL_SEQ_DDR5_FGR:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_DDR5_FGR);
            break;
        case DDRCTL_SEQ_LPDDR5_DSM:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_LPDDR5_DSM);
            break;
        case DDRCTL_SEQ_SWFFC_WITH_FSP:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_SWFFC_WITH_FSP);
            break;
        case DDRCTL_SEQ_SWFFC_WITH_NO_FSP:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_SWFFC_WITH_NO_FSP);
            break;
        case DDRCTL_SEQ_LPDDR5_RFM_LEVEL:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_LPDDR5_RFM_LEVEL);
            break;
        case DDRCTL_SEQ_LPDDR5_SREF_RETRAIN_PPT2:
            dwc_ddrphy_cinit_cpu_dpi_main(sinit_config, CINIT_SEQ_LPDDR5_SREF_RETRAIN_PPT2);
            break;
        default:
            SNPS_WARN("DDRCTL sequence not found: %s (%d)\n", get_ddrctl_seq_str((ddrctl_seq_t) seq), seq);
            rslt = DDRCTL_NOT_SUPPORTED;
    }

    SNPS_WARN("DDRCTL Sequence %s end\n", get_ddrctl_seq_str((ddrctl_seq_t) seq));

    SNPS_WARN("DDRCTL CINIT End function");
    dwc_ddrctl_cinit_end();

    return rslt;
}
