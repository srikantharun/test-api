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


#ifndef __DWC_DDRCTL_CINIT_TYPES_STR_H__
#define __DWC_DDRCTL_CINIT_TYPES_STR_H__


#include "dwc_ddrctl_cinit_types.h"


static inline const char * ddrctl_sw_get_phy_type_str(ddrPhyType_e phy_type)
{
    switch (phy_type) {
        case DWC_DDR54_PHY:
            return "DDR54";
        case DWC_DDR54_PHY_V2:
            return "DDR54 v2";
        case DWC_DDR5_PHY:
            return "DDR5";
        case DWC_LPDDR54_PHY:
            return "LPDDR54";
        case DWC_LPDDR5X4_PHY:
            return "LPDDR5X4 ";
        case DWC_LPDDR4X_MULTIPHY:
            return "LPDDR4X multiphy";
        default:
            return "Unknown";
    }
}

static inline const char * ddrctl_sw_get_phy_train_str(dwc_ddrctl_phy_training_e phy_train_mode)
{
    switch (phy_train_mode) {
        case DWC_PHY_TRAINING:
            return "Train";
        case DWC_PHY_SKIP_TRAINING:
            return "Skip";
        case DWC_PHY_DEV_INIT:
            return "Dev Init";
        default:
            return "Unknown";
    }
}


static inline const char * ddrctl_sw_get_protocol_str(dwc_sdram_protocol proto_id)
{
    switch (proto_id) {
        case DWC_DDR4:
            return "DDR4";
        case DWC_DDR5:
            return "DDR5";
        case DWC_LPDDR4:
            return "LPDDR4";
        case DWC_LPDDR5:
            return "LPDDR5";
        default:
            return "Unknown";
    }
}


static inline const char * ddrctl_sw_get_module_str(dwc_sdram_module_type module)
{
    switch (module) {
        case DWC_NODIMM:
            return "NODIMM";
        case DWC_RDIMM:
            return "RDIMM";
        case DWC_LRDIMM:
            return "LRDIMM";
        case DWC_UDIMM:
            return "UDIMM";
        default:
            return "Unknown";
    }
}


static inline const char * ddrctl_cinit_pub_msg_str(pub_msg_id_t msg_id)
{
    switch (msg_id) {
        case PUB_MSG_END_OF_INITIALIZATION:
            return "End of initialization";
        case PUB_MSG_END_OF_FINE_WRITE_LEVELING:
            return "End of fine write leveling";
        case PUB_MSG_END_OF_READ_ENABLE_TRAINING:
            return "End of read enable training";
        case PUB_MSG_END_OF_READ_DELAY_CENTER_OPTIMIZATION:
            return "End of read delay center optimization";
        case PUB_MSG_END_OF_WRITE_DELAY_CENTER_OPTIMIZATION:
            return "End of write delay center optimization";
        case PUB_MSG_TRAINING_COMPLETE_PASSED:
            return "Training has run successfully";
        case PUB_MSG_TRAINING_COMPLETE_FAILED:
            return "Training has failed";
        case PUB_MSG_START_STREAMING_MESSAGE_MODE:
            return "Start Streaming message mode";
        case PUB_MSG_END_OF_MAX_READ_LATENCY_TRAINING:
            return "End of max read latency training";
        case PUB_MSG_END_OF_CA_TRAINING:
            return "End of CS/CA training";
        case PUB_MSG_SMBUS_REQUEST:
            return "SMBus request";
        case PUB_MSG_SMBUS_SYNC:
            return "SMBus sync";
        case PUB_MSG_END_OF_WRITE_LEVELING_COARSE_DELAY:
            return "End of write leveling coarse delay";
#ifdef DDRCTL_DDR
        case PUB_MSG_END_OF_2D_READ_DELAY_VOLTAGE_CENTER_OPTIMIZATION:
            return "End of 2D read delay/voltage center optimization";
        case PUB_MSG_END_OF_2D_WRITE_DELAY_VOLTAGE_CENTER_OPTIMIZATION:
            return "End of 2D write delay/voltage center optimization";
        case PUB_MSG_END_OF_READ_DQ_DESKEW_TRAINING:
            return "End of read DQ deskew Training";
        case PUB_MSG_END_OF_LCDL_OFFSET_CALIBRATION:
            return "End of LCDL offset calibration";
        case PUB_MSG_END_OF_RCD_QCS_QCA_TRAINING:
            return "End of RCD QCS/QCA training";
        case PUB_MSG_END_OF_LRDIMM_SPECIFIC_TRAINING:
            return "End of LRDIMM specific training";
        case PUB_MSG_END_OF_LRDIMM_MREP_TRAINING:
            return "End of LRDIMM MREP training";
        case PUB_MSG_END_OF_LRDIMM_DWL_TRAINING:
            return "End of LRDIMM DWL training";
        case PUB_MSG_END_OF_LRDIMM_MRD_TRAINING:
            return "End of LRDIMM MRD training";
        case PUB_MSG_END_OF_LRDIMM_MWD_TRAINING:
            return "End of LRDIMM MWD training";
        case PUB_MSG_END_OF_MEMORY_RESET:
            return "End of memory reset";
        case PUB_MSG_END_OF_MPR_READ_DELAY_CENTER_OPTIMIZATION:
            return "End of MPR read delay center optimization";
#endif // DDRCTL_DDR
#ifdef DDRCTL_LPDDR
        case PUB_MSG_END_OF_RXDIGSTROBE_TRAINING:
            return "End of RXDIGSTrobe training";
        case PUB_MSG_END_OF_DRAM_DCA_TRAINING:
            return "End of DRAM DCA training";
        case PUB_MSG_END_OF_PHY_RX_DCA_TRAINING:
            return "End of Phy Rx DCA training";
        case PUB_MSG_END_OF_PHY_TX_DCA_TRAINING:
            return "End of Phy Tx DCA training";
        case PUB_MSG_END_OF_READ_TRAINING_CENTER_OPTIMIZATION:
            return "End of read training center optimization";
#endif // DDRCTL_LPDDR
        default:
            return "Unknown Msg";
    }
}


static inline const char * ddrctl_sw_get_lpddr4_data_rate_str(dwc_lpddr4_data_rate_e data_rate)
{
    switch (data_rate) {
        case DWC_LPDDR4_533:
            return "533";
        case DWC_LPDDR4_1066:
            return "1066";
        case DWC_LPDDR4_1600:
            return "1600";
        case DWC_LPDDR4_2133:
            return "2133";
        case DWC_LPDDR4_2667:
            return "2667";
        case DWC_LPDDR4_3200:
            return "3200";
        case DWC_LPDDR4_3733:
            return "3733";
        case DWC_LPDDR4_4267:
            return "4267";
        default:
            return "Unknown";
    }
}

static inline const char * ddrctl_sw_get_lpddr5_data_rate_str(dwc_lpddr5_data_rate_e data_rate)
{
    switch (data_rate) {
        case DWC_LPDDR5_533:
            return "533";
        case DWC_LPDDR5_1067:
            return "1067";
        case DWC_LPDDR5_1600:
            return "1600";
        case DWC_LPDDR5_2133:
            return "2133";
        case DWC_LPDDR5_2750:
            return "2750";
        case DWC_LPDDR5_3200:
            return "3200";
        case DWC_LPDDR5_3733:
            return "3733";
        case DWC_LPDDR5_4267:
            return "4267";
        case DWC_LPDDR5_4800:
            return "4800";
        case DWC_LPDDR5_5500:
            return "5500";
        case DWC_LPDDR5_6000:
            return "6000";
        case DWC_LPDDR5_6400:
            return "6400";
        case DWC_LPDDR5_7500:
            return "7500";
        case DWC_LPDDR5_8533:
            return "8533";
        case DWC_LPDDR5_9600:
            return "9600";
        default:
            return "Unknown";
    }
}


static inline const char * ddrctl_sw_get_lpddr5_bk_bg_str(dwc_lpddr5_bk_bg_org_e bk_bg)
{
    switch (bk_bg) {
        case DWC_LPDDR5_4BK_4BG:
            return "4 banks, 4 bank groups";
        case DWC_LPDDR5_8BK:
            return "8 banks";
        case DWC_LPDDR5_16BK:
            return "16 banks";
        default:
            return "Unknown";
    }
}


static inline const char * ddrctl_sw_get_cid_str(uint8_t cid)
{
    switch (cid) {
        case 0:
            return "Non-3DS";
        case 1:
            return "2H 3DS";
        case 2:
            return "4H 3DS";
        default:
            return "Unknown";
    }
}


static inline const char * ddrctl_sw_get_dimm_data_width_str(dwc_ddr5_dimm_ch_arch_e data_width)
{
    switch (data_width) {
        case DATA_CHANNEL_32_BIT:
            return "32 bits (no ECC)";
        case DATA_CHANNEL_36_BIT:
            return "36 bits (32 data + 4 ECC)";
        case DATA_CHANNEL_40_BIT:
            return "40 bits (32 data + 8 ECC)";
        default:
            return "Unknown";
    }
}


static inline const char * ddrctl_sw_get_sdram_bus_width_str(dwc_sdram_bus_width_t bus_width)
{
    switch (bus_width) {
        case DWC_BUSWIDTH_FULL:
            return "Full bus width";
        case DWC_BUSWIDTH_HALF:
            return "Half bus width";
        case DWC_BUSWIDTH_QUARTER:
            return "Quarter bus width";
        default:
            return "Unknown";
    }
}

#endif /* __DWC_DDRCTL_CINIT_TYPES_STR_H__ */
