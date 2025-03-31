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


#ifndef __DWC_DDRCTL_CINIT_TYPES_H__
#define __DWC_DDRCTL_CINIT_TYPES_H__

// The following types are sensitive to the encoding defined in CC constants

/*
 * ! \enum ddr5_jedec_spec_t
 * Defining the DDR5 specs supported,
 * Used in a bitmap, Each version will be identified by the active bit.
 */
typedef enum {
    JESD79_5  = (1 << 0),
    JESD79_5A = (1 << 1),
    JESD79_5B = (1 << 2)
} ddr5_jedec_spec_t;


/**
 * @brief Enum type to define frequency ratio
 * 
 * The values for the ratios must match the TMGCFG.frequency_ratio expected values
 */
typedef enum {
    DWC_RATIO_1_2 = 0,
    DWC_RATIO_1_4 = 1,
    DWC_RATIO_WCK_CK_2_1 = 2,
    DWC_RATIO_WCK_CK_4_1 = 3
} dwc_freq_ratio_t;


/*
 * ! \enum dwc_lpddr4_data_rate_e
 * Encoding LPDDR4 SDRAM speed options in Mbps.
 * The encoding must match the encoding in the cc_constants file
 */
typedef enum tag_dwc_lpddr4_data_rate_e {
    DWC_LPDDR4_533 = 1,
    DWC_LPDDR4_1066 = 2,
    DWC_LPDDR4_1600 = 3,
    DWC_LPDDR4_2133 = 4,
    DWC_LPDDR4_2667 = 5,
    DWC_LPDDR4_3200 = 6,
    DWC_LPDDR4_3733 = 7,
    DWC_LPDDR4_4267 = 8
} dwc_lpddr4_data_rate_e;

/*
 * ! \enum dwc_lpddr5_data_rate_e
 * Encoding of LPDDR5 data rates.
 */
typedef enum tag_dwc_lpddr5_data_rate_e {
    DWC_LPDDR5_533 = 1,
    DWC_LPDDR5_1067 = 2,
    DWC_LPDDR5_1600 = 3,
    DWC_LPDDR5_2133 = 4,
    DWC_LPDDR5_2750 = 5,
    DWC_LPDDR5_3200 = 6,
    DWC_LPDDR5_3733 = 7,
    DWC_LPDDR5_4267 = 8,
    DWC_LPDDR5_4800 = 9,
    DWC_LPDDR5_5500 = 10,
    DWC_LPDDR5_6000 = 11,
    DWC_LPDDR5_6400 = 12,
    DWC_LPDDR5_7500 = 13,
    DWC_LPDDR5_8533 = 14,
    DWC_LPDDR5_9600 = 15
} dwc_lpddr5_data_rate_e;

/*
 * ! \enum dwc_lpddr5_wckck_ratio_e
 * Encoding of LPDDR5 WCK to CK ratio.
 * @deprecated Will be removed as soon all calls from testbench are removed
 */
typedef enum tag_dwc_lpddr5_wckck_ratio_e {
    DWC_WCKCK_2_1 = 1,
    DWC_WCKCK_4_1
} dwc_lpddr5_wckck_ratio_e;

/*
 * ! \enum dwc_lpddr5_bk_bg_org_e
 * Encoding of LPDDDR5 back organization.
 */
typedef enum tag_dwc_lpddr5_bk_bg_org_e {
    DWC_LPDDR5_4BK_4BG = 0,
    DWC_LPDDR5_8BK,
    DWC_LPDDR5_16BK
} dwc_lpddr5_bk_bg_org_e;

typedef enum tag_dwc_ddr4_speed_grade_e {
    DWC_DDR4_MONO_FIRST_SG = 0,
    DWC_DDR4_1600J         = 1,
    DWC_DDR4_1600K         = 2,
    DWC_DDR4_1600L         = 3,
    DWC_DDR4_1866L         = 4,
    DWC_DDR4_1866M         = 5,
    DWC_DDR4_1866N         = 6,
    DWC_DDR4_2133N         = 7,
    DWC_DDR4_2133P         = 8,
    DWC_DDR4_2133R         = 9,
    DWC_DDR4_2400P         = 10,
    DWC_DDR4_2400R         = 11,
    DWC_DDR4_2400T         = 12,
    DWC_DDR4_2400U         = 13,
    DWC_DDR4_2666T         = 14,
    DWC_DDR4_2666U         = 15,
    DWC_DDR4_2666V         = 16,
    DWC_DDR4_2666W         = 17,
    DWC_DDR4_2933V         = 18,
    DWC_DDR4_2933W         = 19,
    DWC_DDR4_2933Y         = 20,
    DWC_DDR4_2933AA        = 21,
    DWC_DDR4_3200W         = 22,
    DWC_DDR4_3200AA        = 23,
    DWC_DDR4_3200AC        = 24,
    DWC_DDR4_MONO_LAST_SG  = 25,
    DWC_DDR4_3DS_FIRST_SG  = 26,
    DWC_DDR4_1600J_3DS2B   = 27,
    DWC_DDR4_1600K_3DS2B   = 28,
    DWC_DDR4_1600L_3DS2B   = 29,
    DWC_DDR4_1866L_3DS2B   = 30,
    DWC_DDR4_1866M_3DS2B   = 31,
    DWC_DDR4_1866N_3DS2B   = 32,
    DWC_DDR4_2133P_3DS2A   = 33,
    DWC_DDR4_2133P_3DS3A   = 34,
    DWC_DDR4_2133R_3DS4A   = 35,
    DWC_DDR4_2400P_3DS3B   = 36,
    DWC_DDR4_2400T_3DS2A   = 37,
    DWC_DDR4_2400U_3DS2A   = 38,
    DWC_DDR4_2400U_3DS4A   = 39,
    DWC_DDR4_2666T_3DS3A   = 40,
    DWC_DDR4_2666V_3DS3A   = 41,
    DWC_DDR4_2666W_3DS4A   = 42,
    DWC_DDR4_2933W_3DS3A   = 43,
    DWC_DDR4_2933Y_3DS3A   = 44,
    DWC_DDR4_2933AA_3DS43A = 45,
    DWC_DDR4_3200W_3DS4A   = 46,
    DWC_DDR4_3200AA_3DS4A  = 47,
    DWC_DDR4_3200AC_3DS4A  = 48,
    DWC_DDR4_3DS_LAST_SG   = 49
} dwc_ddr4_speed_grade_e;


/*
 * ! \enum dwc_ddr5_speed_bin_t
 * Encoding of DDDR5 speed bins aligned to rev152 of JEDEC spec.
 */
typedef enum tag_dwc_ddr5_speed_bin_e {
    DWC_DDR5_2100         = 0,
	DWC_DDR5_3200AN       = 1,
	DWC_DDR5_3200B        = 2,
	DWC_DDR5_3200BN       = 3,
	DWC_DDR5_3200C        = 4,
	DWC_DDR5_3600AN       = 5,
	DWC_DDR5_3600B        = 6,
	DWC_DDR5_3600BN       = 7,
	DWC_DDR5_3600C        = 8,
	DWC_DDR5_4000AN       = 9,
	DWC_DDR5_4000B        = 10,
	DWC_DDR5_4000BN       = 11,
	DWC_DDR5_4000C        = 12,
	DWC_DDR5_4400AN       = 13,
	DWC_DDR5_4400B        = 14,
	DWC_DDR5_4400BN       = 15,
	DWC_DDR5_4400C        = 16,
	DWC_DDR5_4800AN       = 17,
	DWC_DDR5_4800B        = 18,
	DWC_DDR5_4800BN       = 19,
	DWC_DDR5_4800C        = 20,
	DWC_DDR5_5200AN       = 21,
	DWC_DDR5_5200B        = 22,
	DWC_DDR5_5200BN       = 23,
	DWC_DDR5_5200C        = 24,
	DWC_DDR5_5600AN       = 25,
	DWC_DDR5_5600B        = 26,
	DWC_DDR5_5600BN       = 27,
	DWC_DDR5_5600C        = 28,
	DWC_DDR5_6000AN       = 29,
	DWC_DDR5_6000B        = 30,
	DWC_DDR5_6000BN       = 31,
	DWC_DDR5_6000C        = 32,
	DWC_DDR5_6400AN       = 33,
	DWC_DDR5_6400B        = 34,
	DWC_DDR5_6400BN       = 35,
	DWC_DDR5_6400C        = 36,
	DWC_DDR5_6800AN       = 37,
	DWC_DDR5_6800B        = 38,
	DWC_DDR5_6800BN       = 39,
	DWC_DDR5_6800C        = 40,
	DWC_DDR5_7200AN       = 41,
	DWC_DDR5_7200B        = 42,
	DWC_DDR5_7200BN       = 43,
	DWC_DDR5_7200C        = 44,
	DWC_DDR5_7600AN       = 45,
	DWC_DDR5_7600B        = 46,
	DWC_DDR5_7600BN       = 47,
	DWC_DDR5_7600C        = 48,
	DWC_DDR5_8000AN       = 49,
	DWC_DDR5_8000B        = 50,
	DWC_DDR5_8000BN       = 51,
	DWC_DDR5_8000C        = 52,
	DWC_DDR5_8400AN       = 53,
	DWC_DDR5_8400B        = 54,
	DWC_DDR5_8400BN       = 55,
	DWC_DDR5_8400C        = 56,
    DWC_DDR5_8800AN       = 57,
    DWC_DDR5_8800B        = 58,
    DWC_DDR5_8800BN       = 59,
    DWC_DDR5_8800C        = 60,
	DWC_DDR5_MONO_LAST_SG = 61,
	DWC_DDR5_3DS_FIRST_SG = 62,
	DWC_DDR5_3200AN_3DS   = 63,
	DWC_DDR5_3200B_3DS    = 64,
	DWC_DDR5_3200BN_3DS   = 65,
	DWC_DDR5_3200C_3DS    = 66,
	DWC_DDR5_3600AN_3DS   = 67,
	DWC_DDR5_3600B_3DS    = 68,
	DWC_DDR5_3600BN_3DS   = 69,
	DWC_DDR5_3600C_3DS    = 70,
	DWC_DDR5_4000AN_3DS   = 71,
	DWC_DDR5_4000B_3DS    = 72,
	DWC_DDR5_4000BN_3DS   = 73,
	DWC_DDR5_4000C_3DS    = 74,
	DWC_DDR5_4400AN_3DS   = 75,
	DWC_DDR5_4400B_3DS    = 76,
	DWC_DDR5_4400BN_3DS   = 77,
	DWC_DDR5_4400C_3DS    = 78,
	DWC_DDR5_4800AN_3DS   = 79,
	DWC_DDR5_4800B_3DS    = 80,
	DWC_DDR5_4800BN_3DS   = 81,
	DWC_DDR5_4800C_3DS    = 82,
	DWC_DDR5_5200AN_3DS   = 83,
	DWC_DDR5_5200B_3DS    = 84,
	DWC_DDR5_5200BN_3DS   = 85,
	DWC_DDR5_5200C_3DS    = 86,
	DWC_DDR5_5600AN_3DS   = 87,
	DWC_DDR5_5600B_3DS    = 88,
	DWC_DDR5_5600BN_3DS   = 89,
	DWC_DDR5_5600C_3DS    = 90,
	DWC_DDR5_6000AN_3DS   = 91,
	DWC_DDR5_6000B_3DS    = 92,
	DWC_DDR5_6000BN_3DS   = 93,
	DWC_DDR5_6000C_3DS    = 94,
	DWC_DDR5_6400AN_3DS   = 95,
	DWC_DDR5_6400B_3DS    = 96,
	DWC_DDR5_6400BN_3DS   = 97,
	DWC_DDR5_6400C_3DS    = 98,
	DWC_DDR5_6800AN_3DS   = 99,
	DWC_DDR5_6800B_3DS    = 100,
	DWC_DDR5_6800BN_3DS   = 101,
	DWC_DDR5_6800C_3DS    = 102,
	DWC_DDR5_7200AN_3DS   = 103,
	DWC_DDR5_7200B_3DS    = 104,
	DWC_DDR5_7200BN_3DS   = 105,
	DWC_DDR5_7200C_3DS    = 106,
	DWC_DDR5_7600AN_3DS   = 107,
	DWC_DDR5_7600B_3DS    = 108,
	DWC_DDR5_7600BN_3DS   = 109,
	DWC_DDR5_7600C_3DS    = 110,
	DWC_DDR5_8000AN_3DS   = 111,
	DWC_DDR5_8000B_3DS    = 112,
	DWC_DDR5_8000BN_3DS   = 113,
	DWC_DDR5_8000C_3DS    = 114,
	DWC_DDR5_8400AN_3DS   = 115,
	DWC_DDR5_8400B_3DS    = 116,
	DWC_DDR5_8400BN_3DS   = 117,
	DWC_DDR5_8400C_3DS    = 118,
    DWC_DDR5_8800AN_3DS   = 119,
    DWC_DDR5_8800B_3DS    = 120,
    DWC_DDR5_8800BN_3DS   = 121,
    DWC_DDR5_8800C_3DS    = 122,
	DWC_DDR5_3DS_LAST_SG  = 123
} dwc_ddr5_speed_bin_t;

/*
 * ! \enum en_lpddr4_device
 * Encoding LPDDR4 SDRAM options.
 * The encoding must match the encoding in the cc_constants file
 */
typedef enum tag_dwc_lpddr4_device_type_e {
    DWC_LPDDR4_1GB_8MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_2GB_16MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_3GB_24MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_4GB_32MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_6GB_48MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_8GB_64MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_12GB_96MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_16GB_128MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_1GB_16MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_2GB_32MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_3GB_48MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_4GB_64MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_6GB_96MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_8GB_128MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_12GB_192MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR4_16GB_256MB_8DQ_8BK_PER_CHANNEL
} dwc_lpddr4_device_type_e;

/*
 * ! \enum dwc_lpddr5_device_type_e
 * Encoding LPDDR5 SDRAM address options.
 * The bank organization is encoded in this enum also.
 * NB The encoding must match the encoding in the Simulate Activity file
 */
typedef enum tag_dwc_lpddr5_device_type_e {
    // x16,4 Banks/4 Bank Groups
    DWC_LPDDR5_2GB_8MB_16DQ_4BK_4BG_PER_CHANNEL = 1,
    DWC_LPDDR5_3GB_12MB_16DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_4GB_16MB_16DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_6GB_24MB_16DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_8GB_32MB_16DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_12GB_48MB_16DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_16GB_64MB_16DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_24GB_96MB_16DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_32GB_128MB_16DQ_4BK_4BG_PER_CHANNEL,

    // byte-mode(x8), 4 Banks/4 Bank Groups
    DWC_LPDDR5_2GB_16MB_8DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_3GB_24MB_8DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_4GB_32MB_8DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_6GB_48MB_8DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_8GB_64MB_8DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_12GB_96MB_8DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_16GB_128MB_8DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_24GB_192MB_8DQ_4BK_4BG_PER_CHANNEL,
    DWC_LPDDR5_32GB_256MB_8DQ_4BK_4BG_PER_CHANNEL,

    // x16, 16 banks mode
    DWC_LPDDR5_2GB_8MB_16DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_3GB_12MB_16DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_4GB_16MB_16DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_6GB_24MB_16DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_8GB_32MB_16DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_12GB_48MB_16DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_16GB_64MB_16DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_24GB_96MB_16DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_32GB_128MB_16DQ_16BK_PER_CHANNEL,

    // byte-mode(x8), 16 banks mode
    DWC_LPDDR5_2GB_16MB_8DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_3GB_24MB_8DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_4GB_32MB_8DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_6GB_48MB_8DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_8GB_64MB_8DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_12GB_96MB_8DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_16GB_128MB_8DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_24GB_192MB_8DQ_16BK_PER_CHANNEL,
    DWC_LPDDR5_32GB_256MB_8DQ_16BK_PER_CHANNEL,

    // x16, 8 Banks mode
    DWC_LPDDR5_2GB_16MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_3GB_24MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_4GB_32MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_6GB_48MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_8GB_64MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_12GB_96MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_16GB_128MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_24GB_192MB_16DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_32GB_256MB_16DQ_8BK_PER_CHANNEL,

    // x8, 8 Banks mode
    DWC_LPDDR5_2GB_32MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_3GB_48MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_4GB_64MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_6GB_96MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_8GB_128MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_12GB_192MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_16GB_256MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_24GB_384MB_8DQ_8BK_PER_CHANNEL,
    DWC_LPDDR5_32GB_512MB_8DQ_8BK_PER_CHANNEL
} dwc_lpddr5_device_type_e;

typedef enum tag_dwc_ddr4_device_type_e {
    // 2 Gb
    DWC_DDR4_2GB_X_4DQ = 1,
    DWC_DDR4_2GB_X_8DQ,
    DWC_DDR4_2GB_X_16DQ,
    // 4 Gb
    DWC_DDR4_4GB_X_4DQ,
    DWC_DDR4_4GB_X_8DQ,
    DWC_DDR4_4GB_X_16DQ,
    // 8 Gb
    DWC_DDR4_8GB_X_4DQ,
    DWC_DDR4_8GB_X_8DQ,
    DWC_DDR4_8GB_X_16DQ,
    // 16 Gb
    DWC_DDR4_16GB_X_4DQ,
    DWC_DDR4_16GB_X_8DQ,
    DWC_DDR4_16GB_X_16DQ
} dwc_ddr4_device_type_e;

typedef enum tag_dwc_ddr5_device_type_e {
    //8 Gb
    DWC_DDR5_8GB_X_4DQ = 1,
    DWC_DDR5_8GB_X_8DQ,
    DWC_DDR5_8GB_X_16DQ,
    //16 Gb
    DWC_DDR5_16GB_X_4DQ,
    DWC_DDR5_16GB_X_8DQ,
    DWC_DDR5_16GB_X_16DQ,
    //24 Gb
    DWC_DDR5_24GB_X_4DQ,
    DWC_DDR5_24GB_X_8DQ,
    DWC_DDR5_24GB_X_16DQ,
    //32 Gb
    DWC_DDR5_32GB_X_4DQ,
    DWC_DDR5_32GB_X_8DQ,
    DWC_DDR5_32GB_X_16DQ,
    //64Gb
    DWC_DDR5_64GB_X_4DQ,
    DWC_DDR5_64GB_X_8DQ,
    DWC_DDR5_64GB_X_16DQ
} dwc_ddr5_device_type_e;

// TODO DELETE ME, not relevant to CINIT
typedef enum tag_dwc_lpddr4_chan_mode_e {
    DWC_LOCK_STEP = 1,
    DWC_SERIAL,
    DWC_MULTI_CHAN,
    DWC_MULTI_CHAN_SHARED_AC
} dwc_lpddr4_chan_mode_e;

typedef enum tag_dwc_sdram_module_type {
    DWC_NODIMM = 1,
    DWC_RDIMM,
    DWC_LRDIMM,
    DWC_UDIMM
} dwc_sdram_module_type;

typedef enum tag_dwc_ddr5_dimm_ch_arch_e {
	DATA_CHANNEL_36_BIT = 1, // DDR5 72bit RDIMM (32 data + 4 ECC)
	DATA_CHANNEL_40_BIT, // DDR5 80bit RDIMM (32 data + 8 ECC)
	DATA_CHANNEL_32_BIT // DDR5 64bit RDIMM (32 data + no ECC)
} dwc_ddr5_dimm_ch_arch_e;

typedef enum tag_dwc_dram_density_e {
    DWC_DEN64M,                                // 64Mb
    DWC_DEN128M,                                // 128Mb
    DWC_DEN256M,                                // 256Mb
    DWC_DEN512M,                                // 512Mb
    DWC_DEN1G,                                // 1Gb
    DWC_DEN2G,                                // 2Gb
    DWC_DEN3G,                                // 3Gb
    DWC_DEN4G,                                // 4Gb
    DWC_DEN6G,                                // 6Gb
    DWC_DEN8G,                                // 8Gb
    DWC_DEN12G,                                // 12Gb
    DWC_DEN16G,                                // 16Gb
    DWC_DEN24G,                                // 24Gb
    DWC_DEN32G,                                // 32Gb
    DWC_DEN64G                                // 64Gb
} dwc_dram_density_e;

/**
 * @brief Enumerated type listing possible SDRAM types supported
 */
typedef enum tag_dwc_sdram_protocol {
    DWC_DDR4,                                //!<DDR4 SDRAM
    DWC_DDR5,                                //!<DDR5 SDRAM
    DWC_LPDDR4 = 2,                                //!<LPDDR4 SDRAM
    DWC_LPDDR5 = 4                                //!<LPDDR5 SDRAM
} dwc_sdram_protocol;

/**
 * @brief Enumerated type listing the sdram bus width bus width
 */
typedef enum tag_dwc_sdram_bus_width_e {
    DWC_BUSWIDTH_FULL = 1,                            //!< Full bus width
    DWC_BUSWIDTH_HALF = 2,                            //!< Half bus width
    DWC_BUSWIDTH_QUARTER = 3                        //!< Quarter bus width
} dwc_sdram_bus_width_e;

typedef dwc_sdram_bus_width_e dwc_sdram_bus_width_t;

/************************************************************************/

/*
 * @brief Enum type for PHY types
 */
typedef enum tag_ddrPhyType_e {
    DWC_DDR54_PHY = 1,
    DWC_LPDDR54_PHY = 2,
    DWC_DDR54_PHY_V2 = 3,
    DWC_LPDDR5X4_PHY = 4,
    DWC_DDR5_PHY = 5,
    DWC_LPDDR4X_MULTIPHY = 6
} ddrPhyType_e;

typedef enum tag_speed_index_e {
    SLOW,
    TYP,
    FAST
} speed_index_e;


/**
 * @brief Enumerated type listing bus width
 */
typedef enum tag_ddrBusWidth_e {
    DDR_BUSWIDTH_FULL = 1,                            //!< Full bus width
    DDR_BUSWIDTH_HALF = 2,                            //!< Half bus width
    DDR_BUSWIDTH_QUARTER = 4,                        //!< Quarter bus width
    DDR_BUSWIDTH_MAX                            //!< internal Not used
} ddrBusWidth_e;

/**
 * @brief Enumerated type listing bus width
 */
typedef enum tag_address_mode_e {
    ADDRESS_MODE_AUTO = 0,                            //!< Automatic
    ADDRESS_MODE_CONFIG = 1,                          //!< Configuration COL/ROW bit size options
    ADDRESS_MODE_REGISTER_FIELD = 2                   //!< Register Field reference
} address_mode_e;


/**
 * @brief Structure containing DDR timing parameters.
 * @note the timing parameters are from JEDEC spec.
 */
typedef struct tag_ddrTimingParameters_t {
    // DRAM Timing Parameters
    uint32_t sg_tck_ps;                            //!< Minimum Clock Cycle Time
    uint32_t trc_ps;                            //!< Active to Active/Auto Refresh command time
    uint32_t trcd_ps;                            //!< Active to Read/Write command time
    uint32_t trp_ps;                            //!< Precharge command period
    uint32_t trpa_ps;                            //!< ???
    uint32_t trrd_l_tck;                            //!< Active bank a to Active bank b command time to same bank group
    uint32_t trrd_s_tck;                            //!< Active bank a to Active bank b command time to different bank group
    uint32_t trrd_ps;                            //!< Active bank a to Active bank b command time
    uint32_t burst_length;                          //!< Burst Length
#ifdef DDRCTL_DDR
    // DDR4 Timing Parameters
    uint32_t ddr4_txp_ps;                            //!< Exit power down to a valid command
    uint32_t ddr4_txpdll_ps;                        //!< Exit precharge power down to READ or WRITE command (DLL-off mode)
    uint32_t ddr4_txsdll_tck;                        //!< SelfRefresh to commands requiring a locked DLL
    uint32_t ddr4_tras_min_ps;                        //!< Minimum Active to Precharge command time
    uint32_t ddr4_tras_max_ps;                        //!< Maximum Active to Precharge command time
    uint32_t ddr4_trefi_ps;                            //!< ???
    uint32_t ddr4_trfc_min_fgr_ps;
    uint32_t ddr4_trfc_min_ps;                        //!< Refresh to Refresh Command interval minimum value
    uint32_t ddr4_trfc_min2_ps;                        //!< Refresh to Refresh Command interval minimum value
    uint32_t ddr4_trfc_min4_ps;                        //!< Refresh to Refresh Command interval minimum value
    uint32_t ddr4_trfc_max_ps;                        //!< Refresh to Refresh Command Interval maximum value
    uint32_t ddr4_twtr_l_tck;                        //!< Write to Read command delay in clocks (sometimes higher than twtr/tck)
    uint32_t ddr4_twtr_s_tck;                        //!< Write to Read command delay in clocks (sometimes higher than twtr/tck)
    uint32_t ddr4_tfaw_ps;                            //!< Four Bank Activate window
    uint32_t ddr4_tzqinit_tck;                        //!< ZQ Cal (Init) time
    uint32_t ddr4_tzqoper_tck;                        //!< ZQ Cal (Long) time
    uint32_t ddr4_tzqcs_tck;                        //!< ZQ Cal (Short) time
    uint32_t ddr4_tmrd_tck;                            //!< Load Mode Register command cycle time
    uint32_t ddr4_tcke_ps;                            //!< CKE minimum high or low pulse width
    uint32_t ddr4_tccd_l_tck;                        //!< Cas to Cas command delay to same bank group
    uint32_t ddr4_tccd_s_tck;                        //!< Cas to Cas command delay to different bank group
    uint32_t ddr4_tmod_ps;                            //!< LOAD MODE to non-LOAD MODE command cycle time
    uint32_t ddr4_trtp_ps;                            //!< Read to Precharge command delay
    uint32_t ddr4_twr_ps;                            //!< Write recovery time
    uint32_t ddr4_tmpx_lh_ps;                        //!< CS_n Low hold time to CKE rising edge
    uint32_t ddr4_tmpx_s_tck;                        //!< CS setup time to CKE
    uint32_t ddr4_tckmpe_ps;                        //!< Valid clock requirement after MPSM entry
    uint32_t ddr4_tcksrx_ps;                        //!< minimum Valid Clock Requirement before SRX
    uint32_t ddr4_txmpdll_ps;                        //!< Exit MPSM to commands requiring a locked DLL

    uint32_t ddr4_tpl_tck;                            //!< C/A parity latency
    uint32_t ddr4_wcl_tck;                            //!< Write Command Latency
    uint32_t ddr4_twr_crc_dm_tck;                        //!< Write recovery time when CRC and DM are enabled (tWR_CRC_DM = twr + twr_crc_dm)
    uint32_t ddr4_twtr_l_crc_dm_tck;                    //!< tWTR_L's additional delay when CRC and DM are enabled (tWTR_L_CRC_DM = twtr_l_tck + twtr_l_crc_dm)
    uint32_t ddr4_twtr_s_crc_dm_tck;                    //!< tWTR_S's additional delay when CRC and DM are enabled (tWTR_S_CRC_DM = twtr_s_tck + twtr_s_crc_dm)
    uint32_t ddr4_tcrc_alert_pw_tck;                    //!< CRC ALERT_n pulse width (Max)
    uint32_t ddr4_tcrc_alert_ps;                        //!< CRC error to ALERT_n pulse width
    uint32_t ddr4_tpar_alert_pw_tck;                    //!< Pulse width of ALERT_N signal when C/A Parity Error is detected (Max)
    uint32_t ddr4_tpar_unknown_ps;                        //!< Commands not guaranteed to be executed during this time
    uint32_t ddr4_tpar_alert_on_ps;                        //!< Delay from errant command to ALERT_n assertion
    uint32_t ddr4_cal_tck;                            //!< CS to Command Address Latency when cal mode is enabled (and not in geardown mode)
    uint32_t ddr4_tdqsck_dll_off_ps;                    //!< Read data Clock to Data Strobe relationship with DLL-off mode
    uint32_t ddr4_tstab_ps;                            //!< ddr4 Stabilization time
    uint32_t ddr4_trfc_dlr_fgr_ps;
    uint32_t ddr4_trfc_dlr_ps;                        //!< Refresh to Refresh Command to different logical rank
    uint32_t ddr4_trfc_dlr2_ps;                        //!< Refresh to Refresh Command to different logical rank
    uint32_t ddr4_trfc_dlr4_ps;                        //!< Refresh to Refresh Command to different logical rank
    uint32_t ddr4_trrd_dlr_tck;                        //!< Active bank a to Active bank b command time to different logical rank
    uint32_t ddr4_tfaw_dlr_tck;                        //!< Four Bank Activate window to different logical rank
    uint32_t ddr4_tccd_dlr_tck;                        //!< Cas to Cas command delay to different logical rank

    uint32_t ddr4_tcwl_1st_set_tck;
    uint32_t ddr4_tcwl_2nd_set_tck;
    uint32_t ddr4_tcl_tck;
    uint32_t ddr4_tcmd_gear_tck;
    uint32_t ddr4_tsync_gear_tck;
    uint32_t ddr4_tgear_hold_tck;
    uint32_t ddr4_tgear_setup_tck;
    uint32_t ddr4_rankMap4;
    uint32_t ddr4_rankMap2;
    uint32_t ddr4_rankMap2i;
    uint32_t ddr4_tcl_rdbi_tck;

    // ddr5 timing parameters
    uint32_t ddr5_tcwl_tck;
    uint32_t ddr5_tcl_tck;
    uint32_t ddr5_tcl_rdbi_tck;

    uint32_t ddr5_tras_min_ps;                        //!< minimum ACT to PRE command period
    uint32_t ddr5_tccd_l_tck;                        //!< minimum CAS_n to CAS_n command delay for same bank group
    uint32_t ddr5_tccd_s_tck;                        //!< minimum CAS_n to CAS_n command delay for different bank group for BL16, and BC8(on-the-fly)
    uint32_t ddr5_tccd_m_tck;                        //!< Read to Read cmd delay for different bank in same bank group
    uint32_t ddr5_tccd_l_wr_tck;                        //!<write to write same bank group second write RMW
    uint32_t ddr5_tccd_l_wr2_tck;                        //!<write to write same bank group second write not RMW
    uint32_t ddr5_tccd_m_wr_tck;                        //!<write to write delay for different bank in same bank group

    uint32_t ddr5_tfaw_2k_tck;                        //!< minimum Four activate window for 2KB page size // TODO summary to ddr5_tfaw_ps
    uint32_t ddr5_tfaw_1k_tck;                        //!< minimum Four activate window for 1KB page size // TODO summary to ddr5_tfaw_ps
    uint32_t ddr5_tfaw_512_tck;                        //!< minimum Four activate window for 512B page size // TODO summary to ddr5_tfaw_ps
    uint32_t ddr5_tfaw_tck;                            //!< minimum Four activate window
    uint32_t ddr5_twtr_l_tck;                        //!< minimum Delay from start of internal write transaction to internal read command for same bank same bank group
    uint32_t ddr5_twtr_m_tck;                        //!< minimum Delay from start of internal write transaction to internal read command for diff bank same bank group
    uint32_t ddr5_tfaw_dlr_tck;                        //!<Four activate window to the different logical rank
    uint32_t ddr5_tfaw_slr_tck;                        //!<Four activate window to the same logical rank
    uint32_t ddr5_twtr_s_tck;                        //!< minimum Delay from start of internal write transaction to internal read command for the same bank group
    uint32_t ddr5_trtp_ps;                            //!< minimum Internal READ Command to PRECHARGE Command delay
    uint32_t ddr5_tppd_tck;                            //!< minimum PRECHARGE (PRE) to PRECHARGE (PRE) delay , // TODO need to add it to VIP
    uint32_t ddr5_twr_ps;                            //!< minimum WRITE recovery time

    // mode register read/write AC timing
    uint32_t ddr5_tmrr_tck;                            //!<minimum Mode Register Read command period
    uint32_t ddr5_tmrr_p_tck;                        //!<minimum Mode Register Read Pattern to Mode Register Read Pattern command spacing
    uint32_t ddr5_tmrw_tck;                            //!< minimum Mode Register Write command period
    uint32_t ddr5_tmrd_tck;                            //!< minimum Mode Register Set command delay

    // refresh timing parameter
    uint32_t ddr5_trefi1_ps;
    uint32_t ddr5_trefi2_ps;
    uint32_t ddr5_trfc_fgr_ps;
    uint32_t ddr5_trfc1_ps;                            //!<minimum Normal Refresh (REFab)
    uint32_t ddr5_trfc2_ps;                            //!<minimum FGR Refresh (REFab)
    uint32_t ddr5_trfcsb_ps;                        //!<minimum Same Bank Refresh (REFab)
    uint32_t ddr5_tdqs2dq_ps;
    uint32_t ddr5_tinit3_us;
    uint32_t ddr5_tinit4_us;

    // 3ds refresh timing parameter
    uint32_t ddr5_trefsbrd_ps;                        //!<minimum Same Bank Refresh to ACT delay

    uint32_t ddr5_trfc_dlr_fgr_ps;
    uint32_t ddr5_trfc1_dlr_ps;                        //!< minimum Normal Refresh with 3DS different logical rank
    uint32_t ddr5_trfc2_dlr_ps;                        //!<minimum Fine Granularity Refresh with 3DS different logical rank
    uint32_t ddr5_trfcsb_dlr_ps;                       //!<minimum Same Bank Refresh with 3DS different logical rank
    uint32_t ddr5_trefsbrd_dlr_ps;                     //!<minimum 3ds Same Bank Refresh to ACT delay
    uint32_t ddr5_trrd_dlr_tck;                        //!<minimum 3ds ACTIVATE to ACTIVATE Command delay to different logical rank
    uint32_t ddr5_tccd_dlr_tck;                        //!<minimum read to read command delay in different logical ranks
    uint32_t ddr5_tccd_wr_dlr_tck;                     //!<minimum write to write command delay in different logical ranks

    // ZQ calibration timing parameters
    uint32_t ddr5_tzqcal_ps;                        //!< minimum ZQ calibration timie
    uint32_t ddr5_tzqlat_ps;                        //!< minimum ZQ calibration latch timie

    // self refresh Timing parameters
    /* uint32_t ddr5_tcpded_ps;                        //!< minimum Command pass disable delay */
    uint32_t ddr5_tcsl_ps;                            //!< minimum Self-Refresh CS_n low Pulse width
    uint32_t ddr5_tcsh_srexit_ps;                        //!< minimum Self-Refresh exit CS_n High Pulse width
    uint32_t ddr5_tcsl_srexit_tck;                        //!< minimum Self-Refresh exit CS_n Low Pulse width
    uint32_t ddr5_tcksrx_ps;                        //!< minimum Valid Clock Requirement before SRX
    uint32_t ddr5_tcklcs_tck;                        //!< minimum Valid Clock Requirement after SRE
    uint32_t ddr5_tcasrx_ps;                        //!< minimum Self-Refresh exit CS_n high
    uint32_t ddr5_txs_ps;                            //!< minimum Exit Self-Refresh to next valid command not requireing DLL
    uint32_t ddr5_txs_dll_ps;                        //!< minimum Exit Self-Refresh to next valid command needing a DLL TBD

    // PDA timings parameters
    uint32_t ddr5_tpda_latch_min_ps;
    uint32_t ddr5_tpda_delay_ps;                        //!< minimum PDA Enumerate ID Command to any other command cycle time
    uint32_t ddr5_tpda_dqs_delay_min_ps;                    //!< minimum Delay to rising strobe edge used for sampling DQ during PDA operation
    uint32_t ddr5_tpda_dqs_delay_max_ps;                    //!< maximum Delay to rising strobe edge used for sampling DQ during PDA operation
    uint32_t ddr5_tpda_s_tck;                        //!< minimum DQ Setup Time during PDA operation
    uint32_t ddr5_tpda_h_tck;                        //!< minimum DQ Hold Time during PDA operation

    // MPC command timings parameters
    uint32_t ddr5_tmpc_delay_tck;                        //!< minimum MPC to any other valid command delay
    uint32_t ddr5_tmc_mpc_setup_tck;                    //!<minimum time between stable MPC command and first falling CS edge (SETUP)
    uint32_t ddr5_tmc_mpc_hold_tck;                        //!<minimum time between first rising CS edge and stable MPC command (HOLD)
    uint32_t ddr5_tmpc_cs_min_tck;                        //!< minimum Time CS_n is held low to register MPC command
    uint32_t ddr5_tmpc_cs_max_tck;                        //!< maximum Time CS_n is held low to register MPC command

    // MPSM command timings parameters
    uint32_t ddr5_tmpsmx_ps;                        //!< minimum MPSM exit to first valid command delay
    uint32_t ddr5_tmpdpdact_ps;                        //!< minimum MPSM DPD exit to first ACT command delay

    // Power down timing parameters;
    uint32_t ddr5_tcpded_ps;                        //!< minimum Command pass disable delay
    uint32_t ddr5_tpd_ps;                            //!< Minimum Power Down Time
    uint32_t ddr5_txp_ps;                            //!< minimum Exit Power Down to next valid command
    uint32_t ddr5_tactpden_tck;                        //!<minimum Timing of ACT command to Power Down Entry command
    uint32_t ddr5_tprpden_tck;                        //!<minimum Timing of PREab, PREsb or PREpb to Power Down Entry command
    uint32_t ddr5_trdpden_tck;                        //!<minimum Timing of RD or RD w/AP to Power Down Entry command
    uint32_t ddr5_twrpden_tck;                        //!<minimum Timing of WR to Power Down Entry command
    uint32_t ddr5_twrapden_tck;                        //!<minimum Timing of WR w/AP to Power Down Entry command
    uint32_t ddr5_trefpden_tck;                        //!<minimum Timing of REFab or REFsb command to Power Down Entry command
    uint32_t ddr5_tmrrpden_tck;                        //!<minimum Timing of MRR to command to Power Down Entry command
    uint32_t ddr5_tmrwpden_tck;                        //!<minimum Timing of MRW command to Power Down Entry command
    uint32_t ddr5_tmpcpden_tck;                        //!<minimum Timing of MPC command to Power Down Entry command

    // Initialization Timing parameters
    uint32_t ddr5_tinit4_ps;                        //!< minimum time for DRAM to register EXIT on CS with CMOS
    uint32_t ddr5_tinit5_tck;                        //!< minimum cycles required after CS_n HIGH
    uint32_t ddr5_txpr_ps;                            //!< minimum time from Exit Reset to first valid Configuration Command

    // VrefCA command Timing parameters
    uint32_t ddr5_tvrefca_delay_tck;                    //!< minimum VrefCA command to any other valid command delay
    uint32_t ddr5_tvrefca_cs_min_tck;                    //!< minimum Time CS_n is held low to register VrefCA command
    uint32_t ddr5_tvrefca_cs_max_tck;                    //!< maximum Time CS_n is held low to register VrefCA command

    // DQS interval OSCilator Read out Timing parameters
    uint32_t ddr5_tosco_ps;                            //!< minimum Delay time from OSC stop to Mode Register Readout

    // CRC Error handling Timing parameters
    uint32_t ddr5_tcrc_alert_ps;                        //!<CRC Alert Delay Time
    uint32_t ddr5_tcrc_alert_pw_ps;                        //!<CRC Alert Pulse Width

    // DDR4 RCD timing parameters
    uint32_t ddr4_rcd_tstaoff_ps;  //!<Clock delay through the register between the input clock and output clock
    uint32_t ddr4_rcd_tpdm_ps;     //!< Propagation delay, single bit switching; CK_t/CK_c cross point to output
    uint32_t ddr4_rcd_tpdm_rd_ps;  //!< MDQS to DQS Propagation Delay
    uint32_t ddr4_rcd_tpdm_wr_ps;  //!< DQS to MDQS Propagation Delay

	// RCD timing parameters
	// For PHYINIT
	uint32_t ddr5_rcd_tstaoff_ps;
	uint32_t ddr5_rcd_tpdm_ps;
	uint32_t ddr5_rcd_tpdm_rd_ps;  //!< MDQS to DQS Propagation Delay
	uint32_t ddr5_rcd_tpdm_wr_ps; //!< DQS to MDQS Propagation Delay
	// For Controller
	uint32_t ddr5_rcd_tstab01_min_ps;
	uint32_t ddr5_rcd_tstab01_max_ps;
	uint32_t ddr5_rcd_tpdex_ps;
	uint32_t ddr5_rcd_tcssr_ps;
	uint32_t ddr5_rcd_tcpded2srx_tck;
	uint32_t ddr5_rcd_tsrx2srx_tck;
	uint32_t ddr5_rcd_tckoff_ps;
	uint32_t ddr5_rcd_tckact_tck;
	uint32_t ddr5_rcd_tcsalt_tck;
	uint32_t ddr5_rcd_trpdx_ps;
	uint32_t ddr5_dimm_t_dcaw_tck; //!< Activate window by DIMM channel
	uint32_t ddr5_dimm_n_dcac_m1;  //!< DIMM Channel Activate Command Count in tDCAW
	uint32_t ddr5_read_crc_latency_adder; //!< Read latency adder when read CRC is enabled (depends on data rate)
	uint32_t ddr5_tdllk_tck;

    // For LRDIMM
    uint32_t ddr5_tcpded_db_ps;
    uint32_t ddr5_rcd_tcssr_db_ps;
    uint32_t ddr5_rcd_tcpded2srx_db_tck;
    uint32_t ddr5_rcd_tstab_dbcmd_ps;
    uint32_t ddr5_rcd_tstab_dbdata_ps;
	uint32_t ddr5_db_tmrrod1_tck;
	uint32_t ddr5_db_tmrr2nod1_tck;

	uint32_t ddr5_rcd_tmrc_tck;
	uint32_t ddr5_rcd_tmrc2n_tck;
	uint32_t ddr5_rcd_tmrd_l_tck;
	uint32_t ddr5_rcd_tmrd2n_l_tck;
	uint32_t ddr5_rcd_tmrd2n_l2_tck;
	uint32_t ddr5_rcd_tmrd_l2_tck;

#endif /* DDRCTL_DDR */

#ifdef DDRCTL_LPDDR
	// LPDDR4 Timing Parameters
	uint32_t lpddr4_tckb;							//!< Clock cycle time during boot
	uint32_t lpddr4_tpbr2pbr;						//!< Per-bank refresh to Per-bank refresh different bank time
	uint32_t lpddr4_tpbr2pbr_mp;						//!< Per-bank refresh to Per-bank refresh different bank time
	uint32_t lpddr4_tras_min;
	uint32_t lpddr4_tras_max;
	uint32_t lpddr4_trfcab;
	uint32_t lpddr4_trfcpb;
	uint32_t lpddr4_trfcab_mp;
	uint32_t lpddr4_trfcpb_mp;
	uint32_t lpddr4_trfiab;
	uint32_t lpddr4_trfipb;
	uint32_t lpddr4_twtr;
	uint32_t lpddr4_tfaw;
	uint32_t lpddr4_tzqreset;
	uint32_t lpddr4_tzqinit;
	uint32_t lpddr4_tzqcs;
	uint32_t lpddr4_tzqcsb;
	uint32_t lpddr4_tzqclb;
	uint32_t lpddr4_tzqcl;
	uint32_t lpddr4_tmrr;
	uint32_t lpddr4_tmrw;
	uint32_t lpddr4_tmrwb;
	uint32_t lpddr4_tmrd;
	uint32_t lpddr4_tmrdb;
	uint32_t lpddr4_tcke;
	uint32_t lpddr4_tckesr;
	uint32_t lpddr4_tccd;
	uint32_t lpddr4_tccd_bl32;
	uint32_t lpddr4_tccdmw;
	uint32_t lpddr4_tccdmw_bl32;
	uint32_t lpddr4_trtp;
	uint32_t lpddr4_twr;
	uint32_t lpddr4_tppd;
	uint32_t lpddr4_tdqsck;
	uint32_t lpddr4_tdqsck_max;
	uint32_t lpddr4_tdqsck_max_dr;
	uint32_t lpddr4_tosco;
	uint32_t lpddr4_tdqss;
	uint32_t lpddr4_tdqs2dq;
	uint32_t lpddr4_tdipw_ps;
	uint32_t lpddr4_trcd;
	uint32_t lpddr4_trp;
	uint32_t lpddr4_trpa;
	uint32_t lpddr4_trc;
	uint32_t lpddr4_cl;
	uint32_t lpddr4_cl_dbi;
	uint32_t lpddr4_cwl_seta;
	uint32_t lpddr4_cwl_setb;
	uint32_t lpddr4_nrtp;
	uint32_t lpddr4_nwr;
	uint32_t lpddr4_tcmdcke;
	uint32_t lpddr4_tmrwckel;
	uint32_t lpddr4_tmrwckelb;
	uint32_t lpddr4_tckckeh;
	uint32_t lpddr4_tckelck;
	uint32_t lpddr4_tsr;
	uint32_t lpddr4_todton_min;
	uint32_t lpddr4_tvrcg_enable;
	uint32_t lpddr4_tvrcg_disable;
	uint32_t lpddr4_txp;
	uint32_t lpddr4_trrd;
	uint32_t lpddr4_odtloff_latency_seta;
	uint32_t lpddr4_odtloff_latency_setb;
	uint32_t lpddr4_odtlon_latency_seta;
	uint32_t lpddr4_odtlon_latency_setb;
	uint32_t lpddr4_wdqson_seta;
	uint32_t lpddr4_wdqson_setb;
	uint32_t lpddr4_wdqsoff_seta;
	uint32_t lpddr4_wdqsoff_setb;
	uint32_t lpddr_tzqinit_min;
	uint32_t lpddr4_derated_trcd;
	uint32_t lpddr4_derated_tras_min;
	uint32_t lpddr4_derated_trp;
	uint32_t lpddr4_derated_trrd;
	uint32_t lpddr4_derated_trc;
	uint32_t lpddr4_trfmpb;
	uint32_t lpddr4_trfmpb_mp;
	// LPDDR5 Timing Parameters (generally in ps)
	uint32_t lpddr5_wck_ps;
	uint32_t lpddr5_cl_ps;
	uint32_t lpddr5_cl_dbi_ps;
	uint32_t lpddr5_twtr_s_ps;
	uint32_t lpddr5_twtr_l_ps;
	uint32_t lpddr5_twtr_ps;
	uint32_t lpddr5_tpbr2pbr_ps;
	uint32_t lpddr5_tpbr2pbr_mp_ps;
	uint32_t lpddr5_tpbr2act_ps;
	uint32_t lpddr5_trcd_ps;
	uint32_t lpddr5_trcd_write_ps;
	uint32_t lpddr5_tccdmw_tck;
	uint32_t lpddr5_tccdmw_bl32_tck;
	uint32_t lpddr5_trp_ps;
	uint32_t lpddr5_tsr_ps;
	uint32_t lpddr5_txsr_ps;
	uint32_t lpddr5_trfcab_ps;
	uint32_t lpddr5_trfcpb_ps;
	uint32_t lpddr5_trfcab_mp_ps;
	uint32_t lpddr5_trfcpb_mp_ps;
	uint32_t lpddr5_tcspd_ps;
	uint32_t lpddr5_tcmpd_ps;
	uint32_t lpddr5_tescke_ps;
	uint32_t lpddr5_tcmdpd_ps;
	uint32_t lpddr5_tcslck_ps;
	uint32_t lpddr5_tckcsh_ps;
	uint32_t lpddr5_txp_ps;
	uint32_t lpddr5_tpdxcsodton_ps;
	uint32_t lpddr5_tmrw_l_ps;
	uint32_t lpddr5_tcsh_ps;
	uint32_t lpddr5_tcsl_ps;
	uint32_t lpddr5_tmrwpd_ps;
	uint32_t lpddr5_tzqpd_ps;
	uint32_t lpddr5_trc_pab_ps;
	uint32_t lpddr5_trc_ppb_ps;
	uint32_t lpddr5_trpab_ps;
	uint32_t lpddr5_trppb_ps;
	uint32_t lpddr5_tras_min_ps;
	uint32_t lpddr5_tras_max_ps;
	uint32_t lpddr5_twr_ps;
	uint32_t lpddr5_tccd_l_tck;						//!< Cas to Cas command delay to same bank group
	uint32_t lpddr5_tccd_l_bl32_tck;					//!< Cas to Cas command delay to same bank group for BL32
	uint32_t lpddr5_tccd_s_tck;						//!< Cas to Cas command delay to different bank group
	uint32_t lpddr5_tccd_ps;
	uint32_t lpddr5_trrd_l_ps;						//!< Active bank a to Active bank b command time to same bank group
	uint32_t lpddr5_trrd_s_ps;						//!< Active bank a to Active bank b command time to different bank group
	uint32_t lpddr5_trrd_ps;
	uint32_t lpddr5_tfaw_ps;
	uint32_t lpddr5_trtp_ps;
	uint32_t lpddr5_tppd_tck;
	uint32_t lpddr5_tmrr_tck;
	uint32_t lpddr5_tmrw_ps;
	uint32_t lpddr5_tmrd_ps;
	uint32_t lpddr5_odtloff_rd_rdqs_tck;			//!< ODTLon_RD_RDQS
	uint32_t lpddr5_odtlon_rd_rdqs_tck;			//!< ODTLon_RD_RDQS
	uint32_t lpddr5_odtloff_rd_rdqs_bl32_tck;			//!< ODTLon_RD_RDQS
	uint32_t lpddr5_odtlon_rd_rdqs_bl32_tck;			//!< ODTLon_RD_RDQS
	uint32_t lpddr5_odtloff_rd_tck;			//!< ODTLon_RD_DQ
	uint32_t lpddr5_odtlon_rd_tck;			//!< ODTLon_RD_DQ
	uint32_t lpddr5_odtloff_rd_bl32_tck;			//!< ODTLon_RD_DQ
	uint32_t lpddr5_odtlon_rd_bl32_tck;			//!< ODTLon_RD_DQ
	uint32_t lpddr5_odtloff_tck;
	uint32_t lpddr5_odtloff_bl32_tck;
	uint32_t lpddr5_odtlon_tck;
	uint32_t lpddr5_odtlon_bl32_tck;
	uint32_t lpddr5_odton_min_ps;
	uint32_t lpddr5_odton_max_ps;
	uint32_t lpddr5_odtoff_min_ps;
	uint32_t lpddr5_odtoff_max_ps;
	uint32_t lpddr5_odt_rdon_min_ps;
	uint32_t lpddr5_odt_rdon_max_ps;
	uint32_t lpddr5_odt_rdoff_min_ps;
	uint32_t lpddr5_odt_rdoff_max_ps;
	uint32_t lpddr5_tzqreset_ps;
	uint32_t lpddr5_tzqlat_ps;
	uint32_t lpddr5_tzqcal_ps;
	uint32_t lpddr5_tzqstop_ps;
	uint32_t lpddr5_tzqoff_us;
	uint32_t lpddr5_tvrcg_enable_ps;
	uint32_t lpddr5_tvrcg_disable_ps;
	// suffix _wck to indicate units are tWCK
	uint32_t lpddr5_wckenl_rd_wck;
	uint32_t lpddr5_wckpre_rd_static_wck;
	uint32_t lpddr5_wckpre_rd_toggle_wck;
	uint32_t lpddr5_wckenl_wr_seta_wck;
	uint32_t lpddr5_wckenl_wr_setb_wck;
	uint32_t lpddr5_wckpre_wr_static_wck;
	uint32_t lpddr5_wckpre_wr_toggle_wck;
	uint32_t lpddr5_wckpre_static_tck;
	uint32_t lpddr5_wckpre_toggle_wr_tck;
	uint32_t lpddr5_wckpre_toggle_rd_tck;
	uint32_t lpddr5_wckenl_rd_tck;
	uint32_t lpddr5_wckenl_wr_tck;
	uint32_t lpddr5_wckenl_fs_tck;
	uint32_t lpddr5_twck_en_wck;
	uint32_t lpddr5_twck_toggle_en_wck;
	uint32_t lpddr5_twck_toggle_dis_wck;
	uint32_t lpddr5_twckstop_ps;
	uint32_t lpddr5_tpdn_ps;
	uint32_t lpddr5_tpdn_dsm_ms;
	uint32_t lpddr5_txsr_dsm_us;
	uint32_t lpddr5_trbtp_ps;
	uint32_t lpddr5_tespd_ps;
	uint32_t lpddr5_wl_tck;
	uint32_t lpddr5_rl_tck;
	uint32_t lpddr5_nrbtp;							//!< READ Burst end to PRECHARGE command delay
	uint32_t lpddr5_nwr;
	uint32_t lpddr5_bl_n_min_tck;						//!< Effective burst length
	uint32_t lpddr5_bl_n_max_tck;						//!< Effective burst length
	uint32_t lpddr5_bl_n_min_bl32_tck;					//!< Effective burst length
	uint32_t lpddr5_bl_n_max_bl32_tck;					//!< Effective burst length
	uint32_t lpddr5_twck_pst_wck;
	uint32_t lpddr5_wckdqo_max_ps;
	uint32_t lpddr5_wckdqo_ps;
	uint32_t lpddr5_wckdqi_ps;
	uint32_t lpddr5_trpst;
	uint32_t lpddr5_trefi_ps;						//!< all bank average refresh interval
	uint32_t lpddr5_trefipb_ps;						//!< per bank average refresh interval
	uint32_t lpddr5_derated_trcd_ps;
	uint32_t lpddr5_derated_trcd_write_ps;
	uint32_t lpddr5_derated_tras_min_ps;
	uint32_t lpddr5_derated_trpab_ps;
	uint32_t lpddr5_derated_trppb_ps;
	uint32_t lpddr5_derated_trrd_ps;
	uint32_t lpddr5_derated_trcab_ps;
	uint32_t lpddr5_derated_trcpb_ps;
	uint32_t lpddr5_tosco;
	uint32_t lpddr5_trtw_tck;
	uint32_t lpddr5_trtw_bl32_tck;
	uint32_t lpddr5_trtw_s_tck;        //!< tRTW for different BG
	uint32_t lpddr5_trtw_s_bl32_tck;        //!< tRTW for different BG
	uint32_t lpddr5_trfmpb_ps;
	uint32_t lpddr5_trfmpb_mp_ps;
#endif /* DDRCTL_LPDDR */
    uint32_t wr2pre;                            //!< min time between write and precharge to the same bank
} ddrTimingParameters_t;

/**
 * @brief Structure containing parameters to program DWC DDR umctl registers.
 * The variables here are pre-calculated timings to help
 * program some register fields.
 */
typedef struct tag_mctl_pre_cfg {
    uint32_t cl[UMCTL2_FREQUENCY_NUM];                    //! CL
    uint32_t cl_dbi[UMCTL2_FREQUENCY_NUM];                    //!<
    uint32_t cwl_x[UMCTL2_FREQUENCY_NUM];                    //!< CWL adjusted.
    uint32_t twr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Write recovery time
    uint32_t twtr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Write to Read command delay
    uint32_t twtr_s[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!<
    uint32_t tfaw[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Four Bank Activate window
    uint32_t txp[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Exit power down to a valid command
    uint32_t txpdll[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ras_max[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ras_min[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rtp[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rc[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_wr2rd_m[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_s[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wdqspreext[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];

    uint32_t odton_min[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t odton[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_mrw[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Mode Register Write command period
    uint32_t t_mr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Load-mode command to next valid command period (tmrd >= tmrw)
    uint32_t t_mod[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rcd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Active to Read/Write command time
    uint32_t t_ccd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Cas to Cas command delay
    uint32_t t_rrd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!< Active bank a to Active bank b command time
    uint32_t t_rp[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_cksrx[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_cksre[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ckesr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_cke[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_mrw_l[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_csh[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_mrd_pda[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_wr_mpr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t odtloff[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t odtloff_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t odtlon[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t odtlon_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_t_rddata_en[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_tphy_wrlat[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_tphy_wrdata[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t cmd_lat_adder[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_t_dram_clk_disable[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_t_dram_clk_enable[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_t_init_start[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_t_init_complete[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_t_ctrl_delay_memclk[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];

    //ddr4
    uint32_t t_sync_gear[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_cmd_gear[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_gear_setup[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_gear_hold[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];

    //ddr5
    uint32_t t_csl[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];

#ifdef UMCTL2_CID_EN
    uint32_t t_ccd_dlr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rrd_dlr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!< ddr4 and ddr5
    uint32_t t_faw_dlr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_faw_slr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_wr2rd_dlr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!< ddr5
    uint32_t t_rd2wr_dlr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!< ddr5
    uint32_t t_refsbrd_dlr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rfcsb_dlr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
#endif /* UMCTL2_CID_EN */

#ifdef DDRCTL_LPDDR
    uint32_t t_rcd_write[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t derated_t_rcd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t derated_t_rcd_write[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t derated_t_ras_min[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t derated_t_rp[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t derated_t_rrd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t derated_t_rc[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t tINITTMG1[DWC_DDRCTL_NUM_CHANNEL];                //!< min cke low time before RESET_n high
    uint32_t tINITTMG3[DWC_DDRCTL_NUM_CHANNEL];                //!< min idle time before first MRW/MRR command.
    uint32_t t_pbr2pbr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_pbr2pbr_mp[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_pbr2act[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t tINIT2;                            //!<
    uint32_t tINIT3;                            //!< used post_cke
    uint32_t tINIT4[UMCTL2_FREQUENCY_NUM];                    //!< min idle time before first CKE high.
    uint32_t t_rrd_s[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!< Activate command to different bank group than prior Activate command
    uint32_t t_osco[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_pdn[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
#endif /* DDRCTL_LPDDRDDRCTL_LPDDR */

	uint32_t wl[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< write latency
	uint32_t rl[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< read latency
	uint32_t t_rbtp[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< LPDDR5
	uint32_t t_cmdcke[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_vrcg_enable[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_vrcg_disable[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t lpddr4_diff_bank_rwa2pre[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Time between Read/Write/Masked Write/Act and Precharge to diff bank
	uint32_t wra2pre[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Time between write with AP and activate to same bank
	uint32_t rda2pre[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Time between write read AP and activate to same bank.
	uint32_t rd2wr_s[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Minimum time from read command to write command for different bank group
	uint32_t rd2wr_s_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Minimum time from read command to write command for different bank group
	uint32_t max_rd_sync[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Maximum time between read commands without a new WCK2CK sync Start
	uint32_t max_wr_sync[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Maximum time between write commands without a new WCK2CK sync start
	uint32_t nwr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< nWR
	uint32_t nrtp[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< nRTP for LPDDR4
	uint32_t nrbtp[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< nRBTP for LPDDR5
	uint32_t dfi_twck_delay[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_en_rd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_en_wr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_en_fs[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_dis[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_fast_toggle[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_toggle[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_toggle_cs[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_toggle_post[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t dfi_twck_toggle_post_rd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t rd2mr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< Time from Read to MRW/MRR command
	uint32_t wr2mr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< Time from Write to MRW/MRR command
	uint32_t mrr2rd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< Time from MRR to Read command
	uint32_t mrr2wr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];		//!< Time from MRR to Write command
	uint32_t mrr2wr_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to Write command
	uint32_t mrr2mrw[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to MRW command
	uint32_t ws_off2ws_fs[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to MRW command
	uint32_t t_wcksus[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to MRW command
	uint32_t ws_fs2wck_sus[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to MRW command
	// ddr4
	uint32_t t_xs_fast_min[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_xs_min[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_mpx_lh[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_mpx_s[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_ckmpe[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t post_mpsm_gap_x32[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];

    // ddr5
    uint32_t t_pd[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];        //!<tPD ddr5
    uint32_t t_mpsmx[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tMPSMX ddr5
    uint32_t t_mpdpxact[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tMPDPADACT ddr5
    uint32_t t_pda_latch[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tPDA_LATCH ddr5
    uint32_t t_pda_delay[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tPDA_DELAY ddr5
    uint32_t t_pda_dqs_delay[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];//!<tPDA_DQS_DELAY ddr5
    uint32_t t_pda_s[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<t_pda_s ddr5
    uint32_t t_pda_h[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tPDA_H ddr5

    uint32_t t_cpded[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCPDED ddr5
    uint32_t t_casrx[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCASRX ddr5
    uint32_t t_csh_srexit[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCSH_SRexit ddr5
    uint32_t t_csl_srexit[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCSl_SRexit ddr5

    uint32_t t_mpc_cs[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tMPC_CS ddr5
    uint32_t t_mpc_setup[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tMPC_Setup ddr5
    uint32_t t_mpc_hold[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tMPC_Hold ddr5
    uint32_t t_mpc_delay[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tMPC_DELAY ddr5
    uint32_t t_ccd_w[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_L_WR write to write same bank same bank group second write write RMW
    uint32_t t_ccd_w_m[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_L_WR write to write diff bank same bank group second write write RMW
    uint32_t t_ccd_w2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_L_WR2 write to write same bank group second write not RMW
    uint32_t t_wr2rd_dpr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<wr2rd_dpr
    uint32_t t_rd2wr_dpr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<rd2wr_dpr
    uint32_t t_ccd_w_s[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_S,min WR to WR delay to diff BG
    uint32_t t_ccd_r_s[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_S,min RD to RD delay to diff BG
    uint32_t t_ccd_r_l[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_S,min RD to RD delay to same bank same BG
    uint32_t t_ccd_r_m[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_S,min RD to RD delay to diff bank same BG
    uint32_t t_mrr2mpc[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t lrank_rd2rd_gap[DWC_DDRCTL_NUM_CHANNEL];
    uint32_t lrank_wr2wr_gap[DWC_DDRCTL_NUM_CHANNEL];
#ifdef MEMC_NUM_RANKS_GT_1
    uint32_t wr2rd_dr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_dr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_dr_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_dr_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_dr_wck_on[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_dr_wck_on[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_wck_on[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_wck_on[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_dr_wck_on_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_dr_wck_on_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_wck_on_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_wck_on_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_wck_on_dq_odt_nt_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_wck_on_dq_odt_nt_odt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
#endif /* MEMC_NUM_RANKS_GT_1 */
/* MEMC_BURST_LENGTH_32 */
#ifdef DDRCTL_BURST_LENGTH_X2
    uint32_t t_ccd_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_mw_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2pre_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2pre_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wra2pre_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rda2pre_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_s_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_s_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_s_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2mr_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2mr_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t max_rd_sync_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t max_wr_sync_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_dr_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_dr_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_dr_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_dr_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_dr_wck_on_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_dr_wck_on_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_wck_on_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_wck_on_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_dr_wck_on_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_dr_wck_on_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_wck_on_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_wck_on_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_rd_gap_wck_on_dq_odt_nt_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t diff_rank_wr_gap_wck_on_dq_odt_nt_odt_blx2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
#endif /* DDRCTL_BURST_LENGTH_X2 */ 

#ifdef DDRCTL_WR_CRC_RETRY
    uint32_t t_wr_crc_retry_window[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
#endif

#ifdef DDRCTL_CAPAR_RETRY
    uint32_t capar_retry_window[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t retry_add_rd_lat_en[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t retry_add_rd_lat[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t extra_rd_retry_window[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t dfi_t_phy_rdlat[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
#endif

    uint32_t refab_hi_sch_gap[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t refsb_hi_sch_gap[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];

	uint32_t mrr_des_timing_unit_sel[DWC_DDRCTL_NUM_CHANNEL];
	uint32_t ci_mrr_des1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_t ci_mrr_des2[DWC_DDRCTL_NUM_CHANNEL];

	// ddr5 RCD
	uint32_t t_stab01[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_cssr[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_cpded2srx[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_srx2srx[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_ckoff[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_ckact[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_t t_csalt[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];

    uint32_t lpddr5_cdd;
    uint32_t tphy_wckcsgap;
    uint32_t t_xs_dll_x32[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
#ifdef DDRCTL_TWO_TIMING_SETS_EN
    uint32_t cl_2[UMCTL2_FREQUENCY_NUM];
    uint32_t cwl_x_2[UMCTL2_FREQUENCY_NUM];
    uint32_t twr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t twtr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t twtr_s_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rtp_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t tfaw_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ras_min_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2pre_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2pre_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rc_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t rd2wr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_wr2rd_m_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_mr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rcd_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rrd_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rp_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_xs_x32_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_xs_dll_x32_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rrd_s_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t wr2rd_s_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_w2_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ppd_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rp_ca_parity_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_wr2rd_dpr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rd2wr_dpr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_w_s_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_r_s_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_w_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_w_m_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_r_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_ccd_r_m_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_refi_x1_x32_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rfc_min_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_refsbrd_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rfcsb_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_zq_long_nop_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_zq_short_nop_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_mrr2mpc_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL]; //!< <minimum time from Mode Register Read to MPC command
#ifdef UMCTL2_CID_EN
    uint32_t t_ccd_dlr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rrd_dlr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_faw_dlr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_wr2rd_dlr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rd2wr_dlr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rfc_min_dlr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_refsbrd_dlr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t t_rfcsb_dlr_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
#endif

    uint32_t refab_hi_sch_gap_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_t refsb_hi_sch_gap_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];

#endif
} mctl_pre_cfg;

/**
 * @brief Type definition of structure describing mode register fields.
 */

typedef struct tag_ddr4_mr0_t {
    uint16_rnd_t wr_recovery;
    uint16_rnd_t dll_reset;
    uint16_rnd_t cl;                                //!< CAS Latency
    uint16_rnd_t burst_type;
    uint16_rnd_t burst_length;
} ddr4_mr0_t;

typedef struct tag_ddr4_mr1_t {
    uint16_rnd_t rtt_nom;
    uint16_rnd_t wr_leveling_enable;
    uint16_rnd_t al;
    uint16_rnd_t output_driver_impedance;
    uint16_rnd_t dll_enable;
} ddr4_mr1_t;

typedef struct tag_ddr4_mr2_t {
    uint16_rnd_t write_crc;
    uint16_rnd_t rtt_wr;
    uint16_rnd_t auto_self_ref;
    uint16_rnd_t cwl;
} ddr4_mr2_t;

typedef struct tag_ddr4_mr3_t {
    uint16_rnd_t wcl;
    uint16_rnd_t geardown;
    uint16_rnd_t mpr_op;
    uint16_rnd_t mpr_ps;
    uint16_rnd_t fine_granularity_refresh;
} ddr4_mr3_t;

typedef struct tag_ddr4_mr4_t {
    uint16_rnd_t wr_preamble;
    uint16_rnd_t rd_preamble;
    uint16_rnd_t selfref_abort;
    uint16_rnd_t cal;
    uint16_rnd_t refresh_mode;
    uint16_rnd_t refresh_range;
} ddr4_mr4_t;

typedef struct tag_ddr4_mr5_t {
    uint16_rnd_t read_dbi;
    uint16_rnd_t write_dbi;
    uint16_rnd_t data_mask;
    uint16_rnd_t ca_parity_persistent;
    uint16_rnd_t rtt_park;
    uint16_rnd_t dis_odt_input_buf_in_pd;
    uint16_rnd_t parity_latency_mode;
} ddr4_mr5_t;

typedef struct tag_ddr4_mr6_t {
    uint16_rnd_t tccd_l;
} ddr4_mr6_t;

// umctl5 ddr5
typedef struct tag_ddr5_mr0_t {
    uint16_rnd_t burst_length;
    uint16_rnd_t cl;                                //!<CAS latency
} ddr5_mr0_t;

typedef struct tag_ddr5_mr2_t {
    uint16_rnd_t rd_preamble_enable;
    uint16_rnd_t wr_leveling;
    uint16_rnd_t ddr5_2n_mode;
    uint16_rnd_t mpsm;
    uint16_rnd_t cs_assertion_duration;
    uint16_rnd_t dev15_mpsm;
    uint16_rnd_t internal_wr_timing;
} ddr5_mr2_t;

typedef struct tag_ddr5_mr3_t {
    uint16_rnd_t wr_leveling_internal_lower_byte;
    uint16_rnd_t wr_leveling_internal_upper_byte;
} ddr5_mr3_t;

typedef struct tag_ddr5_mr4_t {
    uint16_rnd_t refresh_trfc_mode;
    uint16_rnd_t refresh_rate;
} ddr5_mr4_t;

typedef struct tag_ddr5_mr5_t {
    uint16_rnd_t data_output_disable;
    uint16_rnd_t pull_up_output_drv_impedance;
    uint16_rnd_t tdqs_enable;
    uint16_rnd_t dm_enable;
    uint16_rnd_t pull_down_output_drv_impedance;
} ddr5_mr5_t;

typedef struct tag_ddr5_mr6_t {
    uint16_rnd_t trtp;
    uint16_rnd_t wr_recovery;
} ddr5_mr6_t;

typedef struct tag_ddr5_mr8_t {
    uint16_rnd_t rd_preamble;
    uint16_rnd_t wr_preamble;
    uint16_rnd_t rd_postamble;
    uint16_rnd_t wr_postamble;
} ddr5_mr8_t;

typedef struct tag_ddr5_mr13_t {
    uint16_rnd_t tccd_l;
} ddr5_mr13_t;

typedef struct tag_ddr5_mr15_t {
    uint16_rnd_t auto_ecs_in_selfref;
    uint16_rnd_t etc;
} ddr5_mr15_t;

typedef struct tag_ddr5_mr34_t {
    uint16_rnd_t rtt_park;
    uint16_rnd_t rtt_wr;
} ddr5_mr34_t;

typedef struct tag_ddr5_mr35_t {
    uint16_rnd_t rtt_nom_wr;
    uint16_rnd_t rtt_nom_rd;
} ddr5_mr35_t;

typedef struct tag_ddr5_mr37_t {
    uint16_rnd_t odtlon_wr_offset;
    uint16_rnd_t odtloff_wr_offset;
} ddr5_mr37_t;

typedef struct tag_ddr5_mr38_t {
    uint16_rnd_t odtlon_wr_nt_offset;
    uint16_rnd_t odtloff_wr_nt_offset;
} ddr5_mr38_t;

typedef struct tag_ddr5_mr39_t {
    uint16_rnd_t odtlon_rd_nt_offset;
    uint16_rnd_t odtloff_rd_nt_offset;
} ddr5_mr39_t;

typedef struct tag_ddr5_mr40_t {
    uint16_rnd_t rd_dqs_offset;
} ddr5_mr40_t;

typedef struct tag_ddr5_mr45_t {
    uint16_rnd_t osc_run_time;
} ddr5_mr45_t;

typedef struct tag_ddr5_mr50_t {
    uint16_rnd_t rd_crc_enable;
    uint16_rnd_t wr_crc_enable_lower_nibble;
    uint16_rnd_t wr_crc_enable_upper_nibble;
    uint16_rnd_t wr_crc_error_status;
    uint16_rnd_t wr_crc_auto_disable_enable;
    uint16_rnd_t wr_crc_auto_disable_status;
} ddr5_mr50_t;

typedef struct tag_ddr5_mr51_t {
    uint16_rnd_t wr_crc_auto_disable_thre;
} ddr5_mr51_t;

typedef struct tag_ddr5_mr52_t {
    uint16_rnd_t wr_crc_auto_disable_window;
} ddr5_mr52_t;

typedef struct tag_ddr5_mr58_t {
    uint16_rnd_t rfm_required;
    uint16_rnd_t raa_initial_management_threshold;
    uint16_rnd_t raa_maximum_management_threshold;
} ddr5_mr58_t;

typedef struct tag_ddr5_mr59_t {
    uint16_rnd_t raa_counter_decr_per_ref_cmd;
} ddr5_mr59_t;

typedef struct tag_ddr5_mode_registers_t {
    ddr5_mr0_t mr0;
    ddr5_mr2_t mr2;
    ddr5_mr3_t mr3;
    ddr5_mr4_t mr4;
    ddr5_mr5_t mr5;
    ddr5_mr6_t mr6;
    ddr5_mr8_t mr8;
    ddr5_mr13_t mr13;
    ddr5_mr15_t mr15;
    ddr5_mr34_t mr34;
    ddr5_mr35_t mr35;
    ddr5_mr37_t mr37;
    ddr5_mr38_t mr38;
    ddr5_mr39_t mr39;
    ddr5_mr40_t mr40;
    ddr5_mr45_t mr45;
    ddr5_mr50_t mr50;
    ddr5_mr51_t mr51;
    ddr5_mr52_t mr52;
    ddr5_mr58_t mr58[MEMC_NUM_RANKS];
    ddr5_mr59_t mr59[MEMC_NUM_RANKS];
} ddr5_mode_registers_t;

typedef struct tag_ddr4_mode_registers_t {
    ddr4_mr0_t mr0;
    ddr4_mr1_t mr1;
    ddr4_mr2_t mr2;
    ddr4_mr3_t mr3;
    ddr4_mr4_t mr4;
    ddr4_mr5_t mr5;
    ddr4_mr6_t mr6;
} ddr4_mode_registers_t;

typedef struct tag_lpddr4_mr0_t {
    uint16_rnd_t refresh_mode;
    uint16_rnd_t latency_mode;
    uint16_rnd_t rfm_support;
    uint16_rnd_t rzqi;
    uint16_rnd_t scls;
    uint16_rnd_t catr;
} lpddr4_mr0_t;

typedef struct tag_lpddr4_mr1_t {
    uint16_rnd_t rd_postamble;
    uint16_rnd_t wr_recovery;
    uint16_rnd_t rd_preamble;
    uint16_rnd_t wr_preamble;
    uint16_rnd_t burst_length;
} lpddr4_mr1_t;

typedef struct tag_lpddr4_mr2_t {
    uint16_rnd_t wls;
    uint16_rnd_t rl_wl;
} lpddr4_mr2_t;

typedef struct tag_lpddr4_mr3_t {
    uint16_rnd_t write_dbi;
    uint16_rnd_t read_dbi;
    uint16_rnd_t pdds;
    uint16_rnd_t pprp;
    uint16_rnd_t wr_postamble;
    uint16_rnd_t pu_cal;
} lpddr4_mr3_t;

typedef struct tag_lpddr4_mr12_t {
    uint16_rnd_t vr_ca;
    uint16_rnd_t vref_ca;
} lpddr4_mr12_t;

typedef struct tag_lpddr4_mr11_t {
    uint16_rnd_t ca_odt;
    uint16_rnd_t dq_odt;
} lpddr4_mr11_t;

typedef struct tag_lpddr4_mr13_t {
    uint16_rnd_t fsp_op;
    uint16_rnd_t fsp_wr;
    uint16_rnd_t dmd;
} lpddr4_mr13_t;

typedef struct tag_lpddr4_mr14_t {
    uint16_rnd_t vr_dq;
    uint16_rnd_t vref_dq;
} lpddr4_mr14_t;

typedef struct tag_lpddr4_mr22_t {
    uint16_rnd_t odtd;
    uint16_rnd_t odtd_ca;
    uint16_rnd_t odtd_cs;
    uint16_rnd_t odtd_ck;
    uint16_rnd_t soc_odt;
} lpddr4_mr22_t;

typedef struct tag_lpddr4_mr23_t {
    uint16_rnd_t dqs_interval;
} lpddr4_mr23_t;

typedef struct tag_lpddr4_mr26_t {
    uint16_rnd_t scl;
} lpddr4_mr26_t;

typedef struct tag_lpddr4_mode_registers_t {
    lpddr4_mr0_t mr0;
    lpddr4_mr1_t mr1;
    lpddr4_mr2_t mr2;
    lpddr4_mr3_t mr3;
    lpddr4_mr11_t mr11;
    lpddr4_mr12_t mr12;
    lpddr4_mr13_t mr13;
    lpddr4_mr14_t mr14;
    lpddr4_mr22_t mr22;
    lpddr4_mr23_t mr23;
    lpddr4_mr26_t mr26;
} lpddr4_mode_registers_t;

typedef struct tag_lpddr5_mr0_t {
	uint16_rnd_t per_pin_dfe;
	uint16_rnd_t unified_nt_odt;
	uint16_rnd_t dmi_output_behavior_mode;
	uint16_rnd_t optimized_refresh_mode;
	uint16_rnd_t enhanced_wck_always_on_mode_support;
	uint16_rnd_t latency_mode;
	uint16_rnd_t enhanced_nt_odt;

} lpddr5_mr0_t;

typedef struct tag_lpddr5_mr1_t {
    uint16_rnd_t write_latency;
    uint16_rnd_t ck_mode;
    uint16_rnd_t arfm_support;
    uint16_rnd_t drfm_support;
} lpddr5_mr1_t;

typedef struct tag_lpddr5_mr2_t {
    uint16_rnd_t nwr;
    uint16_rnd_t rl_nrtp;
} lpddr5_mr2_t;

typedef struct tag_lpddr5_mr3_t {
    uint16_rnd_t write_dbi;
    uint16_rnd_t read_dbi;
    uint16_rnd_t wls;
    uint16_rnd_t bk_bg_org;
    uint16_rnd_t pdds;
} lpddr5_mr3_t;

typedef struct tag_lpddr5_mr10_t {
    uint32_rnd_t rdqs_pst_mode;
    uint32_rnd_t rdqs_pst;
    uint32_rnd_t rdqs_pre_2;
    uint32_rnd_t wck_pst;
    uint32_rnd_t rdqs_pre;
} lpddr5_mr10_t;

typedef struct tag_lpddr5_mr11_t {
    uint16_rnd_t cs_odt_op;
    uint16_rnd_t ca_odt;
    uint16_rnd_t nt_odt;
    uint16_rnd_t dq_odt;
} lpddr5_mr11_t;

typedef struct tag_lpddr5_mr12_t {
    uint16_rnd_t vbs;
    uint16_rnd_t vref_ca;
} lpddr5_mr12_t;

typedef struct tag_lpddr5_mr13_t {
    uint16_rnd_t dual_vdd2;
    uint16_rnd_t dmd;
    uint16_rnd_t vro;
    uint16_rnd_t thermal_offset;
} lpddr5_mr13_t;

typedef struct tag_lpddr5_mr14_t {
    uint16_rnd_t vdlc;
    uint16_rnd_t vref_dq;
} lpddr5_mr14_t;

typedef struct tag_lpddr5_mr15_t {
    uint16_rnd_t vref_dq;
} lpddr5_mr15_t;

typedef struct tag_lpddr5_mr16_t {
    uint16_rnd_t cbt;
    uint16_rnd_t vrcg;
    uint16_rnd_t fsp_op;
    uint16_rnd_t fsp_wr;
} lpddr5_mr16_t;

typedef struct tag_lpddr5_mr17_t {
    uint16_rnd_t odtd;
    uint16_rnd_t odtd_ca;
    uint16_rnd_t odtd_cs;
    uint16_rnd_t odtd_ck;
    uint16_rnd_t soc_odt;
} lpddr5_mr17_t;

typedef struct tag_lpddr5_mr18_t {
    uint16_rnd_t ckr;
    uint16_rnd_t wck2ck_leveling;
    uint16_rnd_t wck_on;
    uint16_rnd_t wck_fm;
    uint16_rnd_t wck_odt;
} lpddr5_mr18_t;

typedef struct tag_lpddr5_mr19_t {
    uint16_rnd_t dvfsq;
    uint16_rnd_t dvfsc;
} lpddr5_mr19_t;

typedef struct tag_lpddr5_mr20_t {
    uint16_rnd_t wck_mode;
    uint16_rnd_t rdqs;
} lpddr5_mr20_t;

typedef struct tag_lpddr5_mr21_t {
    uint16_rnd_t dcfe;
    uint16_rnd_t wxfs;
} lpddr5_mr21_t;

typedef struct tag_lpddr5_mr22_t {
    uint16_rnd_t wecc;
    uint16_rnd_t recc;
} lpddr5_mr22_t;

typedef struct tag_lpddr5_mr23_t {
    uint16_rnd_t pasr_mask;
} lpddr5_mr23_t;

typedef struct tag_lpddr5_mr24_t {
    uint16_rnd_t dfes;
    uint16_rnd_t dfequ;
    uint16_rnd_t dfeql;
} lpddr5_mr24_t;

typedef struct tag_lpddr5_mr25_t {
    uint16_rnd_t ck_bus_term;
    uint16_rnd_t ca_bus_term;
    uint16_rnd_t parc;
    uint16_rnd_t optimized_refresh_mode;
} lpddr5_mr25_t;

typedef struct tag_lpddr5_mr26_t {
    uint16_rnd_t dwck_rdws_train;
} lpddr5_mr26_t;

typedef struct tag_lpddr5_mr27_t {
    uint16_rnd_t raa_mult;
    uint16_rnd_t raa_imt;
    uint16_rnd_t raa_rfm;
} lpddr5_mr27_t;

typedef struct tag_lpddr5_mr28_t {
    uint16_rnd_t zq_int;
    uint16_rnd_t zq_stop;
    uint16_rnd_t zq_reset;
} lpddr5_mr28_t;

typedef struct tag_lpddr5_mr37_t {
    uint16_rnd_t wck2dqi_runtime;
} lpddr5_mr37_t;

typedef struct tag_lpddr5_mr40_t {
    uint16_rnd_t wck2dqo_runtime;
} lpddr5_mr40_t;

typedef struct tag_lpddr5_mr41_t {
    uint16_rnd_t pdfec;
    uint16_rnd_t nt_dq_odt;
    uint16_rnd_t dvfsc_edvfsc_support;
    uint16_rnd_t edvfsc_odt_support;
} lpddr5_mr41_t;

typedef struct tag_lpddr5_mr46_t {
    uint16_rnd_t enh_rdqs;
    uint16_rnd_t fifo_rdqs_training;
} lpddr5_mr46_t;

typedef struct tag_lpddr5_mr57_t {
    uint16_rnd_t arfm;
    uint16_rnd_t rfm_sbc;
    uint16_rnd_t rfm_sb;
    uint16_rnd_t raa_dec;
} lpddr5_mr57_t;

typedef struct tag_lpddr5_mr75_t {
    uint16_rnd_t brc_support;
} lpddr5_mr75_t;


//todo mr29,mr30,mr31,mr32,mr33,mr34,mr37,mr40
//todo mr0,mr26,mr41,mr46 for 5A
typedef struct tag_lpddr5_mode_registers_t {
    lpddr5_mr0_t mr0;
    lpddr5_mr1_t mr1;
    lpddr5_mr2_t mr2;
    lpddr5_mr3_t mr3;
    lpddr5_mr10_t mr10;
    lpddr5_mr11_t mr11;
    lpddr5_mr12_t mr12;
    lpddr5_mr13_t mr13;
    lpddr5_mr14_t mr14;
    lpddr5_mr15_t mr15;
    lpddr5_mr16_t mr16;
    lpddr5_mr17_t mr17;
    lpddr5_mr18_t mr18;
    lpddr5_mr19_t mr19;
    lpddr5_mr20_t mr20;
    lpddr5_mr21_t mr21;
    lpddr5_mr22_t mr22;
    lpddr5_mr23_t mr23;
    lpddr5_mr24_t mr24;
    lpddr5_mr25_t mr25;
    lpddr5_mr26_t mr26;
    lpddr5_mr27_t mr27;
    lpddr5_mr28_t mr28;
    lpddr5_mr37_t mr37;
    lpddr5_mr40_t mr40;
    lpddr5_mr41_t mr41;
    lpddr5_mr46_t mr46;
    lpddr5_mr57_t mr57;
    lpddr5_mr75_t mr75;
} lpddr5_mode_registers_t;

typedef struct tag_ddr4_rcd_rc0a_t {                        // RC0A: RDIMM Operating Speed
    uint16_rnd_t operating_speed;                        // DA[2:0] Operating speed
    //uint16_rnd_t context;                            // DA[3] Context for operation training
} ddr4_rc0a_t;

typedef struct tag_ddr4_rcd_rc0d_t {                        // RC0D: DIMM Configuration Control Word
    uint16_rnd_t cs_mode;                            // DA[1:0] CS mode 0:Direct DualCS, 1:Direct QuadCS, 2:Reserved, 3:Encoded QuadCS
    uint16_rnd_t dimm_type;                            // DA[2] DIMM Type 0:LRDIMM, 1:RDIMM
    uint16_rnd_t address_mirroring;                        // DA[3] Address mirroring for MRS commands 0:Disabled, 1:Enabled
} ddr4_rc0d_t;

typedef struct tag_ddr4_rcd_rc0e_t {                        // RC0E: Parity Control Word (Parity Enable, ALERT_n assertion, ALERT_n Re-enable)
    uint16_rnd_t parity_check;                        // DA[0] Parity enable    0: disable, 1: enable
                                        // DA[1] Reserved
    uint16_rnd_t alert_n_assertion;                        // DA[2] ALERT_n assertion 0: Static ALERT_n Assertion Mode, 1: Pulsed ALERT_n Mode
    uint16_rnd_t alert_n_reenable;                        // DA[3] ALERT_n re-enable 0: Parity checking remains disabled after ALERT_n pulse, 1: Parity Checking is re-enabled after ALERT_n pulse
} ddr4_rc0e_t;

typedef struct tag_ddr4_rcd_rc0f_t {                        // RC0F: Command Latency Adder Control Word
    uint16_rnd_t latency_adder_nladd_to_all_dram_cmd;            // DA[2:0] Latency adder nLadd to all DRAM commands
                                        // DA[3] Reserved
} ddr4_rc0f_t;

typedef struct tag_ddr4_rcd_rc3x_t {                        // RC3X: Fine Granularity RDIMM Operating Speed
    uint16_rnd_t fine_granularity_operating_speed;                // DA[7:0] Fine Granularity Operating Speed
} ddr4_rc3x_t;

typedef struct tag_ddr4_rcd_control_words_t {
    ddr4_rc0a_t rc0a;
    ddr4_rc0d_t rc0d;
    ddr4_rc0e_t rc0e;
    ddr4_rc0f_t rc0f;
    ddr4_rc3x_t rc3x;
} ddr4_control_words_t;
////////////////////////////////////
typedef struct tag_ddr5_rcd_rw00_t {
    uint16_rnd_t ca_rate;                    // 0: SDR, 1: DDR
    uint16_rnd_t sdr_mode;                   // 0: SDR1, 1: SDR2
} ddr5_rw00_t;

typedef struct tag_ddr5_rcd_rw01_t {
    uint16_rnd_t parity_check;                // 0: disable, 1: enable
    uint16_rnd_t dram_if_cmds;                    // 0: Block, 1: Not block
    uint16_rnd_t databuffer_cmds;            // 0: Block, 1: Not block
    uint16_rnd_t alert_n_assertion;            // 0: Static ALERT_n Assertion Mode 1: Pulsed ALERT_n Mode
    uint16_rnd_t alert_n_reenable;            // 0: Parity checking remains disabled after ALERT_n pulse, 1: Parity Checking is re-enabled after ALERT_n pulse
} ddr5_rw01_t;

typedef struct tag_ddr5_rcd_rw05_t {
    uint16_rnd_t operating_speed;
} ddr5_rw05_t;

typedef struct tag_ddr5_rcd_rw06_t {
    uint16_rnd_t fine_granularity_operating_speed;
} ddr5_rw06_t;

typedef struct tag_ddr5_rcd_rw09_t {
    uint16_rnd_t dimm_type;                    //0: LRDIMM enabled:BCS_n , BCOM[2:0] & BRST_n,1: RDIMM Disabled
    uint16_rnd_t dcs_qcs_en;                    //0: DCS1 Disabled 1: DCS1 Enabled
} ddr5_rw09_t;

typedef struct tag_ddr5_rcd_rw11_t {
    uint16_rnd_t latency_adder_nladd_to_all_dram_cmd;
} ddr5_rw11_t;

typedef struct tag_ddr5_rcd_control_words_t {
    ddr5_rw00_t rw00;
    ddr5_rw01_t rw01;
    ddr5_rw05_t rw05;
    ddr5_rw06_t rw06;
    ddr5_rw09_t rw09;
    ddr5_rw11_t rw11;
} ddr5_control_words_t;

//////////ddr5 data buffer///////////
typedef struct tag_ddr5_db_rw80_t {
    uint16_rnd_t db_ca_rate;                // 0: 2N(default), 1: 1N
} ddr5_rw80_t;

typedef struct tag_ddr5_db_rw81_t {
    uint16_rnd_t db_pba_mode;                // Per Buffer Addressability 0: Disable, 1: Enable
} ddr5_rw81_t;

typedef struct tag_ddr5_db_rw82_t {
    uint16_rnd_t db_tp_mode;                // Transparent mode 0: Disable, 1: Enable
} ddr5_rw82_t;

typedef struct tag_ddr5_db_rw84_t {
    uint16_rnd_t lrdimm_operating_speed;
} ddr5_rw84_t;

typedef struct tag_ddr5_db_rw85_t {
    uint16_rnd_t fine_granularity_operating_speed;
} ddr5_rw85_t;

typedef struct tag_ddr5_db_control_words_t {
    ddr5_rw80_t rw80;
    ddr5_rw81_t rw81;
    ddr5_rw82_t rw82;
    ddr5_rw84_t rw84;
    ddr5_rw85_t rw85;
} ddr5_db_control_words_t;

typedef struct tag_ddr5_scaling_control_t {
	uint32_t ddr5_trefi1_ps_scale_en;
	uint32_t ddr5_trefi1_ps_scale_val;
	uint32_t ddr5_trfc1_ps_scale_val;
	uint32_t ddr5_trfc2_ps_scale_val;
	uint32_t ddr5_trfcsb_ps_scale_val;
	uint32_t ddr5_trfcsb_dlr_ps_scale_val;
} ddr5_scaling_control_t;
////////////////////////////////////
typedef enum {
    DWC_PHY_TRAINING = 0,        //<! if set to 0 firmware training is executed
    DWC_PHY_SKIP_TRAINING = 1,    //<! if set to 1 training is skipped and registers are programmed to work with zero board delay.
    DWC_PHY_DEV_INIT = 2        //<! if set to 2 training is used to skip training but execute the firmware to initialize the DRAM state while registers are programmed to work with zero board delay.
} dwc_ddrctl_phy_training_e;



/// @enum a enumerated type to select a software sequence for simulation.
typedef enum {
    CINIT_SEQ_INITIALIZATION=1,
    CINIT_SEQ_CLK_REMOVAL,
    CINIT_SEQ_PWR_REMOVAL,
    CINIT_SEQ_MPSM,
    CINIT_SEQ_DDR5_FGR,
    CINIT_SEQ_LPDDR5_DSM,
    CINIT_SEQ_SWFFC_WITH_FSP,
    CINIT_SEQ_SWFFC_WITH_NO_FSP,
    CINIT_SEQ_LPDDR5_RFM_LEVEL,
    CINIT_SEQ_LPDDR5_SREF_RETRAIN_PPT2
} dwc_ddrctl_cinit_seq_e;

/// @enum a enumerated type for DFIMISC.dfi_frequency
typedef enum {
   DFI_FREQ_0,
   DFI_FREQ_1,
   DFI_FREQ_2,
   DFI_FREQ_3,
   DFI_FREQ_4,
   DFI_FREQ_5,
   DFI_FREQ_6,
   DFI_FREQ_7,
   DFI_FREQ_8,
   DFI_FREQ_9,
   DFI_FREQ_10,
   DFI_FREQ_11,
   DFI_FREQ_12,
   DFI_FREQ_13,
   DFI_FREQ_14,
   DFI_FREQ_15,
   DFI_FREQ_16,
   DFI_FREQ_17,
   DFI_FREQ_18,
   DFI_FREQ_19,
   DFI_FREQ_20,
   DFI_FREQ_21,
   DFI_FREQ_22,
   DFI_FREQ_23,
   DFI_FREQ_24,
   DFI_FREQ_25,
   DFI_FREQ_26,
   DFI_FREQ_27,
   DFI_FREQ_28,
   DFI_FREQ_29,
   DFI_FREQ_30,
   DFI_FREQ_31
} dwc_ddrctl_dfi_frequency_e;

/// @enum dwc_ddrctl_cinit_tb_signal_e a enumerated type to send a signal/event to the simulator
typedef enum {
	CINIT_SEND_DPI_MAIN_DONE=1,
	CINIT_SEND_WR_RD_TRAFFIC=2
} dwc_ddrctl_cinit_tb_signal_e;

  /*! \enum en_pub_message_id
   * Decode of Mailbox message from PUB firmware.
   * See DesignWare Cores DDR5/4-STD DDR5 UDIMM/RDIMMTraining Firmware Application Note
   * for details of the encoding.
   */
typedef enum {
    PUB_MSG_END_OF_INITIALIZATION                              = 0x00,
    PUB_MSG_END_OF_FINE_WRITE_LEVELING                         = 0x01,
    PUB_MSG_END_OF_READ_ENABLE_TRAINING                        = 0x02,
    PUB_MSG_END_OF_READ_DELAY_CENTER_OPTIMIZATION              = 0x03,
    PUB_MSG_END_OF_WRITE_DELAY_CENTER_OPTIMIZATION             = 0x04,
    PUB_MSG_TRAINING_COMPLETE_PASSED                           = 0x07,
    PUB_MSG_START_STREAMING_MESSAGE_MODE                       = 0x08,
    PUB_MSG_END_OF_MAX_READ_LATENCY_TRAINING                   = 0x09,
    PUB_MSG_END_OF_CA_TRAINING                                 = 0x0d,
/* DDR specific messages */
#ifdef DDRCTL_DDR
    PUB_MSG_END_OF_2D_READ_DELAY_VOLTAGE_CENTER_OPTIMIZATION   = 0x05,
    PUB_MSG_END_OF_2D_WRITE_DELAY_VOLTAGE_CENTER_OPTIMIZATION  = 0x06,
    PUB_MSG_END_OF_READ_DQ_DESKEW_TRAINING                     = 0x0a,
    PUB_MSG_END_OF_LCDL_OFFSET_CALIBRATION                     = 0x0b,
    PUB_MSG_END_OF_RCD_QCS_QCA_TRAINING                        = 0x1d,
    PUB_MSG_END_OF_LRDIMM_SPECIFIC_TRAINING                    = 0x0c,
    PUB_MSG_END_OF_LRDIMM_MREP_TRAINING                        = 0x20,
    PUB_MSG_END_OF_LRDIMM_DWL_TRAINING                         = 0x21,
    PUB_MSG_END_OF_LRDIMM_MRD_TRAINING                         = 0x22,
    PUB_MSG_END_OF_LRDIMM_MWD_TRAINING                         = 0x23,
    PUB_MSG_END_OF_MEMORY_RESET                                = 0x60,
    PUB_MSG_END_OF_MPR_READ_DELAY_CENTER_OPTIMIZATION          = 0xfd,
#endif // DDRCTL_DDR
/* LPDDR specific messages */
#ifdef DDRCTL_LPDDR
    PUB_MSG_END_OF_RXDIGSTROBE_TRAINING                        = 0x05,
    PUB_MSG_END_OF_DRAM_DCA_TRAINING                           = 0x06,
    PUB_MSG_END_OF_PHY_RX_DCA_TRAINING                         = 0x0a,
    PUB_MSG_END_OF_PHY_TX_DCA_TRAINING                         = 0x0b,
    PUB_MSG_END_OF_READ_TRAINING_CENTER_OPTIMIZATION           = 0xfd,
#endif // DDRCTL_LPDDR
    PUB_MSG_SMBUS_REQUEST                                      = 0x50,
    PUB_MSG_SMBUS_SYNC                                         = 0x51,
    PUB_MSG_END_OF_WRITE_LEVELING_COARSE_DELAY                 = 0xfe,
    PUB_MSG_TRAINING_COMPLETE_FAILED                           = 0xff
} pub_msg_id_t;


#endif /* __DWC_DDRCTL_CINIT_TYPES_H__ */
