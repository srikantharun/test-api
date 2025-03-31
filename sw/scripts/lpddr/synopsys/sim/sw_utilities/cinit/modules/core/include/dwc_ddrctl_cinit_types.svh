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


`ifndef __DWC_DDRCTL_CINIT_TYPES_H__
`define __DWC_DDRCTL_CINIT_TYPES_H__

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
typedef enum {
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
typedef enum {
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
typedef enum {
    DWC_WCKCK_2_1 = 1,
    DWC_WCKCK_4_1
} dwc_lpddr5_wckck_ratio_e;

/*
 * ! \enum dwc_lpddr5_bk_bg_org_e
 * Encoding of LPDDDR5 back organization.
 */
typedef enum {
    DWC_LPDDR5_4BK_4BG = 0,
    DWC_LPDDR5_8BK,
    DWC_LPDDR5_16BK
} dwc_lpddr5_bk_bg_org_e;

typedef enum {
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
typedef enum {
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
typedef enum {
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
typedef enum {
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

typedef enum {
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

typedef enum {
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
typedef enum {
    DWC_LOCK_STEP = 1,
    DWC_SERIAL,
    DWC_MULTI_CHAN,
    DWC_MULTI_CHAN_SHARED_AC
} dwc_lpddr4_chan_mode_e;

typedef enum {
    DWC_NODIMM = 1,
    DWC_RDIMM,
    DWC_LRDIMM,
    DWC_UDIMM
} dwc_sdram_module_type;

typedef enum {
	DATA_CHANNEL_36_BIT = 1, // DDR5 72bit RDIMM (32 data + 4 ECC)
	DATA_CHANNEL_40_BIT, // DDR5 80bit RDIMM (32 data + 8 ECC)
	DATA_CHANNEL_32_BIT // DDR5 64bit RDIMM (32 data + no ECC)
} dwc_ddr5_dimm_ch_arch_e;

typedef enum {
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
typedef enum {
    DWC_DDR4,                                //!<DDR4 SDRAM
    DWC_DDR5,                                //!<DDR5 SDRAM
    DWC_LPDDR4 = 2,                                //!<LPDDR4 SDRAM
    DWC_LPDDR5 = 4                                //!<LPDDR5 SDRAM
} dwc_sdram_protocol;

/**
 * @brief Enumerated type listing the sdram bus width bus width
 */
typedef enum {
    DWC_BUSWIDTH_FULL = 1,                            //!< Full bus width
    DWC_BUSWIDTH_HALF = 2,                            //!< Half bus width
    DWC_BUSWIDTH_QUARTER = 3                        //!< Quarter bus width
} dwc_sdram_bus_width_e;

typedef dwc_sdram_bus_width_e dwc_sdram_bus_width_t;

/************************************************************************/

/*
 * @brief Enum type for PHY types
 */
typedef enum {
    DWC_DDR54_PHY = 1,
    DWC_LPDDR54_PHY = 2,
    DWC_DDR54_PHY_V2 = 3,
    DWC_LPDDR5X4_PHY = 4,
    DWC_DDR5_PHY = 5,
    DWC_LPDDR4X_MULTIPHY = 6
} ddrPhyType_e;

typedef enum {
    SLOW,
    TYP,
    FAST
} speed_index_e;


/**
 * @brief Enumerated type listing bus width
 */
typedef enum {
    DDR_BUSWIDTH_FULL = 1,                            //!< Full bus width
    DDR_BUSWIDTH_HALF = 2,                            //!< Half bus width
    DDR_BUSWIDTH_QUARTER = 4,                        //!< Quarter bus width
    DDR_BUSWIDTH_MAX                            //!< internal Not used
} ddrBusWidth_e;

/**
 * @brief Enumerated type listing bus width
 */
typedef enum {
    ADDRESS_MODE_AUTO = 0,                            //!< Automatic
    ADDRESS_MODE_CONFIG = 1,                          //!< Configuration COL/ROW bit size options
    ADDRESS_MODE_REGISTER_FIELD = 2                   //!< Register Field reference
} address_mode_e;


/**
 * @brief Structure containing DDR timing parameters.
 * @note the timing parameters are from JEDEC spec.
 */
typedef struct {
    // DRAM Timing Parameters
    int unsigned sg_tck_ps;                            //!< Minimum Clock Cycle Time
    int unsigned trc_ps;                            //!< Active to Active/Auto Refresh command time
    int unsigned trcd_ps;                            //!< Active to Read/Write command time
    int unsigned trp_ps;                            //!< Precharge command period
    int unsigned trpa_ps;                            //!< ???
    int unsigned trrd_l_tck;                            //!< Active bank a to Active bank b command time to same bank group
    int unsigned trrd_s_tck;                            //!< Active bank a to Active bank b command time to different bank group
    int unsigned trrd_ps;                            //!< Active bank a to Active bank b command time
    int unsigned burst_length;                          //!< Burst Length
`ifdef DDRCTL_DDR
    // DDR4 Timing Parameters
    int unsigned ddr4_txp_ps;                            //!< Exit power down to a valid command
    int unsigned ddr4_txpdll_ps;                        //!< Exit precharge power down to READ or WRITE command (DLL-off mode)
    int unsigned ddr4_txsdll_tck;                        //!< SelfRefresh to commands requiring a locked DLL
    int unsigned ddr4_tras_min_ps;                        //!< Minimum Active to Precharge command time
    int unsigned ddr4_tras_max_ps;                        //!< Maximum Active to Precharge command time
    int unsigned ddr4_trefi_ps;                            //!< ???
    int unsigned ddr4_trfc_min_fgr_ps;
    int unsigned ddr4_trfc_min_ps;                        //!< Refresh to Refresh Command interval minimum value
    int unsigned ddr4_trfc_min2_ps;                        //!< Refresh to Refresh Command interval minimum value
    int unsigned ddr4_trfc_min4_ps;                        //!< Refresh to Refresh Command interval minimum value
    int unsigned ddr4_trfc_max_ps;                        //!< Refresh to Refresh Command Interval maximum value
    int unsigned ddr4_twtr_l_tck;                        //!< Write to Read command delay in clocks (sometimes higher than twtr/tck)
    int unsigned ddr4_twtr_s_tck;                        //!< Write to Read command delay in clocks (sometimes higher than twtr/tck)
    int unsigned ddr4_tfaw_ps;                            //!< Four Bank Activate window
    int unsigned ddr4_tzqinit_tck;                        //!< ZQ Cal (Init) time
    int unsigned ddr4_tzqoper_tck;                        //!< ZQ Cal (Long) time
    int unsigned ddr4_tzqcs_tck;                        //!< ZQ Cal (Short) time
    int unsigned ddr4_tmrd_tck;                            //!< Load Mode Register command cycle time
    int unsigned ddr4_tcke_ps;                            //!< CKE minimum high or low pulse width
    int unsigned ddr4_tccd_l_tck;                        //!< Cas to Cas command delay to same bank group
    int unsigned ddr4_tccd_s_tck;                        //!< Cas to Cas command delay to different bank group
    int unsigned ddr4_tmod_ps;                            //!< LOAD MODE to non-LOAD MODE command cycle time
    int unsigned ddr4_trtp_ps;                            //!< Read to Precharge command delay
    int unsigned ddr4_twr_ps;                            //!< Write recovery time
    int unsigned ddr4_tmpx_lh_ps;                        //!< CS_n Low hold time to CKE rising edge
    int unsigned ddr4_tmpx_s_tck;                        //!< CS setup time to CKE
    int unsigned ddr4_tckmpe_ps;                        //!< Valid clock requirement after MPSM entry
    int unsigned ddr4_tcksrx_ps;                        //!< minimum Valid Clock Requirement before SRX
    int unsigned ddr4_txmpdll_ps;                        //!< Exit MPSM to commands requiring a locked DLL

    int unsigned ddr4_tpl_tck;                            //!< C/A parity latency
    int unsigned ddr4_wcl_tck;                            //!< Write Command Latency
    int unsigned ddr4_twr_crc_dm_tck;                        //!< Write recovery time when CRC and DM are enabled (tWR_CRC_DM = twr + twr_crc_dm)
    int unsigned ddr4_twtr_l_crc_dm_tck;                    //!< tWTR_L's additional delay when CRC and DM are enabled (tWTR_L_CRC_DM = twtr_l_tck + twtr_l_crc_dm)
    int unsigned ddr4_twtr_s_crc_dm_tck;                    //!< tWTR_S's additional delay when CRC and DM are enabled (tWTR_S_CRC_DM = twtr_s_tck + twtr_s_crc_dm)
    int unsigned ddr4_tcrc_alert_pw_tck;                    //!< CRC ALERT_n pulse width (Max)
    int unsigned ddr4_tcrc_alert_ps;                        //!< CRC error to ALERT_n pulse width
    int unsigned ddr4_tpar_alert_pw_tck;                    //!< Pulse width of ALERT_N signal when C/A Parity Error is detected (Max)
    int unsigned ddr4_tpar_unknown_ps;                        //!< Commands not guaranteed to be executed during this time
    int unsigned ddr4_tpar_alert_on_ps;                        //!< Delay from errant command to ALERT_n assertion
    int unsigned ddr4_cal_tck;                            //!< CS to Command Address Latency when cal mode is enabled (and not in geardown mode)
    int unsigned ddr4_tdqsck_dll_off_ps;                    //!< Read data Clock to Data Strobe relationship with DLL-off mode
    int unsigned ddr4_tstab_ps;                            //!< ddr4 Stabilization time
    int unsigned ddr4_trfc_dlr_fgr_ps;
    int unsigned ddr4_trfc_dlr_ps;                        //!< Refresh to Refresh Command to different logical rank
    int unsigned ddr4_trfc_dlr2_ps;                        //!< Refresh to Refresh Command to different logical rank
    int unsigned ddr4_trfc_dlr4_ps;                        //!< Refresh to Refresh Command to different logical rank
    int unsigned ddr4_trrd_dlr_tck;                        //!< Active bank a to Active bank b command time to different logical rank
    int unsigned ddr4_tfaw_dlr_tck;                        //!< Four Bank Activate window to different logical rank
    int unsigned ddr4_tccd_dlr_tck;                        //!< Cas to Cas command delay to different logical rank

    int unsigned ddr4_tcwl_1st_set_tck;
    int unsigned ddr4_tcwl_2nd_set_tck;
    int unsigned ddr4_tcl_tck;
    int unsigned ddr4_tcmd_gear_tck;
    int unsigned ddr4_tsync_gear_tck;
    int unsigned ddr4_tgear_hold_tck;
    int unsigned ddr4_tgear_setup_tck;
    int unsigned ddr4_rankMap4;
    int unsigned ddr4_rankMap2;
    int unsigned ddr4_rankMap2i;
    int unsigned ddr4_tcl_rdbi_tck;

    // ddr5 timing parameters
    int unsigned ddr5_tcwl_tck;
    int unsigned ddr5_tcl_tck;
    int unsigned ddr5_tcl_rdbi_tck;

    int unsigned ddr5_tras_min_ps;                        //!< minimum ACT to PRE command period
    int unsigned ddr5_tccd_l_tck;                        //!< minimum CAS_n to CAS_n command delay for same bank group
    int unsigned ddr5_tccd_s_tck;                        //!< minimum CAS_n to CAS_n command delay for different bank group for BL16, and BC8(on-the-fly)
    int unsigned ddr5_tccd_m_tck;                        //!< Read to Read cmd delay for different bank in same bank group
    int unsigned ddr5_tccd_l_wr_tck;                        //!<write to write same bank group second write RMW
    int unsigned ddr5_tccd_l_wr2_tck;                        //!<write to write same bank group second write not RMW
    int unsigned ddr5_tccd_m_wr_tck;                        //!<write to write delay for different bank in same bank group

    int unsigned ddr5_tfaw_2k_tck;                        //!< minimum Four activate window for 2KB page size // TODO summary to ddr5_tfaw_ps
    int unsigned ddr5_tfaw_1k_tck;                        //!< minimum Four activate window for 1KB page size // TODO summary to ddr5_tfaw_ps
    int unsigned ddr5_tfaw_512_tck;                        //!< minimum Four activate window for 512B page size // TODO summary to ddr5_tfaw_ps
    int unsigned ddr5_tfaw_tck;                            //!< minimum Four activate window
    int unsigned ddr5_twtr_l_tck;                        //!< minimum Delay from start of internal write transaction to internal read command for same bank same bank group
    int unsigned ddr5_twtr_m_tck;                        //!< minimum Delay from start of internal write transaction to internal read command for diff bank same bank group
    int unsigned ddr5_tfaw_dlr_tck;                        //!<Four activate window to the different logical rank
    int unsigned ddr5_tfaw_slr_tck;                        //!<Four activate window to the same logical rank
    int unsigned ddr5_twtr_s_tck;                        //!< minimum Delay from start of internal write transaction to internal read command for the same bank group
    int unsigned ddr5_trtp_ps;                            //!< minimum Internal READ Command to PRECHARGE Command delay
    int unsigned ddr5_tppd_tck;                            //!< minimum PRECHARGE (PRE) to PRECHARGE (PRE) delay , // TODO need to add it to VIP
    int unsigned ddr5_twr_ps;                            //!< minimum WRITE recovery time

    // mode register read/write AC timing
    int unsigned ddr5_tmrr_tck;                            //!<minimum Mode Register Read command period
    int unsigned ddr5_tmrr_p_tck;                        //!<minimum Mode Register Read Pattern to Mode Register Read Pattern command spacing
    int unsigned ddr5_tmrw_tck;                            //!< minimum Mode Register Write command period
    int unsigned ddr5_tmrd_tck;                            //!< minimum Mode Register Set command delay

    // refresh timing parameter
    int unsigned ddr5_trefi1_ps;
    int unsigned ddr5_trefi2_ps;
    int unsigned ddr5_trfc_fgr_ps;
    int unsigned ddr5_trfc1_ps;                            //!<minimum Normal Refresh (REFab)
    int unsigned ddr5_trfc2_ps;                            //!<minimum FGR Refresh (REFab)
    int unsigned ddr5_trfcsb_ps;                        //!<minimum Same Bank Refresh (REFab)
    int unsigned ddr5_tdqs2dq_ps;
    int unsigned ddr5_tinit3_us;
    int unsigned ddr5_tinit4_us;

    // 3ds refresh timing parameter
    int unsigned ddr5_trefsbrd_ps;                        //!<minimum Same Bank Refresh to ACT delay

    int unsigned ddr5_trfc_dlr_fgr_ps;
    int unsigned ddr5_trfc1_dlr_ps;                        //!< minimum Normal Refresh with 3DS different logical rank
    int unsigned ddr5_trfc2_dlr_ps;                        //!<minimum Fine Granularity Refresh with 3DS different logical rank
    int unsigned ddr5_trfcsb_dlr_ps;                       //!<minimum Same Bank Refresh with 3DS different logical rank
    int unsigned ddr5_trefsbrd_dlr_ps;                     //!<minimum 3ds Same Bank Refresh to ACT delay
    int unsigned ddr5_trrd_dlr_tck;                        //!<minimum 3ds ACTIVATE to ACTIVATE Command delay to different logical rank
    int unsigned ddr5_tccd_dlr_tck;                        //!<minimum read to read command delay in different logical ranks
    int unsigned ddr5_tccd_wr_dlr_tck;                     //!<minimum write to write command delay in different logical ranks

    // ZQ calibration timing parameters
    int unsigned ddr5_tzqcal_ps;                        //!< minimum ZQ calibration timie
    int unsigned ddr5_tzqlat_ps;                        //!< minimum ZQ calibration latch timie

    // self refresh Timing parameters
    /* int unsigned ddr5_tcpded_ps;                        //!< minimum Command pass disable delay */
    int unsigned ddr5_tcsl_ps;                            //!< minimum Self-Refresh CS_n low Pulse width
    int unsigned ddr5_tcsh_srexit_ps;                        //!< minimum Self-Refresh exit CS_n High Pulse width
    int unsigned ddr5_tcsl_srexit_tck;                        //!< minimum Self-Refresh exit CS_n Low Pulse width
    int unsigned ddr5_tcksrx_ps;                        //!< minimum Valid Clock Requirement before SRX
    int unsigned ddr5_tcklcs_tck;                        //!< minimum Valid Clock Requirement after SRE
    int unsigned ddr5_tcasrx_ps;                        //!< minimum Self-Refresh exit CS_n high
    int unsigned ddr5_txs_ps;                            //!< minimum Exit Self-Refresh to next valid command not requireing DLL
    int unsigned ddr5_txs_dll_ps;                        //!< minimum Exit Self-Refresh to next valid command needing a DLL TBD

    // PDA timings parameters
    int unsigned ddr5_tpda_latch_min_ps;
    int unsigned ddr5_tpda_delay_ps;                        //!< minimum PDA Enumerate ID Command to any other command cycle time
    int unsigned ddr5_tpda_dqs_delay_min_ps;                    //!< minimum Delay to rising strobe edge used for sampling DQ during PDA operation
    int unsigned ddr5_tpda_dqs_delay_max_ps;                    //!< maximum Delay to rising strobe edge used for sampling DQ during PDA operation
    int unsigned ddr5_tpda_s_tck;                        //!< minimum DQ Setup Time during PDA operation
    int unsigned ddr5_tpda_h_tck;                        //!< minimum DQ Hold Time during PDA operation

    // MPC command timings parameters
    int unsigned ddr5_tmpc_delay_tck;                        //!< minimum MPC to any other valid command delay
    int unsigned ddr5_tmc_mpc_setup_tck;                    //!<minimum time between stable MPC command and first falling CS edge (SETUP)
    int unsigned ddr5_tmc_mpc_hold_tck;                        //!<minimum time between first rising CS edge and stable MPC command (HOLD)
    int unsigned ddr5_tmpc_cs_min_tck;                        //!< minimum Time CS_n is held low to register MPC command
    int unsigned ddr5_tmpc_cs_max_tck;                        //!< maximum Time CS_n is held low to register MPC command

    // MPSM command timings parameters
    int unsigned ddr5_tmpsmx_ps;                        //!< minimum MPSM exit to first valid command delay
    int unsigned ddr5_tmpdpdact_ps;                        //!< minimum MPSM DPD exit to first ACT command delay

    // Power down timing parameters;
    int unsigned ddr5_tcpded_ps;                        //!< minimum Command pass disable delay
    int unsigned ddr5_tpd_ps;                            //!< Minimum Power Down Time
    int unsigned ddr5_txp_ps;                            //!< minimum Exit Power Down to next valid command
    int unsigned ddr5_tactpden_tck;                        //!<minimum Timing of ACT command to Power Down Entry command
    int unsigned ddr5_tprpden_tck;                        //!<minimum Timing of PREab, PREsb or PREpb to Power Down Entry command
    int unsigned ddr5_trdpden_tck;                        //!<minimum Timing of RD or RD w/AP to Power Down Entry command
    int unsigned ddr5_twrpden_tck;                        //!<minimum Timing of WR to Power Down Entry command
    int unsigned ddr5_twrapden_tck;                        //!<minimum Timing of WR w/AP to Power Down Entry command
    int unsigned ddr5_trefpden_tck;                        //!<minimum Timing of REFab or REFsb command to Power Down Entry command
    int unsigned ddr5_tmrrpden_tck;                        //!<minimum Timing of MRR to command to Power Down Entry command
    int unsigned ddr5_tmrwpden_tck;                        //!<minimum Timing of MRW command to Power Down Entry command
    int unsigned ddr5_tmpcpden_tck;                        //!<minimum Timing of MPC command to Power Down Entry command

    // Initialization Timing parameters
    int unsigned ddr5_tinit4_ps;                        //!< minimum time for DRAM to register EXIT on CS with CMOS
    int unsigned ddr5_tinit5_tck;                        //!< minimum cycles required after CS_n HIGH
    int unsigned ddr5_txpr_ps;                            //!< minimum time from Exit Reset to first valid Configuration Command

    // VrefCA command Timing parameters
    int unsigned ddr5_tvrefca_delay_tck;                    //!< minimum VrefCA command to any other valid command delay
    int unsigned ddr5_tvrefca_cs_min_tck;                    //!< minimum Time CS_n is held low to register VrefCA command
    int unsigned ddr5_tvrefca_cs_max_tck;                    //!< maximum Time CS_n is held low to register VrefCA command

    // DQS interval OSCilator Read out Timing parameters
    int unsigned ddr5_tosco_ps;                            //!< minimum Delay time from OSC stop to Mode Register Readout

    // CRC Error handling Timing parameters
    int unsigned ddr5_tcrc_alert_ps;                        //!<CRC Alert Delay Time
    int unsigned ddr5_tcrc_alert_pw_ps;                        //!<CRC Alert Pulse Width

    // DDR4 RCD timing parameters
    int unsigned ddr4_rcd_tstaoff_ps;  //!<Clock delay through the register between the input clock and output clock
    int unsigned ddr4_rcd_tpdm_ps;     //!< Propagation delay, single bit switching; CK_t/CK_c cross point to output
    int unsigned ddr4_rcd_tpdm_rd_ps;  //!< MDQS to DQS Propagation Delay
    int unsigned ddr4_rcd_tpdm_wr_ps;  //!< DQS to MDQS Propagation Delay

	// RCD timing parameters
	// For PHYINIT
	int unsigned ddr5_rcd_tstaoff_ps;
	int unsigned ddr5_rcd_tpdm_ps;
	int unsigned ddr5_rcd_tpdm_rd_ps;  //!< MDQS to DQS Propagation Delay
	int unsigned ddr5_rcd_tpdm_wr_ps; //!< DQS to MDQS Propagation Delay
	// For Controller
	int unsigned ddr5_rcd_tstab01_min_ps;
	int unsigned ddr5_rcd_tstab01_max_ps;
	int unsigned ddr5_rcd_tpdex_ps;
	int unsigned ddr5_rcd_tcssr_ps;
	int unsigned ddr5_rcd_tcpded2srx_tck;
	int unsigned ddr5_rcd_tsrx2srx_tck;
	int unsigned ddr5_rcd_tckoff_ps;
	int unsigned ddr5_rcd_tckact_tck;
	int unsigned ddr5_rcd_tcsalt_tck;
	int unsigned ddr5_rcd_trpdx_ps;
	int unsigned ddr5_dimm_t_dcaw_tck; //!< Activate window by DIMM channel
	int unsigned ddr5_dimm_n_dcac_m1;  //!< DIMM Channel Activate Command Count in tDCAW
	int unsigned ddr5_read_crc_latency_adder; //!< Read latency adder when read CRC is enabled (depends on data rate)
	int unsigned ddr5_tdllk_tck;

    // For LRDIMM
    int unsigned ddr5_tcpded_db_ps;
    int unsigned ddr5_rcd_tcssr_db_ps;
    int unsigned ddr5_rcd_tcpded2srx_db_tck;
    int unsigned ddr5_rcd_tstab_dbcmd_ps;
    int unsigned ddr5_rcd_tstab_dbdata_ps;
	int unsigned ddr5_db_tmrrod1_tck;
	int unsigned ddr5_db_tmrr2nod1_tck;

	int unsigned ddr5_rcd_tmrc_tck;
	int unsigned ddr5_rcd_tmrc2n_tck;
	int unsigned ddr5_rcd_tmrd_l_tck;
	int unsigned ddr5_rcd_tmrd2n_l_tck;
	int unsigned ddr5_rcd_tmrd2n_l2_tck;
	int unsigned ddr5_rcd_tmrd_l2_tck;

`endif /* DDRCTL_DDR */

`ifdef DDRCTL_LPDDR
	// LPDDR4 Timing Parameters
	int unsigned lpddr4_tckb;							//!< Clock cycle time during boot
	int unsigned lpddr4_tpbr2pbr;						//!< Per-bank refresh to Per-bank refresh different bank time
	int unsigned lpddr4_tpbr2pbr_mp;						//!< Per-bank refresh to Per-bank refresh different bank time
	int unsigned lpddr4_tras_min;
	int unsigned lpddr4_tras_max;
	int unsigned lpddr4_trfcab;
	int unsigned lpddr4_trfcpb;
	int unsigned lpddr4_trfcab_mp;
	int unsigned lpddr4_trfcpb_mp;
	int unsigned lpddr4_trfiab;
	int unsigned lpddr4_trfipb;
	int unsigned lpddr4_twtr;
	int unsigned lpddr4_tfaw;
	int unsigned lpddr4_tzqreset;
	int unsigned lpddr4_tzqinit;
	int unsigned lpddr4_tzqcs;
	int unsigned lpddr4_tzqcsb;
	int unsigned lpddr4_tzqclb;
	int unsigned lpddr4_tzqcl;
	int unsigned lpddr4_tmrr;
	int unsigned lpddr4_tmrw;
	int unsigned lpddr4_tmrwb;
	int unsigned lpddr4_tmrd;
	int unsigned lpddr4_tmrdb;
	int unsigned lpddr4_tcke;
	int unsigned lpddr4_tckesr;
	int unsigned lpddr4_tccd;
	int unsigned lpddr4_tccd_bl32;
	int unsigned lpddr4_tccdmw;
	int unsigned lpddr4_tccdmw_bl32;
	int unsigned lpddr4_trtp;
	int unsigned lpddr4_twr;
	int unsigned lpddr4_tppd;
	int unsigned lpddr4_tdqsck;
	int unsigned lpddr4_tdqsck_max;
	int unsigned lpddr4_tdqsck_max_dr;
	int unsigned lpddr4_tosco;
	int unsigned lpddr4_tdqss;
	int unsigned lpddr4_tdqs2dq;
	int unsigned lpddr4_tdipw_ps;
	int unsigned lpddr4_trcd;
	int unsigned lpddr4_trp;
	int unsigned lpddr4_trpa;
	int unsigned lpddr4_trc;
	int unsigned lpddr4_cl;
	int unsigned lpddr4_cl_dbi;
	int unsigned lpddr4_cwl_seta;
	int unsigned lpddr4_cwl_setb;
	int unsigned lpddr4_nrtp;
	int unsigned lpddr4_nwr;
	int unsigned lpddr4_tcmdcke;
	int unsigned lpddr4_tmrwckel;
	int unsigned lpddr4_tmrwckelb;
	int unsigned lpddr4_tckckeh;
	int unsigned lpddr4_tckelck;
	int unsigned lpddr4_tsr;
	int unsigned lpddr4_todton_min;
	int unsigned lpddr4_tvrcg_enable;
	int unsigned lpddr4_tvrcg_disable;
	int unsigned lpddr4_txp;
	int unsigned lpddr4_trrd;
	int unsigned lpddr4_odtloff_latency_seta;
	int unsigned lpddr4_odtloff_latency_setb;
	int unsigned lpddr4_odtlon_latency_seta;
	int unsigned lpddr4_odtlon_latency_setb;
	int unsigned lpddr4_wdqson_seta;
	int unsigned lpddr4_wdqson_setb;
	int unsigned lpddr4_wdqsoff_seta;
	int unsigned lpddr4_wdqsoff_setb;
	int unsigned lpddr_tzqinit_min;
	int unsigned lpddr4_derated_trcd;
	int unsigned lpddr4_derated_tras_min;
	int unsigned lpddr4_derated_trp;
	int unsigned lpddr4_derated_trrd;
	int unsigned lpddr4_derated_trc;
	int unsigned lpddr4_trfmpb;
	int unsigned lpddr4_trfmpb_mp;
	// LPDDR5 Timing Parameters (generally in ps)
	int unsigned lpddr5_wck_ps;
	int unsigned lpddr5_cl_ps;
	int unsigned lpddr5_cl_dbi_ps;
	int unsigned lpddr5_twtr_s_ps;
	int unsigned lpddr5_twtr_l_ps;
	int unsigned lpddr5_twtr_ps;
	int unsigned lpddr5_tpbr2pbr_ps;
	int unsigned lpddr5_tpbr2pbr_mp_ps;
	int unsigned lpddr5_tpbr2act_ps;
	int unsigned lpddr5_trcd_ps;
	int unsigned lpddr5_trcd_write_ps;
	int unsigned lpddr5_tccdmw_tck;
	int unsigned lpddr5_tccdmw_bl32_tck;
	int unsigned lpddr5_trp_ps;
	int unsigned lpddr5_tsr_ps;
	int unsigned lpddr5_txsr_ps;
	int unsigned lpddr5_trfcab_ps;
	int unsigned lpddr5_trfcpb_ps;
	int unsigned lpddr5_trfcab_mp_ps;
	int unsigned lpddr5_trfcpb_mp_ps;
	int unsigned lpddr5_tcspd_ps;
	int unsigned lpddr5_tcmpd_ps;
	int unsigned lpddr5_tescke_ps;
	int unsigned lpddr5_tcmdpd_ps;
	int unsigned lpddr5_tcslck_ps;
	int unsigned lpddr5_tckcsh_ps;
	int unsigned lpddr5_txp_ps;
	int unsigned lpddr5_tpdxcsodton_ps;
	int unsigned lpddr5_tmrw_l_ps;
	int unsigned lpddr5_tcsh_ps;
	int unsigned lpddr5_tcsl_ps;
	int unsigned lpddr5_tmrwpd_ps;
	int unsigned lpddr5_tzqpd_ps;
	int unsigned lpddr5_trc_pab_ps;
	int unsigned lpddr5_trc_ppb_ps;
	int unsigned lpddr5_trpab_ps;
	int unsigned lpddr5_trppb_ps;
	int unsigned lpddr5_tras_min_ps;
	int unsigned lpddr5_tras_max_ps;
	int unsigned lpddr5_twr_ps;
	int unsigned lpddr5_tccd_l_tck;						//!< Cas to Cas command delay to same bank group
	int unsigned lpddr5_tccd_l_bl32_tck;					//!< Cas to Cas command delay to same bank group for BL32
	int unsigned lpddr5_tccd_s_tck;						//!< Cas to Cas command delay to different bank group
	int unsigned lpddr5_tccd_ps;
	int unsigned lpddr5_trrd_l_ps;						//!< Active bank a to Active bank b command time to same bank group
	int unsigned lpddr5_trrd_s_ps;						//!< Active bank a to Active bank b command time to different bank group
	int unsigned lpddr5_trrd_ps;
	int unsigned lpddr5_tfaw_ps;
	int unsigned lpddr5_trtp_ps;
	int unsigned lpddr5_tppd_tck;
	int unsigned lpddr5_tmrr_tck;
	int unsigned lpddr5_tmrw_ps;
	int unsigned lpddr5_tmrd_ps;
	int unsigned lpddr5_odtloff_rd_rdqs_tck;			//!< ODTLon_RD_RDQS
	int unsigned lpddr5_odtlon_rd_rdqs_tck;			//!< ODTLon_RD_RDQS
	int unsigned lpddr5_odtloff_rd_rdqs_bl32_tck;			//!< ODTLon_RD_RDQS
	int unsigned lpddr5_odtlon_rd_rdqs_bl32_tck;			//!< ODTLon_RD_RDQS
	int unsigned lpddr5_odtloff_rd_tck;			//!< ODTLon_RD_DQ
	int unsigned lpddr5_odtlon_rd_tck;			//!< ODTLon_RD_DQ
	int unsigned lpddr5_odtloff_rd_bl32_tck;			//!< ODTLon_RD_DQ
	int unsigned lpddr5_odtlon_rd_bl32_tck;			//!< ODTLon_RD_DQ
	int unsigned lpddr5_odtloff_tck;
	int unsigned lpddr5_odtloff_bl32_tck;
	int unsigned lpddr5_odtlon_tck;
	int unsigned lpddr5_odtlon_bl32_tck;
	int unsigned lpddr5_odton_min_ps;
	int unsigned lpddr5_odton_max_ps;
	int unsigned lpddr5_odtoff_min_ps;
	int unsigned lpddr5_odtoff_max_ps;
	int unsigned lpddr5_odt_rdon_min_ps;
	int unsigned lpddr5_odt_rdon_max_ps;
	int unsigned lpddr5_odt_rdoff_min_ps;
	int unsigned lpddr5_odt_rdoff_max_ps;
	int unsigned lpddr5_tzqreset_ps;
	int unsigned lpddr5_tzqlat_ps;
	int unsigned lpddr5_tzqcal_ps;
	int unsigned lpddr5_tzqstop_ps;
	int unsigned lpddr5_tzqoff_us;
	int unsigned lpddr5_tvrcg_enable_ps;
	int unsigned lpddr5_tvrcg_disable_ps;
	// suffix _wck to indicate units are tWCK
	int unsigned lpddr5_wckenl_rd_wck;
	int unsigned lpddr5_wckpre_rd_static_wck;
	int unsigned lpddr5_wckpre_rd_toggle_wck;
	int unsigned lpddr5_wckenl_wr_seta_wck;
	int unsigned lpddr5_wckenl_wr_setb_wck;
	int unsigned lpddr5_wckpre_wr_static_wck;
	int unsigned lpddr5_wckpre_wr_toggle_wck;
	int unsigned lpddr5_wckpre_static_tck;
	int unsigned lpddr5_wckpre_toggle_wr_tck;
	int unsigned lpddr5_wckpre_toggle_rd_tck;
	int unsigned lpddr5_wckenl_rd_tck;
	int unsigned lpddr5_wckenl_wr_tck;
	int unsigned lpddr5_wckenl_fs_tck;
	int unsigned lpddr5_twck_en_wck;
	int unsigned lpddr5_twck_toggle_en_wck;
	int unsigned lpddr5_twck_toggle_dis_wck;
	int unsigned lpddr5_twckstop_ps;
	int unsigned lpddr5_tpdn_ps;
	int unsigned lpddr5_tpdn_dsm_ms;
	int unsigned lpddr5_txsr_dsm_us;
	int unsigned lpddr5_trbtp_ps;
	int unsigned lpddr5_tespd_ps;
	int unsigned lpddr5_wl_tck;
	int unsigned lpddr5_rl_tck;
	int unsigned lpddr5_nrbtp;							//!< READ Burst end to PRECHARGE command delay
	int unsigned lpddr5_nwr;
	int unsigned lpddr5_bl_n_min_tck;						//!< Effective burst length
	int unsigned lpddr5_bl_n_max_tck;						//!< Effective burst length
	int unsigned lpddr5_bl_n_min_bl32_tck;					//!< Effective burst length
	int unsigned lpddr5_bl_n_max_bl32_tck;					//!< Effective burst length
	int unsigned lpddr5_twck_pst_wck;
	int unsigned lpddr5_wckdqo_max_ps;
	int unsigned lpddr5_wckdqo_ps;
	int unsigned lpddr5_wckdqi_ps;
	int unsigned lpddr5_trpst;
	int unsigned lpddr5_trefi_ps;						//!< all bank average refresh interval
	int unsigned lpddr5_trefipb_ps;						//!< per bank average refresh interval
	int unsigned lpddr5_derated_trcd_ps;
	int unsigned lpddr5_derated_trcd_write_ps;
	int unsigned lpddr5_derated_tras_min_ps;
	int unsigned lpddr5_derated_trpab_ps;
	int unsigned lpddr5_derated_trppb_ps;
	int unsigned lpddr5_derated_trrd_ps;
	int unsigned lpddr5_derated_trcab_ps;
	int unsigned lpddr5_derated_trcpb_ps;
	int unsigned lpddr5_tosco;
	int unsigned lpddr5_trtw_tck;
	int unsigned lpddr5_trtw_bl32_tck;
	int unsigned lpddr5_trtw_s_tck;        //!< tRTW for different BG
	int unsigned lpddr5_trtw_s_bl32_tck;        //!< tRTW for different BG
	int unsigned lpddr5_trfmpb_ps;
	int unsigned lpddr5_trfmpb_mp_ps;
`endif /* DDRCTL_LPDDR */
    int unsigned wr2pre;                            //!< min time between write and precharge to the same bank
} ddrTimingParameters_t;

/**
 * @brief Structure containing parameters to program DWC DDR umctl registers.
 * The variables here are pre-calculated timings to help
 * program some register fields.
 */
typedef struct {
    int unsigned cl[`UMCTL2_FREQUENCY_NUM];                    //! CL
    int unsigned cl_dbi[`UMCTL2_FREQUENCY_NUM];                    //!<
    int unsigned cwl_x[`UMCTL2_FREQUENCY_NUM];                    //!< CWL adjusted.
    int unsigned twr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Write recovery time
    int unsigned twtr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Write to Read command delay
    int unsigned twtr_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!<
    int unsigned tfaw[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Four Bank Activate window
    int unsigned txp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Exit power down to a valid command
    int unsigned txpdll[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ras_max[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ras_min[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rtp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rc[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_wr2rd_m[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wdqspreext[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];

    int unsigned odton_min[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned odton[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_mrw[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Mode Register Write command period
    int unsigned t_mr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Load-mode command to next valid command period (tmrd >= tmrw)
    int unsigned t_mod[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rcd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Active to Read/Write command time
    int unsigned t_ccd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Cas to Cas command delay
    int unsigned t_rrd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!< Active bank a to Active bank b command time
    int unsigned t_rp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_cksrx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_cksre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ckesr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_cke[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_mrw_l[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_csh[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_mrd_pda[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_wr_mpr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned odtloff[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned odtloff_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned odtlon[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned odtlon_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_t_rddata_en[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_tphy_wrlat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_tphy_wrdata[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned cmd_lat_adder[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_t_dram_clk_disable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_t_dram_clk_enable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_t_init_start[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_t_init_complete[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_t_ctrl_delay_memclk[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];

    //ddr4
    int unsigned t_sync_gear[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_cmd_gear[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_gear_setup[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_gear_hold[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];

    //ddr5
    int unsigned t_csl[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];

`ifdef UMCTL2_CID_EN
    int unsigned t_ccd_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rrd_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!< ddr4 and ddr5
    int unsigned t_faw_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_faw_slr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_wr2rd_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!< ddr5
    int unsigned t_rd2wr_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!< ddr5
    int unsigned t_refsbrd_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rfcsb_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
`endif /* UMCTL2_CID_EN */

`ifdef DDRCTL_LPDDR
    int unsigned t_rcd_write[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned derated_t_rcd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned derated_t_rcd_write[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned derated_t_ras_min[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned derated_t_rp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned derated_t_rrd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned derated_t_rc[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned tINITTMG1[`DWC_DDRCTL_NUM_CHANNEL];                //!< min cke low time before RESET_n high
    int unsigned tINITTMG3[`DWC_DDRCTL_NUM_CHANNEL];                //!< min idle time before first MRW/MRR command.
    int unsigned t_pbr2pbr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_pbr2pbr_mp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_pbr2act[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned tINIT2;                            //!<
    int unsigned tINIT3;                            //!< used post_cke
    int unsigned tINIT4[`UMCTL2_FREQUENCY_NUM];                    //!< min idle time before first CKE high.
    int unsigned t_rrd_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!< Activate command to different bank group than prior Activate command
    int unsigned t_osco[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_pdn[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
`endif /* DDRCTL_LPDDRDDRCTL_LPDDR */

	int unsigned wl[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< write latency
	int unsigned rl[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< read latency
	int unsigned t_rbtp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< LPDDR5
	int unsigned t_cmdcke[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_vrcg_enable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_vrcg_disable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned lpddr4_diff_bank_rwa2pre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Time between Read/Write/Masked Write/Act and Precharge to diff bank
	int unsigned wra2pre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Time between write with AP and activate to same bank
	int unsigned rda2pre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Time between write read AP and activate to same bank.
	int unsigned rd2wr_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Minimum time from read command to write command for different bank group
	int unsigned rd2wr_s_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Minimum time from read command to write command for different bank group
	int unsigned max_rd_sync[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Maximum time between read commands without a new WCK2CK sync Start
	int unsigned max_wr_sync[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Maximum time between write commands without a new WCK2CK sync start
	int unsigned nwr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< nWR
	int unsigned nrtp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< nRTP for LPDDR4
	int unsigned nrbtp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< nRBTP for LPDDR5
	int unsigned dfi_twck_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_en_rd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_en_wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_en_fs[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_dis[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_fast_toggle[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_toggle[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_toggle_cs[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_toggle_post[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned dfi_twck_toggle_post_rd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned rd2mr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< Time from Read to MRW/MRR command
	int unsigned wr2mr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< Time from Write to MRW/MRR command
	int unsigned mrr2rd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< Time from MRR to Read command
	int unsigned mrr2wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];		//!< Time from MRR to Write command
	int unsigned mrr2wr_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to Write command
	int unsigned mrr2mrw[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to MRW command
	int unsigned ws_off2ws_fs[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to MRW command
	int unsigned t_wcksus[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to MRW command
	int unsigned ws_fs2wck_sus[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];	//!< Time from MRR to MRW command
	// ddr4
	int unsigned t_xs_fast_min[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_xs_min[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_mpx_lh[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_mpx_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_ckmpe[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned post_mpsm_gap_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];

    // ddr5
    int unsigned t_pd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];        //!<tPD ddr5
    int unsigned t_mpsmx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tMPSMX ddr5
    int unsigned t_mpdpxact[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tMPDPADACT ddr5
    int unsigned t_pda_latch[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tPDA_LATCH ddr5
    int unsigned t_pda_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tPDA_DELAY ddr5
    int unsigned t_pda_dqs_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];//!<tPDA_DQS_DELAY ddr5
    int unsigned t_pda_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<t_pda_s ddr5
    int unsigned t_pda_h[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tPDA_H ddr5

    int unsigned t_cpded[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCPDED ddr5
    int unsigned t_casrx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCASRX ddr5
    int unsigned t_csh_srexit[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCSH_SRexit ddr5
    int unsigned t_csl_srexit[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCSl_SRexit ddr5

    int unsigned t_mpc_cs[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tMPC_CS ddr5
    int unsigned t_mpc_setup[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tMPC_Setup ddr5
    int unsigned t_mpc_hold[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tMPC_Hold ddr5
    int unsigned t_mpc_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tMPC_DELAY ddr5
    int unsigned t_ccd_w[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_L_WR write to write same bank same bank group second write write RMW
    int unsigned t_ccd_w_m[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_L_WR write to write diff bank same bank group second write write RMW
    int unsigned t_ccd_w2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_L_WR2 write to write same bank group second write not RMW
    int unsigned t_wr2rd_dpr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<wr2rd_dpr
    int unsigned t_rd2wr_dpr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<rd2wr_dpr
    int unsigned t_ccd_w_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_S,min WR to WR delay to diff BG
    int unsigned t_ccd_r_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_S,min RD to RD delay to diff BG
    int unsigned t_ccd_r_l[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_S,min RD to RD delay to same bank same BG
    int unsigned t_ccd_r_m[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];    //!<tCCD_S,min RD to RD delay to diff bank same BG
    int unsigned t_mrr2mpc[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned lrank_rd2rd_gap[`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned lrank_wr2wr_gap[`DWC_DDRCTL_NUM_CHANNEL];
`ifdef MEMC_NUM_RANKS_GT_1
    int unsigned wr2rd_dr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_dr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_dr_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_dr_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_dr_wck_on[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_dr_wck_on[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_wck_on[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_wck_on[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_dr_wck_on_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_dr_wck_on_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_wck_on_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_wck_on_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_wck_on_dq_odt_nt_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_wck_on_dq_odt_nt_odt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
`endif /* MEMC_NUM_RANKS_GT_1 */
/* MEMC_BURST_LENGTH_32 */
`ifdef DDRCTL_BURST_LENGTH_X2
    int unsigned t_ccd_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_mw_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2pre_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2pre_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wra2pre_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rda2pre_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_s_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_s_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_s_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2mr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2mr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned max_rd_sync_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned max_wr_sync_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_dr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_dr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_dr_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_dr_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_dr_wck_on_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_dr_wck_on_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_wck_on_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_wck_on_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_dr_wck_on_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_dr_wck_on_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_wck_on_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_wck_on_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_rd_gap_wck_on_dq_odt_nt_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned diff_rank_wr_gap_wck_on_dq_odt_nt_odt_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
`endif /* DDRCTL_BURST_LENGTH_X2 */ 

`ifdef DDRCTL_WR_CRC_RETRY
    int unsigned t_wr_crc_retry_window[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
`endif

`ifdef DDRCTL_CAPAR_RETRY
    int unsigned capar_retry_window[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned retry_add_rd_lat_en[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned retry_add_rd_lat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned extra_rd_retry_window[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned dfi_t_phy_rdlat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
`endif

    int unsigned refab_hi_sch_gap[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned refsb_hi_sch_gap[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];

	int unsigned mrr_des_timing_unit_sel[`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned ci_mrr_des1[`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned ci_mrr_des2[`DWC_DDRCTL_NUM_CHANNEL];

	// ddr5 RCD
	int unsigned t_stab01[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_cssr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_cpded2srx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_srx2srx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_ckoff[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_ckact[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	int unsigned t_csalt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];

    int unsigned lpddr5_cdd;
    int unsigned tphy_wckcsgap;
    int unsigned t_xs_dll_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
`ifdef DDRCTL_TWO_TIMING_SETS_EN
    int unsigned cl_2[`UMCTL2_FREQUENCY_NUM];
    int unsigned cwl_x_2[`UMCTL2_FREQUENCY_NUM];
    int unsigned twr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned twtr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned twtr_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rtp_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned tfaw_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ras_min_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2pre_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2pre_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rc_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned rd2wr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_wr2rd_m_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_mr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rcd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rrd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rp_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_xs_x32_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_xs_dll_x32_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rrd_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned wr2rd_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_w2_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ppd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rp_ca_parity_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_wr2rd_dpr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rd2wr_dpr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_w_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_r_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_w_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_w_m_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_r_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_ccd_r_m_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_refi_x1_x32_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rfc_min_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_refsbrd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rfcsb_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_zq_long_nop_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_zq_short_nop_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_mrr2mpc_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL]; //!< <minimum time from Mode Register Read to MPC command
`ifdef UMCTL2_CID_EN
    int unsigned t_ccd_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rrd_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_faw_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_wr2rd_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rd2wr_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rfc_min_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_refsbrd_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned t_rfcsb_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
`endif

    int unsigned refab_hi_sch_gap_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
    int unsigned refsb_hi_sch_gap_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];

`endif
} mctl_pre_cfg;

/**
 * @brief Type definition of structure describing mode register fields.
 */

typedef struct {
    rand shortint unsigned wr_recovery;
    rand shortint unsigned dll_reset;
    rand shortint unsigned cl;                                //!< CAS Latency
    rand shortint unsigned burst_type;
    rand shortint unsigned burst_length;
} ddr4_mr0_t;

typedef struct {
    rand shortint unsigned rtt_nom;
    rand shortint unsigned wr_leveling_enable;
    rand shortint unsigned al;
    rand shortint unsigned output_driver_impedance;
    rand shortint unsigned dll_enable;
} ddr4_mr1_t;

typedef struct {
    rand shortint unsigned write_crc;
    rand shortint unsigned rtt_wr;
    rand shortint unsigned auto_self_ref;
    rand shortint unsigned cwl;
} ddr4_mr2_t;

typedef struct {
    rand shortint unsigned wcl;
    rand shortint unsigned geardown;
    rand shortint unsigned mpr_op;
    rand shortint unsigned mpr_ps;
    rand shortint unsigned fine_granularity_refresh;
} ddr4_mr3_t;

typedef struct {
    rand shortint unsigned wr_preamble;
    rand shortint unsigned rd_preamble;
    rand shortint unsigned selfref_abort;
    rand shortint unsigned cal;
    rand shortint unsigned refresh_mode;
    rand shortint unsigned refresh_range;
} ddr4_mr4_t;

typedef struct {
    rand shortint unsigned read_dbi;
    rand shortint unsigned write_dbi;
    rand shortint unsigned data_mask;
    rand shortint unsigned ca_parity_persistent;
    rand shortint unsigned rtt_park;
    rand shortint unsigned dis_odt_input_buf_in_pd;
    rand shortint unsigned parity_latency_mode;
} ddr4_mr5_t;

typedef struct {
    rand shortint unsigned tccd_l;
} ddr4_mr6_t;

// umctl5 ddr5
typedef struct {
    rand shortint unsigned burst_length;
    rand shortint unsigned cl;                                //!<CAS latency
} ddr5_mr0_t;

typedef struct {
    rand shortint unsigned rd_preamble_enable;
    rand shortint unsigned wr_leveling;
    rand shortint unsigned ddr5_2n_mode;
    rand shortint unsigned mpsm;
    rand shortint unsigned cs_assertion_duration;
    rand shortint unsigned dev15_mpsm;
    rand shortint unsigned internal_wr_timing;
} ddr5_mr2_t;

typedef struct {
    rand shortint unsigned wr_leveling_internal_lower_byte;
    rand shortint unsigned wr_leveling_internal_upper_byte;
} ddr5_mr3_t;

typedef struct {
    rand shortint unsigned refresh_trfc_mode;
    rand shortint unsigned refresh_rate;
} ddr5_mr4_t;

typedef struct {
    rand shortint unsigned data_output_disable;
    rand shortint unsigned pull_up_output_drv_impedance;
    rand shortint unsigned tdqs_enable;
    rand shortint unsigned dm_enable;
    rand shortint unsigned pull_down_output_drv_impedance;
} ddr5_mr5_t;

typedef struct {
    rand shortint unsigned trtp;
    rand shortint unsigned wr_recovery;
} ddr5_mr6_t;

typedef struct {
    rand shortint unsigned rd_preamble;
    rand shortint unsigned wr_preamble;
    rand shortint unsigned rd_postamble;
    rand shortint unsigned wr_postamble;
} ddr5_mr8_t;

typedef struct {
    rand shortint unsigned tccd_l;
} ddr5_mr13_t;

typedef struct {
    rand shortint unsigned auto_ecs_in_selfref;
    rand shortint unsigned etc;
} ddr5_mr15_t;

typedef struct {
    rand shortint unsigned rtt_park;
    rand shortint unsigned rtt_wr;
} ddr5_mr34_t;

typedef struct {
    rand shortint unsigned rtt_nom_wr;
    rand shortint unsigned rtt_nom_rd;
} ddr5_mr35_t;

typedef struct {
    rand shortint unsigned odtlon_wr_offset;
    rand shortint unsigned odtloff_wr_offset;
} ddr5_mr37_t;

typedef struct {
    rand shortint unsigned odtlon_wr_nt_offset;
    rand shortint unsigned odtloff_wr_nt_offset;
} ddr5_mr38_t;

typedef struct {
    rand shortint unsigned odtlon_rd_nt_offset;
    rand shortint unsigned odtloff_rd_nt_offset;
} ddr5_mr39_t;

typedef struct {
    rand shortint unsigned rd_dqs_offset;
} ddr5_mr40_t;

typedef struct {
    rand shortint unsigned osc_run_time;
} ddr5_mr45_t;

typedef struct {
    rand shortint unsigned rd_crc_enable;
    rand shortint unsigned wr_crc_enable_lower_nibble;
    rand shortint unsigned wr_crc_enable_upper_nibble;
    rand shortint unsigned wr_crc_error_status;
    rand shortint unsigned wr_crc_auto_disable_enable;
    rand shortint unsigned wr_crc_auto_disable_status;
} ddr5_mr50_t;

typedef struct {
    rand shortint unsigned wr_crc_auto_disable_thre;
} ddr5_mr51_t;

typedef struct {
    rand shortint unsigned wr_crc_auto_disable_window;
} ddr5_mr52_t;

typedef struct {
    rand shortint unsigned rfm_required;
    rand shortint unsigned raa_initial_management_threshold;
    rand shortint unsigned raa_maximum_management_threshold;
} ddr5_mr58_t;

typedef struct {
    rand shortint unsigned raa_counter_decr_per_ref_cmd;
} ddr5_mr59_t;

typedef struct {
rand ddr5_mr0_t mr0;
rand ddr5_mr2_t mr2;
rand ddr5_mr3_t mr3;
rand ddr5_mr4_t mr4;
rand ddr5_mr5_t mr5;
rand ddr5_mr6_t mr6;
rand ddr5_mr8_t mr8;
rand ddr5_mr13_t mr13;
rand ddr5_mr15_t mr15;
rand ddr5_mr34_t mr34;
rand ddr5_mr35_t mr35;
rand ddr5_mr37_t mr37;
rand ddr5_mr38_t mr38;
rand ddr5_mr39_t mr39;
rand ddr5_mr40_t mr40;
rand ddr5_mr45_t mr45;
rand ddr5_mr50_t mr50;
rand ddr5_mr51_t mr51;
rand ddr5_mr52_t mr52;
rand ddr5_mr58_t mr58[MEMC_NUM_RANKS];
rand ddr5_mr59_t mr59[MEMC_NUM_RANKS];
} ddr5_mode_registers_t;

typedef struct {
rand ddr4_mr0_t mr0;
rand ddr4_mr1_t mr1;
rand ddr4_mr2_t mr2;
rand ddr4_mr3_t mr3;
rand ddr4_mr4_t mr4;
rand ddr4_mr5_t mr5;
rand ddr4_mr6_t mr6;
} ddr4_mode_registers_t;

typedef struct {
    rand shortint unsigned refresh_mode;
    rand shortint unsigned latency_mode;
    rand shortint unsigned rfm_support;
    rand shortint unsigned rzqi;
    rand shortint unsigned scls;
    rand shortint unsigned catr;
} lpddr4_mr0_t;

typedef struct {
    rand shortint unsigned rd_postamble;
    rand shortint unsigned wr_recovery;
    rand shortint unsigned rd_preamble;
    rand shortint unsigned wr_preamble;
    rand shortint unsigned burst_length;
} lpddr4_mr1_t;

typedef struct {
    rand shortint unsigned wls;
    rand shortint unsigned rl_wl;
} lpddr4_mr2_t;

typedef struct {
    rand shortint unsigned write_dbi;
    rand shortint unsigned read_dbi;
    rand shortint unsigned pdds;
    rand shortint unsigned pprp;
    rand shortint unsigned wr_postamble;
    rand shortint unsigned pu_cal;
} lpddr4_mr3_t;

typedef struct {
    rand shortint unsigned vr_ca;
    rand shortint unsigned vref_ca;
} lpddr4_mr12_t;

typedef struct {
    rand shortint unsigned ca_odt;
    rand shortint unsigned dq_odt;
} lpddr4_mr11_t;

typedef struct {
    rand shortint unsigned fsp_op;
    rand shortint unsigned fsp_wr;
    rand shortint unsigned dmd;
} lpddr4_mr13_t;

typedef struct {
    rand shortint unsigned vr_dq;
    rand shortint unsigned vref_dq;
} lpddr4_mr14_t;

typedef struct {
    rand shortint unsigned odtd;
    rand shortint unsigned odtd_ca;
    rand shortint unsigned odtd_cs;
    rand shortint unsigned odtd_ck;
    rand shortint unsigned soc_odt;
} lpddr4_mr22_t;

typedef struct {
    rand shortint unsigned dqs_interval;
} lpddr4_mr23_t;

typedef struct {
    rand shortint unsigned scl;
} lpddr4_mr26_t;

typedef struct {
rand lpddr4_mr0_t mr0;
rand lpddr4_mr1_t mr1;
rand lpddr4_mr2_t mr2;
rand lpddr4_mr3_t mr3;
rand lpddr4_mr11_t mr11;
rand lpddr4_mr12_t mr12;
rand lpddr4_mr13_t mr13;
rand lpddr4_mr14_t mr14;
rand lpddr4_mr22_t mr22;
rand lpddr4_mr23_t mr23;
rand lpddr4_mr26_t mr26;
} lpddr4_mode_registers_t;

typedef struct {
	rand shortint unsigned per_pin_dfe;
	rand shortint unsigned unified_nt_odt;
	rand shortint unsigned dmi_output_behavior_mode;
	rand shortint unsigned optimized_refresh_mode;
	rand shortint unsigned enhanced_wck_always_on_mode_support;
	rand shortint unsigned latency_mode;
	rand shortint unsigned enhanced_nt_odt;

} lpddr5_mr0_t;

typedef struct {
    rand shortint unsigned write_latency;
    rand shortint unsigned ck_mode;
    rand shortint unsigned arfm_support;
    rand shortint unsigned drfm_support;
} lpddr5_mr1_t;

typedef struct {
    rand shortint unsigned nwr;
    rand shortint unsigned rl_nrtp;
} lpddr5_mr2_t;

typedef struct {
    rand shortint unsigned write_dbi;
    rand shortint unsigned read_dbi;
    rand shortint unsigned wls;
    rand shortint unsigned bk_bg_org;
    rand shortint unsigned pdds;
} lpddr5_mr3_t;

typedef struct {
    rand int unsigned rdqs_pst_mode;
    rand int unsigned rdqs_pst;
    rand int unsigned rdqs_pre_2;
    rand int unsigned wck_pst;
    rand int unsigned rdqs_pre;
} lpddr5_mr10_t;

typedef struct {
    rand shortint unsigned cs_odt_op;
    rand shortint unsigned ca_odt;
    rand shortint unsigned nt_odt;
    rand shortint unsigned dq_odt;
} lpddr5_mr11_t;

typedef struct {
    rand shortint unsigned vbs;
    rand shortint unsigned vref_ca;
} lpddr5_mr12_t;

typedef struct {
    rand shortint unsigned dual_vdd2;
    rand shortint unsigned dmd;
    rand shortint unsigned vro;
    rand shortint unsigned thermal_offset;
} lpddr5_mr13_t;

typedef struct {
    rand shortint unsigned vdlc;
    rand shortint unsigned vref_dq;
} lpddr5_mr14_t;

typedef struct {
    rand shortint unsigned vref_dq;
} lpddr5_mr15_t;

typedef struct {
    rand shortint unsigned cbt;
    rand shortint unsigned vrcg;
    rand shortint unsigned fsp_op;
    rand shortint unsigned fsp_wr;
} lpddr5_mr16_t;

typedef struct {
    rand shortint unsigned odtd;
    rand shortint unsigned odtd_ca;
    rand shortint unsigned odtd_cs;
    rand shortint unsigned odtd_ck;
    rand shortint unsigned soc_odt;
} lpddr5_mr17_t;

typedef struct {
    rand shortint unsigned ckr;
    rand shortint unsigned wck2ck_leveling;
    rand shortint unsigned wck_on;
    rand shortint unsigned wck_fm;
    rand shortint unsigned wck_odt;
} lpddr5_mr18_t;

typedef struct {
    rand shortint unsigned dvfsq;
    rand shortint unsigned dvfsc;
} lpddr5_mr19_t;

typedef struct {
    rand shortint unsigned wck_mode;
    rand shortint unsigned rdqs;
} lpddr5_mr20_t;

typedef struct {
    rand shortint unsigned dcfe;
    rand shortint unsigned wxfs;
} lpddr5_mr21_t;

typedef struct {
    rand shortint unsigned wecc;
    rand shortint unsigned recc;
} lpddr5_mr22_t;

typedef struct {
    rand shortint unsigned pasr_mask;
} lpddr5_mr23_t;

typedef struct {
    rand shortint unsigned dfes;
    rand shortint unsigned dfequ;
    rand shortint unsigned dfeql;
} lpddr5_mr24_t;

typedef struct {
    rand shortint unsigned ck_bus_term;
    rand shortint unsigned ca_bus_term;
    rand shortint unsigned parc;
    rand shortint unsigned optimized_refresh_mode;
} lpddr5_mr25_t;

typedef struct {
    rand shortint unsigned dwck_rdws_train;
} lpddr5_mr26_t;

typedef struct {
    rand shortint unsigned raa_mult;
    rand shortint unsigned raa_imt;
    rand shortint unsigned raa_rfm;
} lpddr5_mr27_t;

typedef struct {
    rand shortint unsigned zq_int;
    rand shortint unsigned zq_stop;
    rand shortint unsigned zq_reset;
} lpddr5_mr28_t;

typedef struct {
    rand shortint unsigned wck2dqi_runtime;
} lpddr5_mr37_t;

typedef struct {
    rand shortint unsigned wck2dqo_runtime;
} lpddr5_mr40_t;

typedef struct {
    rand shortint unsigned pdfec;
    rand shortint unsigned nt_dq_odt;
    rand shortint unsigned dvfsc_edvfsc_support;
    rand shortint unsigned edvfsc_odt_support;
} lpddr5_mr41_t;

typedef struct {
    rand shortint unsigned enh_rdqs;
    rand shortint unsigned fifo_rdqs_training;
} lpddr5_mr46_t;

typedef struct {
    rand shortint unsigned arfm;
    rand shortint unsigned rfm_sbc;
    rand shortint unsigned rfm_sb;
    rand shortint unsigned raa_dec;
} lpddr5_mr57_t;

typedef struct {
    rand shortint unsigned brc_support;
} lpddr5_mr75_t;


//todo mr29,mr30,mr31,mr32,mr33,mr34,mr37,mr40
//todo mr0,mr26,mr41,mr46 for 5A
typedef struct {
rand lpddr5_mr0_t mr0;
rand lpddr5_mr1_t mr1;
rand lpddr5_mr2_t mr2;
rand lpddr5_mr3_t mr3;
rand lpddr5_mr10_t mr10;
rand lpddr5_mr11_t mr11;
rand lpddr5_mr12_t mr12;
rand lpddr5_mr13_t mr13;
rand lpddr5_mr14_t mr14;
rand lpddr5_mr15_t mr15;
rand lpddr5_mr16_t mr16;
rand lpddr5_mr17_t mr17;
rand lpddr5_mr18_t mr18;
rand lpddr5_mr19_t mr19;
rand lpddr5_mr20_t mr20;
rand lpddr5_mr21_t mr21;
rand lpddr5_mr22_t mr22;
rand lpddr5_mr23_t mr23;
rand lpddr5_mr24_t mr24;
rand lpddr5_mr25_t mr25;
rand lpddr5_mr26_t mr26;
rand lpddr5_mr27_t mr27;
rand lpddr5_mr28_t mr28;
rand lpddr5_mr37_t mr37;
rand lpddr5_mr40_t mr40;
rand lpddr5_mr41_t mr41;
rand lpddr5_mr46_t mr46;
rand lpddr5_mr57_t mr57;
rand lpddr5_mr75_t mr75;
} lpddr5_mode_registers_t;

typedef struct {                        // RC0A: RDIMM Operating Speed
    rand shortint unsigned operating_speed;                        // DA[2:0] Operating speed
    //rand shortint unsigned context;                            // DA[3] Context for operation training
} ddr4_rc0a_t;

typedef struct {                        // RC0D: DIMM Configuration Control Word
    rand shortint unsigned cs_mode;                            // DA[1:0] CS mode 0:Direct DualCS, 1:Direct QuadCS, 2:Reserved, 3:Encoded QuadCS
    rand shortint unsigned dimm_type;                            // DA[2] DIMM Type 0:LRDIMM, 1:RDIMM
    rand shortint unsigned address_mirroring;                        // DA[3] Address mirroring for MRS commands 0:Disabled, 1:Enabled
} ddr4_rc0d_t;

typedef struct {                        // RC0E: Parity Control Word (Parity Enable, ALERT_n assertion, ALERT_n Re-enable)
    rand shortint unsigned parity_check;                        // DA[0] Parity enable    0: disable, 1: enable
                                        // DA[1] Reserved
    rand shortint unsigned alert_n_assertion;                        // DA[2] ALERT_n assertion 0: Static ALERT_n Assertion Mode, 1: Pulsed ALERT_n Mode
    rand shortint unsigned alert_n_reenable;                        // DA[3] ALERT_n re-enable 0: Parity checking remains disabled after ALERT_n pulse, 1: Parity Checking is re-enabled after ALERT_n pulse
} ddr4_rc0e_t;

typedef struct {                        // RC0F: Command Latency Adder Control Word
    rand shortint unsigned latency_adder_nladd_to_all_dram_cmd;            // DA[2:0] Latency adder nLadd to all DRAM commands
                                        // DA[3] Reserved
} ddr4_rc0f_t;

typedef struct {                        // RC3X: Fine Granularity RDIMM Operating Speed
    rand shortint unsigned fine_granularity_operating_speed;                // DA[7:0] Fine Granularity Operating Speed
} ddr4_rc3x_t;

typedef struct {
rand ddr4_rc0a_t rc0a;
rand ddr4_rc0d_t rc0d;
rand ddr4_rc0e_t rc0e;
rand ddr4_rc0f_t rc0f;
rand ddr4_rc3x_t rc3x;
} ddr4_control_words_t;
////////////////////////////////////
typedef struct {
    rand shortint unsigned ca_rate;                    // 0: SDR, 1: DDR
    rand shortint unsigned sdr_mode;                   // 0: SDR1, 1: SDR2
} ddr5_rw00_t;

typedef struct {
    rand shortint unsigned parity_check;                // 0: disable, 1: enable
    rand shortint unsigned dram_if_cmds;                    // 0: Block, 1: Not block
    rand shortint unsigned databuffer_cmds;            // 0: Block, 1: Not block
    rand shortint unsigned alert_n_assertion;            // 0: Static ALERT_n Assertion Mode 1: Pulsed ALERT_n Mode
    rand shortint unsigned alert_n_reenable;            // 0: Parity checking remains disabled after ALERT_n pulse, 1: Parity Checking is re-enabled after ALERT_n pulse
} ddr5_rw01_t;

typedef struct {
    rand shortint unsigned operating_speed;
} ddr5_rw05_t;

typedef struct {
    rand shortint unsigned fine_granularity_operating_speed;
} ddr5_rw06_t;

typedef struct {
    rand shortint unsigned dimm_type;                    //0: LRDIMM enabled:BCS_n , BCOM[2:0] & BRST_n,1: RDIMM Disabled
    rand shortint unsigned dcs_qcs_en;                    //0: DCS1 Disabled 1: DCS1 Enabled
} ddr5_rw09_t;

typedef struct {
    rand shortint unsigned latency_adder_nladd_to_all_dram_cmd;
} ddr5_rw11_t;

typedef struct {
rand ddr5_rw00_t rw00;
rand ddr5_rw01_t rw01;
rand ddr5_rw05_t rw05;
rand ddr5_rw06_t rw06;
rand ddr5_rw09_t rw09;
rand ddr5_rw11_t rw11;
} ddr5_control_words_t;

//////////ddr5 data buffer///////////
typedef struct {
    rand shortint unsigned db_ca_rate;                // 0: 2N(default), 1: 1N
} ddr5_rw80_t;

typedef struct {
    rand shortint unsigned db_pba_mode;                // Per Buffer Addressability 0: Disable, 1: Enable
} ddr5_rw81_t;

typedef struct {
    rand shortint unsigned db_tp_mode;                // Transparent mode 0: Disable, 1: Enable
} ddr5_rw82_t;

typedef struct {
    rand shortint unsigned lrdimm_operating_speed;
} ddr5_rw84_t;

typedef struct {
    rand shortint unsigned fine_granularity_operating_speed;
} ddr5_rw85_t;

typedef struct {
rand ddr5_rw80_t rw80;
rand ddr5_rw81_t rw81;
rand ddr5_rw82_t rw82;
rand ddr5_rw84_t rw84;
rand ddr5_rw85_t rw85;
} ddr5_db_control_words_t;

typedef struct {
	int unsigned ddr5_trefi1_ps_scale_en;
	int unsigned ddr5_trefi1_ps_scale_val;
	int unsigned ddr5_trfc1_ps_scale_val;
	int unsigned ddr5_trfc2_ps_scale_val;
	int unsigned ddr5_trfcsb_ps_scale_val;
	int unsigned ddr5_trfcsb_dlr_ps_scale_val;
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
    PUB_MSG_END_OF_INITIALIZATION                              = 'h00,
    PUB_MSG_END_OF_FINE_WRITE_LEVELING                         = 'h01,
    PUB_MSG_END_OF_READ_ENABLE_TRAINING                        = 'h02,
    PUB_MSG_END_OF_READ_DELAY_CENTER_OPTIMIZATION              = 'h03,
    PUB_MSG_END_OF_WRITE_DELAY_CENTER_OPTIMIZATION             = 'h04,
    PUB_MSG_TRAINING_COMPLETE_PASSED                           = 'h07,
    PUB_MSG_START_STREAMING_MESSAGE_MODE                       = 'h08,
    PUB_MSG_END_OF_MAX_READ_LATENCY_TRAINING                   = 'h09,
    PUB_MSG_END_OF_CA_TRAINING                                 = 'h0d,
/* DDR specific messages */
`ifdef DDRCTL_DDR
    PUB_MSG_END_OF_2D_READ_DELAY_VOLTAGE_CENTER_OPTIMIZATION   = 'h05,
    PUB_MSG_END_OF_2D_WRITE_DELAY_VOLTAGE_CENTER_OPTIMIZATION  = 'h06,
    PUB_MSG_END_OF_READ_DQ_DESKEW_TRAINING                     = 'h0a,
    PUB_MSG_END_OF_LCDL_OFFSET_CALIBRATION                     = 'h0b,
    PUB_MSG_END_OF_RCD_QCS_QCA_TRAINING                        = 'h1d,
    PUB_MSG_END_OF_LRDIMM_SPECIFIC_TRAINING                    = 'h0c,
    PUB_MSG_END_OF_LRDIMM_MREP_TRAINING                        = 'h20,
    PUB_MSG_END_OF_LRDIMM_DWL_TRAINING                         = 'h21,
    PUB_MSG_END_OF_LRDIMM_MRD_TRAINING                         = 'h22,
    PUB_MSG_END_OF_LRDIMM_MWD_TRAINING                         = 'h23,
    PUB_MSG_END_OF_MEMORY_RESET                                = 'h60,
    PUB_MSG_END_OF_MPR_READ_DELAY_CENTER_OPTIMIZATION          = 'hfd,
`endif // DDRCTL_DDR
/* LPDDR specific messages */
`ifdef DDRCTL_LPDDR
    PUB_MSG_END_OF_RXDIGSTROBE_TRAINING                        = 'h05,
    PUB_MSG_END_OF_DRAM_DCA_TRAINING                           = 'h06,
    PUB_MSG_END_OF_PHY_RX_DCA_TRAINING                         = 'h0a,
    PUB_MSG_END_OF_PHY_TX_DCA_TRAINING                         = 'h0b,
    PUB_MSG_END_OF_READ_TRAINING_CENTER_OPTIMIZATION           = 'hfd,
`endif // DDRCTL_LPDDR
    PUB_MSG_SMBUS_REQUEST                                      = 'h50,
    PUB_MSG_SMBUS_SYNC                                         = 'h51,
    PUB_MSG_END_OF_WRITE_LEVELING_COARSE_DELAY                 = 'hfe,
    PUB_MSG_TRAINING_COMPLETE_FAILED                           = 'hff
} pub_msg_id_t;


`endif /* __DWC_DDRCTL_CINIT_TYPES_H__ */
