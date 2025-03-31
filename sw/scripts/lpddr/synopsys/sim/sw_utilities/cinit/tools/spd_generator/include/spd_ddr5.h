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


#ifndef TOOLS_SPDGENERATOR_INCLUDE_SPD_DDR5_H_
#define TOOLS_SPDGENERATOR_INCLUDE_SPD_DDR5_H_

#include "spd_generator.h"

typedef struct spd_ddr5_s {
    uint8_t bytes_total_used;                               /* Byte  0 (0x000): Number of Bytes in SPD Device */
    uint8_t revision;                                       /* Byte  1 (0x001): SPD Revision for Base Configuration Parameters */
    uint8_t kb_dram_device_type;                            /* Byte  2 (0x002): Key Byte / Host Bus Command Protocol Type */
    uint8_t kb_module_type;                                 /* Byte  3 (0x003): Key Byte / Module Type */
    uint8_t sdram_density_package;                          /* Byte  4 (0x004): First SDRAM Density and Package */
    uint8_t sdram_addressing;                               /* Byte  5 (0x005): First SDRAM Addressing */
    uint8_t sdram_width;                                    /* Byte  6 (0x006): First SDRAM I/O Width */
    uint8_t sdram_bkg_bpbg;                                 /* Byte  7 (0x007): First SDRAM Bank Groups & Banks Per Bank Group */
    uint8_t second_sdram_density_package;                   /* Byte  8 (0x008): Second SDRAM Density and Package */
    uint8_t second_sdram_addressing;                        /* Byte  9 (0x009): Second SDRAM Addressing */
    uint8_t second_sdram_width;                             /* Byte 10 (0x00A): Secondary SDRAM I/O Width */
    uint8_t second_sdram_bkg_bpbg;                          /* Byte 11 (0x00B): Second SDRAM Bank Groups & Banks Per Bank Group */
    uint8_t sdram_bl32_ppr;                                 /* Byte 12 (0x00C): SDRAM BL32 & Post Package Repair */
    uint8_t sdram_duty_cycle;                               /* Byte 13 (0x00D): SDRAM Duty Cycle Adjuster & Partial Array Self Refresh */
    uint8_t fault_handling;                                 /* Byte 14 (0x00E): SDRAM Fault Handling */
    uint8_t reserved_0;                                     /* Byte 15 (0x00F): Reserved */
    uint8_t vdd;                                            /* Byte 16 (0x010): SDRAM Nominal Voltage, VDD */
    uint8_t vddq;                                           /* Byte 17 (0x011): SDRAM Nominal Voltage, VDDQ */
    uint8_t vpp;                                            /* Byte 18 (0x012): SDRAM Nominal Voltage, VPP */
    uint8_t timing;                                         /* Byte 19 (0x013): SDRAM Timing */
    union {
        struct {
            uint8_t    tCKAVGmin_lsb;                       /* Byte 20 (0x014): SDRAM Minimum Cycle Time (tCKAVGmin) - Least Significant Byte */
            uint8_t    tCKAVGmin_msb;                       /* Byte 21 (0x015): SDRAM Minimum Cycle Time (tCKAVGmin) - Most Significant Byte */
        };
        uint16_t tCKAVGmin;
    };
    union {
        struct {
            uint8_t    tCKAVGmax_lsb;                       /* Byte 22 (0x016): SDRAM Maximum Cycle Time (tCKAVGmax) - Least Significant Byte */
            uint8_t    tCKAVGmax_msb;                       /* Byte 23 (0x017): SDRAM Maximum Cycle Time (tCKAVGmax) - Most Significant Byte */
        };
        uint16_t tCKAVGmax;
    };
        struct {
            uint8_t    CASlatency_byte0;                    /* Byte 24 (0x018): SDRAM CAS Latencies Supported - First Byte */
            uint8_t    CASlatency_byte1;                    /* Byte 25 (0x019): SDRAM CAS Latencies Supported - Second Byte */
            uint8_t    CASlatency_byte2;                    /* Byte 26 (0x01A): SDRAM CAS Latencies Supported - Third Byte */
            uint8_t    CASlatency_byte3;                    /* Byte 27 (0x01B): SDRAM CAS Latencies Supported - Fourth Byte */
            uint8_t    CASlatency_byte4;                    /* Byte 28 (0x01C): SDRAM CAS Latencies Supported - Fifth Byte */
        };
    uint8_t reserved_1;                                     /* Byte 29 (0x01D): Reserved */
    union {
        struct {
            uint8_t    tAAmin_lsb;                          /* Byte 30 (0x01E): SDRAM Minimum CAS Latency Time (tAAmin) - Least Significant Byte */
            uint8_t tAAmin_msb;                             /* Byte 31 (0x01F): SDRAM Minimum CAS Latency Time (tAAmin) - Most Significant Byte */
        };
        uint16_t tAAmin;
    };
    union {
        struct {
            uint8_t    tRCDmin_lsb;                         /* Byte 32 (0x020): SDRAM Minimum RAS to CAS Delay Time (tRCDmin) - Least Significant Byte */
            uint8_t tRCDmin_msb;                            /* Byte 33 (0x021): SDRAM Minimum RAS to CAS Delay Time (tRCDmin) - Most Significant Byte */
        };
        uint16_t tRCDmin;
    };
    union {
        struct {
            uint8_t    tRPmin_lsb;                          /* Byte 34 (0x022): SDRAM Minimum Row Precharge Delay Time (tRPmin) - Least Significant Byte */
            uint8_t tRPmin_msb;                             /* Byte 35 (0x023): SDRAM Minimum Row Precharge Delay Time (tRPmin) - Most Significant Byte */
        };
        uint16_t tRPmin;
    };
    union {
        struct {
            uint8_t    tRASmin_lsb;                         /* Byte 36 (0x024): SDRAM Minimum Active to Precharge Delay Time (tRASmin) - Least Significant Byte */
            uint8_t tRASmin_msb;                            /* Byte 37 (0x025): SDRAM Minimum Active to Precharge Delay Time (tRASmin) - Most Significant Byte */
        };
        uint16_t tRASmin;
    };
    union {
        struct {
            uint8_t    tRCmin_lsb;                          /* Byte 38 (0x026): SDRAM Minimum Active to Active/Refresh Delay Time (tRCmin) - Least Significant Byte */
            uint8_t tRCmin_msb;                             /* Byte 39 (0x027): SDRAM Minimum Active to Active/Refresh Delay Time (tRCmin) - Most Significant Byte */
        };
        uint16_t tRCmin;
    };
    union {
        struct {
            uint8_t    tWRmin_lsb;                          /* Byte 40 (0x028): SDRAM Minimum Write Recovery Time (tWRmin) - Least Significant Byte */
            uint8_t tWRmin_msb;                             /* Byte 41 (0x029): SDRAM Minimum Write Recovery Time (tWRmin) - Most Significant Byte */
        };
        uint16_t tWRmin;
    };
    union {
        struct {
            uint8_t    tRFC1_slr_min_lsb;                   /* Byte 42 (0x02A): SDRAM Minimum Refresh Recovery Delay Time (tRFC1min, tRFC1_slr min) - Least Significant Byte */
            uint8_t tRFC1_slr_min_msb;                      /* Byte 43 (0x02B): SDRAM Minimum Refresh Recovery Delay Time (tRFC1min, tRFC1_slr min) - Most Significant Byte */
        };
        uint16_t tRFC1_slr_min;
    };
    union {
        struct {
            uint8_t    tRFC2_slr_min_lsb;                   /* Byte 44 (0x02C): SDRAM Minimum Refresh Recovery Delay Time (tRFC2min, tRFC2_slr min) - Least Significant Byte */
            uint8_t tRFC2_slr_min_msb;                      /* Byte 45 (0x02D): SDRAM Minimum Refresh Recovery Delay Time (tRFC2min, tRFC2_slr min) - Most Significant Byte */
        };
        uint16_t tRFC2_slr_min;
    };
    union {
        struct {
            uint8_t    tRFCsb_slr_min_lsb;                  /* Byte 46 (0x02E): SDRAM Minimum Refresh Recovery Delay Time (tRFCsbmin, tRFCsb_slr min) - Least Significant Byte */
            uint8_t tRFCsb_slr_min_msb;                     /* Byte 47 (0x02F): SDRAM Minimum Refresh Recovery Delay Time (tRFCsbmin, tRFCsb_slr min) - Most Significant Byte */
        };
        uint16_t tRFCsb_slr_min;
    };
    union {
        struct {
            uint8_t    tRFC1_dlr_min_lsb;                   /* Byte 48 (0x030): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC1_dlr min) - Least Significant Byte */
            uint8_t tRFC1_dlr_min_msb;                      /* Byte 49 (0x031): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC1_dlr min) - Most Significant Byte */
        };
        uint16_t tRFC1_dlr_min;
    };
    union {
        struct {
            uint8_t    tRFC2_dlr_lsb;                       /* Byte 50 (0x032): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC2_dlr min) - Least Significant Byte */
            uint8_t tRFC2_dlr_msb;                          /* Byte 51 (0x033): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC2_dlr min) - Most Significant Byte */
        };
        uint16_t tRFC2_dlr_min;
    };
    union {
        struct {
            uint8_t tRFCsb_dlr_min_lsb;                     /* Byte 52 (0x034): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFCsb_dlr min) - Least Significant Byte*/
            uint8_t tRFCsb_dlr_min_msb;                     /* Byte 53 (0x035): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFCsb_dlr min) - Most Significant Byte */
        };
        uint16_t tRFCsb_dlr_min;
    };
    union {
        struct {
            uint8_t sdram_refresh_mgnt_lsb;                 /* Byte 54 (0x036): SDRAM Refresh Management, First Byte, First SDRAM */
            uint8_t sdram_refresh_mgnt_msb;                 /* Byte 55 (0x037): SDRAM Refresh Management, Second Byte, First SDRAM */
        };
        uint16_t sdram_refresh_mgnt;
    };
    union {
        struct {
            uint8_t second_sdram_refresh_mgnt_lsb;          /* Byte 56 (0x038): SDRAM Refresh Management, First Byte, Second SDRAM */
            uint8_t second_sdram_refresh_mgnt_msb;          /* Byte 57 (0x039): SDRAM Refresh Management, Second Byte, Second SDRAM */
        };
        uint16_t second_sdram_refresh_mgt;
    };
    union {
        struct {
            uint8_t sdram_adapt_A_refresh_lsb;              /* Byte 58 (0x03A): SDRAM Adaptive Refresh Management - ARFM level A, Least Significant Byte */
            uint8_t sdram_adapt_A_refresh_msb;              /* Byte 59 (0x03B): SDRAM Adaptive Refresh Management - ARFM level A, Most Significant Byte */
        };
        uint16_t sdram_adapt_A_refresh;
    };
    union {
        struct {
            uint8_t second_sdram_adapt_A_refresh_lsb;       /* Byte 60 (0x03C): Second SDRAM Adaptive Refresh Management - ARFM level A, Least Significant Byte */
            uint8_t second_sdram_adapt_A_refresh_msb;       /* Byte 61 (0x03D): Second SDRAM Adaptive Refresh Management - ARFM level A, Most Significant Byte */
        };
        uint16_t second_sdram_adapt_A_refresh;
    };
    union {
        struct {
            uint8_t sdram_adapt_B_refresh_lsb;              /* Byte 62 (0x03E): SDRAM Adaptive Refresh Management - ARFM level B, Least Significant Byte*/
            uint8_t sdram_adapt_B_refresh_msb;              /* Byte 63 (0x03F): SDRAM Adaptive Refresh Management - ARFM level B, Most Significant Byte */
        };
        uint16_t sdram_adapt_B_refresh;
    };
    union {
        struct {
            uint8_t second_sdram_adapt_B_refresh_lsb;       /* Byte 64 (0x040): Second SDRAM Adaptive Refresh Management - ARFM level B, Least Significant Byte */
            uint8_t second_sdram_adapt_B_refresh_msb;       /* Byte 65 (0x041): Second SDRAM Adaptive Refresh Management - ARFM level B, Most Significant Byte */
        };
        uint16_t second_sdram_adapt_B_refresh;
    };
    union {
        struct {
            uint8_t sdram_adapt_C_refresh_lsb;              /* Byte 66 (0x042): SDRAM Adaptive Refresh Management - ARFM level C, Least Significant Byte*/
            uint8_t sdram_adapt_C_refresh_msb;              /* Byte 67 (0x043): SDRAM Adaptive Refresh Management - ARFM level C, Most Significant Byte */
        };
        uint16_t sdram_adapt_C_refresh;
    };
    union {
        struct {
            uint8_t second_sdram_adapt_C_refresh_lsb;       /* Byte 68 (0x044): Second SDRAM Adaptive Refresh Management - ARFM level C, Least Significant Byte */
            uint8_t second_sdram_adapt_C_refresh_msb;       /* Byte 69 (0x045): Second SDRAM Adaptive Refresh Management - ARFM level C, Most Significant Byte */
        };
        uint16_t second_sdram_adapt_C_refresh;
    };
    uint8_t reserved_2[164];                                /* Bytes 70~233 (0x046~0x0E9): Reserved, Base Configuration Section */
    uint8_t module_organization;                            /* Byte 234 (0x0EA): Module Organization */
    uint8_t memory_channel_bus_width;                       /* Byte 235 (0x0EB): Memory Channel Bus Width */
    uint8_t reserved_3[274];                                /* Bytes 236~509 (0x0EC~0x1FD): Reserved, Base Configuration Section */
    union {
        struct {
            uint8_t crc_lsb;                                /* Bytes 510 (0x1FE): Cyclical Redundancy Code (CRC) for SPD Block 1, Least Significant Byte */
            uint8_t crc_msb;                                /* Bytes 511 (0x1FF): Cyclical Redundancy Code (CRC) for SPD Block 1, Most Significant Byte */
        };
        uint16_t crc;
    };
    uint8_t reserved_4[512];                                /* Bytes 512~1023 (0x200~0x3FF): Reserved, Base Configuration Section */
} __attribute__((packed)) spd_ddr5_t;


int core_ddr5(app_options_t *options);

uint16_t print_and_validate_ddr5_spd(spd_ddr5_t *ddr5);

#endif /* TOOLS_SPDGENERATOR_INCLUDE_SPD_DDR5_H_ */
