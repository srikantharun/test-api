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


#ifndef __DWC_DDRCTL_CINIT_STRUCT_SPD_H__
#define __DWC_DDRCTL_CINIT_STRUCT_SPD_H__

#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_cfg.h"

typedef struct tag_SPD_DDR4 {
    uint8_t bytes_total_used;                            /* Byte  0 (0x000): Number of Bytes Used / Number of Bytes in SPD Device */
    uint8_t revision;                                /* Byte  1 (0x001): SPD Revision */
    uint8_t kb_dram_device_type;                            /* Byte  2 (0x002): Key Byte / DRAM Device Type */
    uint8_t kb_module_type;                                /* Byte  3 (0x003): Key Byte / Module Type */
    uint8_t sdram_density_banks;                            /* Byte  4 (0x004): SDRAM Density and Banks */
    uint8_t sdram_addressing;                            /* Byte  5 (0x005): SDRAM Addressing */
    uint8_t primary_sdram_package_type;                        /* Byte  6 (0x006): Primary SDRAM Package Type */
    uint8_t sdram_optional_features;                        /* Byte  7 (0x007): SDRAM Optional Features */
    uint8_t sdram_thermal_and_refresh_options;                    /* Byte  8 (0x008): SDRAM Thermal and Refresh Options */
    uint8_t other_sdram_optional_features;                        /* Byte  9 (0x009): Other SDRAM Optional Features */
    uint8_t secondary_sdram_package_type;                        /* Byte 10 (0x00A): Secondary SDRAM Package Type */
    uint8_t module_nom_voltage_vdd;                            /* Byte 11 (0x00B): Module Nominal Voltage, VDD */
    uint8_t module_organization;                            /* Byte 12 (0x00C): Module Organization */
    uint8_t module_memory_bus_width;                        /* Byte 13 (0x00D): Module Memory Bus Width */
    uint8_t module_thermal_sensor;                            /* Byte 14 (0x00E): Module Thermal Sensor */
    uint8_t extended_module_type;                            /* Byte 15 (0x00F): Extended Module Type */
    uint8_t _RESERVED0;                                /* Byte 16 (0x010): Reserved */
    uint8_t timebases;                                /* Byte 17 (0x011): Timebases */
    uint8_t tCKAVG_min_mtb;                                /* Byte 18 (0x012): SDRAM Minimum Cycle Time (tCKAVGmin) */
    uint8_t tCKAVG_max_mtb;                                /* Byte 19 (0x013): SDRAM Maximum Cycle Time (tCKAVGmax) */
    union {
        struct {
            uint8_t CL_supported_byte0;                    /* Byte 20 (0x014): CAS Latencies Supported, First Byte */
            uint8_t CL_supported_byte1;                    /* Byte 21 (0x015): CAS Latencies Supported, Second Byte */
            uint8_t CL_supported_byte2;                    /* Byte 22 (0x016): CAS Latencies Supported, Third Byte */
            uint8_t CL_supported_byte3;                    /* Byte 23 (0x017): CAS Latencies Supported, Fourth Byte */
        };
        uint32_t CL_supported;
    };
    uint8_t tAA_min_mtb;                                /* Byte 24 (0x018): Minimum CAS Latency Time (tAAmin) */
    uint8_t tRCD_min_mtb;                                /* Byte 25 (0x019): Minimum RAS to CAS Delay Time (tRCDmin) */
    uint8_t tRP_min_mtb;                                /* Byte 26 (0x01A): Minimum Row Precharge Delay Time (tRPmin) */
    uint8_t tRAS_min_tRC_min_mtb_msb;                        /* Byte 27 (0x01B): Upper Nibbles for tRASmin and tRCmin */
    uint8_t tRAS_min_mtb_lsb;                            /* Byte 28 (0x01C): Minimum Active to Precharge Delay Time (tRASmin), Least Significant Byte */
    uint8_t tRC_min_mtb_lsb;                            /* Byte 29 (0x01D): Minimum Active to Active/Refresh Delay Time (tRCmin), Least Significant Byte */
    union {
        struct {
            uint8_t tRFC1_min_mtb_lsb;                    /* Byte 30 (0x01E): Minimum Refresh Recovery Delay Time (tRFC1min), Least Significant Byte */
            uint8_t tRFC1_min_mtb_msb;                    /* Byte 31 (0x01F): Minimum Refresh Recovery Delay Time (tRFC1min), Most Significant Byte */
        };
        uint16_t tRFC1_min_mtb;
    };
    union {
        struct {
            uint8_t tRFC2_min_mtb_lsb;                    /* Byte 32 (0x020): Minimum Refresh Recovery Delay Time (tRFC2min), Least Significant Byte */
            uint8_t tRFC2_min_mtb_msb;                    /* Byte 33 (0x021): Minimum Refresh Recovery Delay Time (tRFC2min), Most Significant Byte */
        };
        uint16_t tRFC2_min_mtb;
    };
    union {
        struct {
            uint8_t tRFC4_min_mtb_lsb;                    /* Byte 34 (0x022): Minimum Refresh Recovery Delay Time (tRFC4min), Least Significant Byte */
            uint8_t tRFC4_min_mtb_msb;                    /* Byte 35 (0x023): Minimum Refresh Recovery Delay Time (tRFC4min), Most Significant Byte */
        };
        uint16_t tRFC4_min_mtb;
    };
    uint8_t tFAW_min_mtb_msb;                            /* Byte 36 (0x024): Upper Nibble for tFAW */
    uint8_t tFAW_min_mtb_lsb;                            /* Byte 37 (0x025): Minimum Four Activate Window Delay Time (tFAWmin), Least Significant Byte */
    uint8_t tRRD_S_min_mtb;                                /* Byte 38 (0x026): Minimum Activate to Activate Delay Time (tRRD_Smin), different bank group */
    uint8_t tRRD_L_min_mtb;                                /* Byte 39 (0x027): Minimum Activate to Activate Delay Time (tRRD_Lmin), same bank group */
    uint8_t tCCD_L_min_mtb;                                /* Byte 40 (0x028): Minimum CAS to CAS Delay Time (tCCD_Lmin), same bank group */
    uint8_t tWR_min_mtb_msb;                            /* Byte 41 (0x029): Upper Nibble for tWRmin */
    uint8_t tWR_min_mtb_lsb;                            /* Byte 42 (0x02A): Minimum Write Recovery Time (tWRmin) */
    uint8_t tWTR_L_min_tWTR_S_min_mtb_msb;                        /* Byte 43 (0x029): Upper Nibbles for tWTRmin */
    uint8_t tWTR_S_min_mtb_lsb;                            /* Byte 44 (0x02C): Minimum Write to Read Time (tWTR_Smin), different bank group */
    uint8_t tWTR_L_min_mtb_lsb;                            /* Byte 45 (0x02D): Minimum Write to Read Time (tWTR_Lmin), same bank group */
    uint8_t _RESERVED1[14];                                /* Byte 46~59 (0x02E~0x03B): Reserved, Base Configuration Section */
    uint8_t connector_to_SDRAM_bit_mapping[18];                    /* Bytes 60~77 (0x03C~0x04D): Connector to SDRAM Bit Mapping */
    uint8_t _RESERVED2[39];                                /* Bytes 78~116 (0x04E~0x074): Reserved, Base Configuration Section */
    int8_t tCCD_L_min_ftb;                                /* Byte 117 (0x075): Fine Offset for Minimum CAS to CAS Delay Time (tCCD_Lmin), same bank group */
    int8_t tRRD_L_min_ftb;                                /* Byte 118 (0x076): Fine Offset for Minimum Activate to Activate Delay Time (tRRD_Lmin), same bank group */
    int8_t tRRD_S_min_ftb;                                /* Byte 119 (0x077): Fine Offset for Minimum Activate to Activate Delay Time (tRRD_Smin), different bank group */
    int8_t tRC_min_ftb;                                /* Byte 120 (0x078): Fine Offset for Minimum Active to Active/Refresh Delay Time (tRCmin) */
    int8_t tRP_min_ftb;                                /* Byte 121 (0x079): Fine Offset for Minimum Row Precharge Delay Time (tRPmin) */
    int8_t tRCD_min_ftb;                                /* Byte 122 (0x07A): Fine Offset for Minimum RAS to CAS Delay Time (tRCDmin) */
    int8_t tAA_min_ftb;                                /* Byte 123 (0x07B): Fine Offset for Minimum CAS Latency Time (tAAmin) */
    int8_t tCKAVG_max_ftb;                                /* Byte 123 (0x07B): Fine Offset for Minimum CAS Latency Time (tAAmin) */
    int8_t tCKAVG_min_ftb;                                /* Byte 125 (0x07D): Fine Offset for SDRAM Minimum Cycle Time (tCKAVGmin) */
    union {
        struct {
            uint8_t crc_lsb;                        /* Byte 126 (0x07E): Cyclical Redundancy Code (CRC) for Base Configuration Section, Least Significant Byte */
            uint8_t crc_msb;                        /* Byte 127 (0x07F): Cyclical Redundancy Code (CRC) for Base Configuration Section, Most Significant Byte */
        };
        uint16_t crc;
    };
    union {
        struct {
            uint8_t raw_card_extension_module_nom_height;            /* Byte 128 (0x080) (Unbuffered): Raw Card Extension, Module Nominal Height */
            uint8_t module_max_thickness;                    /* Byte 129 (0x081) (Unbuffered): Module Maximum Thickness */
            uint8_t ref_raw_card_used;                    /* Byte 130 (0x082) (Unbuffered): Reference Raw Card Used */
            uint8_t address_mapping_from_edge_connector_to_dram;        /* Byte 131 (0x083) (Unbuffered): Address Mapping from Edge Connector to DRAM */
            uint8_t _RESERVED0[60];                        /* Bytes 132~191 (0x084~0x0BF) (Unbuffered): Reserved */
            union {
                struct {
                    uint8_t crc_lsb;                /* Byte 254 (0x0FE) (Unbuffered): Cyclical Redundancy Code (CRC) for SPD Block 1, Least Significant Byte */
                    uint8_t crc_msb;                /* Byte 255 (0x0FF) (Unbuffered): Cyclical Redundancy Code (CRC) for SPD Block 1, Most Significant Byte */
                };
                uint16_t crc;
            };
        } UDIMM;
        struct {
            uint8_t raw_card_extension_module_nom_height;            /* Byte 128 (0x080) (Registered): Raw Card Extension, Module Nominal Height */
            uint8_t module_max_thickness;                    /* Byte 129 (0x081) (Registered): Module Maximum Thickness */
            uint8_t ref_raw_card_used;                    /* Byte 130 (0x082) (Registered): Reference Raw Card */
            uint8_t dimm_attributes;                    /* Byte 131 (0x083) (Registered): DIMM Attributes */
            uint8_t rdimm_thermal_heat_spreader_solution;            /* Byte 132 (0x084) (Registered): RDIMM Thermal Heat Spreader Solution */
            uint8_t register_mfr_id_code_lsb;                /* Byte 133 (0x085) (Registered): Register Manufacturer ID Code, First Byte */
            uint8_t register_mfr_id_code_msb;                /* Byte 134 (0x086) (Registered): Register Manufacturer ID Code, Second Byte */
            uint8_t register_rev_number;                    /* Byte 135 (0x087) (Registered): Register Revision Number */
            uint8_t address_mapping_from_register_to_dram;            /* Byte 136 (0x088) (Registered): Address Mapping from Register to DRAM */
            uint8_t register_output_ds_for_control_and_ca;            /* Byte 137 (0x089) (Registered): Register Output Drive Strength for Control and Command/ Address */
            uint8_t register_output_ds_for_clk;                /* Byte 138 (0x08A) (Registered): Register Output Drive Strength for Clock */
            uint8_t _RESERVED0[115];                    /* Bytes 139~191 (0x08B~0x0BF): Reserved */
            union {
                struct {
                    uint8_t crc_lsb;                /* Byte 254 (0x0FE) (Registered): Cyclical Redundancy Code (CRC) for SPD Block 1, Least Significant Byte */
                    uint8_t crc_msb;                /* Byte 255 (0x0FF) (Registered): Cyclical Redundancy Code (CRC) for SPD Block 1, Most Significant Byte */
                };
                uint16_t crc;
            };
        } RDIMM;
        struct {
            uint8_t raw_card_extension_module_nom_height;            /* Byte 128 (0x080) (Load Reduced): Raw Card Extension, Module Nominal Height */
            uint8_t module_max_thickness;                    /* Byte 129 (0x081) (Load Reduced): Module Maximum Thickness */
            uint8_t ref_raw_card_used;                    /* Byte 130 (0x082) (Load Reduced): Reference Raw Card Used */
            uint8_t dimm_attributes;                    /* Byte 131 (0x083) (Load Reduced): DIMM Attributes */
            uint8_t lrdimm_thermal_heat_spreader_solution;            /* Byte 132 (0x084) (Load Reduced): LRDIMM Thermal Heat Spreader Solution */
            uint8_t register_and_db_mfr_id_code_lsb;            /* Byte 133 (0x085) (Load Reduced): Register and Data Buffer Manufacturer ID Code, First Byte */
            uint8_t register_and_db_mfr_id_code_msb;            /* Byte 134 (0x086) (Load Reduced): Register and Data Buffer Manufacturer ID Code, Most Significant Byte */
            uint8_t register_rev_number;                    /* Byte 135 (0x087) (Load Reduced): Register Revision Number */
            uint8_t address_mapping_from_register_to_dram;            /* Byte 136 (0x088) (Load Reduced): Address Mapping from Register to DRAM */
            uint8_t register_output_ds_for_control_and_ca;            /* Byte 137 (0x089) (Load Reduced): Register Output Drive Strength for Control and Command/Address */
            uint8_t register_output_ds_for_clk_and_db;            /* Byte 138 (0x08A) (Load Reduced): Register Output Drive Strength for Clock and Data Buffer Control */
            uint8_t db_rev_number;                        /* Byte 139 (0x08B) (Load Reduced): Data Buffer Revision Number */
            uint8_t dram_VrefDQ_for_package_rank0;                /* Byte 140 (0x08C) (Load Reduced): DRAM VrefDQ for Package Rank 0 */
            uint8_t dram_VrefDQ_for_package_rank1;                /* Byte 141 (0x08D) (Load Reduced): DRAM VrefDQ for Package Rank 1 */
            uint8_t dram_VrefDQ_for_package_rank2;                /* Byte 142 (0x08E) (Load Reduced): DRAM VrefDQ for Package Rank 2 */
            uint8_t dram_VrefDQ_for_package_rank3;                /* Byte 143 (0x08F) (Load Reduced): DRAM VrefDQ for Package Rank 3 */
            uint8_t db_VrefDQ_for_dram_if;                    /* Byte 144 (0x090) (Load Reduced): Data Buffer VrefDQ for DRAM Interface */
            uint8_t db_ds_and_rtt_for_mdq_lte1866;                /* Byte 145 (0x091) (Load Reduced): Data Buffer MDQ Drive Strength and RTT for data rate < 1866 */
            uint8_t db_ds_and_rtt_for_mdq_gt1866_lte2400;            /* Byte 146 (0x092) (Load Reduced): Data Buffer MDQ Drive Strength and RTT for 1866 < data rate < 2400 */
            uint8_t db_ds_and_rtt_for_mdq_gt2400_lte3200;            /* Byte 147 (0x093) (Load Reduced): Data Buffer MDQ Drive Strength and RTT for 2400 < data rate < 3200 */
            uint8_t dram_ds;                        /* Byte 148 (0x094) (Load Reduced): DRAM Drive Strength (for data rates < 1866, 1866 < data rate < 2400, and 2400 < data rate < 3200) */
            uint8_t dram_rtt_wr_rtt_nom_lte1866;                /* Byte 149 (0x095) (Load Reduced): DRAM ODT (RTT_WR and RTT_NOM) for data rate < 1866 */
            uint8_t dram_rtt_wr_rtt_nom_gt1866_lte2400;            /* Byte 150 (0x096) (Load Reduced): DRAM ODT (RTT_WR and RTT_NOM) for 1866 < data rate < 2400 */
            uint8_t dram_rtt_wr_rtt_nom_gt2400_lte3200;            /* Byte 151 (0x097) (Load Reduced): DRAM ODT (RTT_WR and RTT_NOM) for 2400 < data rate < 3200 */
            uint8_t dram_rtt_park_lte1866;                    /* Byte 152 (0x098) (Load Reduced): DRAM ODT (RTT_PARK) for data rate < 1866 */
            uint8_t dram_rtt_park_gt1866_lte2400;                /* Byte 153 (0x099) (Load Reduced): DRAM ODT (RTT_PARK) for 1866 < data rate < 2400 */
            uint8_t dram_rtt_park_gt2400_lte3200;                /* Byte 154 (0x09A) (Load Reduced): DRAM ODT (RTT_PARK) for 2400 < data rate < 3200 */
            uint8_t db_VrefDQ_for_dram_if_range;                /* Byte 155 (0x09B) (Load Reduced): Data Buffer VrefDQ for DRAM Interface Range */
            uint8_t db_dq_dfe;                        /* Byte 156 (0x09C) (Load Reduced): Data Buffer DQ Decision Feedback Equalization (DFE) */
            uint8_t _RESERVED0[97];                        /* Bytes 157~191 (0x09D~0x0BF) (Load Reduced): Reserved */
            union {
                struct {
                    uint8_t crc_lsb;                /* Bytes 254 (0x0FE) (Load Reduced): Cyclical Redundancy Code (CRC) for SPD Block 1, Least Significant Byte */
                    uint8_t crc_msb;                /* Bytes 255 (0x0FF) (Load Reduced): Cyclical Redundancy Code (CRC) for SPD Block 1, Most Significant Byte */
                };
                uint16_t crc;
            };
        } LRDIMM;
    };                                        /* Module-Specific Section: Bytes 128~191 (0x080~0x0BF) */
    uint8_t data[256];                                /* Module-Specific Section: Bytes 256~512 (0x100~0x1FF) */
} __attribute__((packed)) SPD_DDR4_t;

typedef struct tag_SPD_DDR5 {
    uint8_t bytes_total_used;               /* Byte  0 (0x000): Number of Bytes in SPD Device */
    uint8_t revision;                       /* Byte  1 (0x001): SPD Revision for Base Configuration Parameters */
    uint8_t kb_dram_device_type;            /* Byte  2 (0x002): Key Byte / Host Bus Command Protocol Type */
    uint8_t kb_module_type;                 /* Byte  3 (0x003): Key Byte / Module Type */
    uint8_t sdram_density_banks;            /* Byte  4 (0x004): First SDRAM Density and Package */
    uint8_t sdram_addressing;               /* Byte  5 (0x005): First SDRAM Addressing */
    uint8_t sdram_width;                    /* Byte  6 (0x006): First SDRAM I/O Width */
    uint8_t sdram_bkg_bpbg;                 /* Byte  7 (0x007): First SDRAM Bank Groups & Banks Per Bank Group */
    uint8_t second_sdram_package_type;      /* Byte  8 (0x008): Second SDRAM Density and Package */
    uint8_t second_sdram_addressing;        /* Byte  9 (0x009): Second SDRAM Addressing */
    uint8_t second_sdram_width;             /* Byte 10 (0x00A): Secondary SDRAM I/O Width */
    uint8_t second_sdram_bkg_bpbg;          /* Byte 11 (0x00B): Second SDRAM Bank Groups & Banks Per Bank Group */
    uint8_t sdram_bl32_ppr;                 /* Byte 12 (0x00C): SDRAM BL32 & Post Package Repair */
    uint8_t sdram_duty_cycle;               /* Byte 13 (0x00D): SDRAM Duty Cycle Adjuster & Partial Array Self Refresh */
    uint8_t fault_handling;                 /* Byte 14 (0x00E): SDRAM Fault Handling */
    uint8_t reserved_0;                     /* Byte 15 (0x00F): Reserved */
    uint8_t vdd;                            /* Byte 16 (0x010): SDRAM Nominal Voltage, VDD */
    uint8_t vddq;                           /* Byte 17 (0x011): SDRAM Nominal Voltage, VDDQ */
    uint8_t vpp;                            /* Byte 18 (0x012): SDRAM Nominal Voltage, VPP */
    uint8_t timing;                         /* Byte 19 (0x013): SDRAM Timing */
    union {
        struct {
            uint8_t    tCKAVGmin_lsb;       /* Byte 20 (0x014): SDRAM Minimum Cycle Time (tCKAVGmin) - Least Significant Byte */
            uint8_t    tCKAVGmin_msb;       /* Byte 21 (0x015): SDRAM Minimum Cycle Time (tCKAVGmin) - Most Significant Byte */
        };
        uint16_t tCKAVGmin;
    };
    union {
        struct {
            uint8_t    tCKAVGmax_lsb;       /* Byte 22 (0x016): SDRAM Maximum Cycle Time (tCKAVGmax) - Least Significant Byte */
            uint8_t    tCKAVGmax_msb;       /* Byte 23 (0x017): SDRAM Maximum Cycle Time (tCKAVGmax) - Most Significant Byte */
        };
        uint16_t tCKAVGmax;
    };
    struct {
        uint8_t    CASlatency_byte0;        /* Byte 24 (0x018): SDRAM CAS Latencies Supported - First Byte */
        uint8_t    CASlatency_byte1;        /* Byte 25 (0x019): SDRAM CAS Latencies Supported - Second Byte */
        uint8_t    CASlatency_byte2;        /* Byte 26 (0x01A): SDRAM CAS Latencies Supported - Third Byte */
        uint8_t    CASlatency_byte3;        /* Byte 27 (0x01B): SDRAM CAS Latencies Supported - Fourth Byte */
        uint8_t    CASlatency_byte4;        /* Byte 28 (0x01C): SDRAM CAS Latencies Supported - Fifth Byte */
    };
    uint8_t reserved_1;                     /* Byte 29 (0x01D): Reserved */
    union {
        struct {
            uint8_t tAAmin_lsb;             /* Byte 30 (0x01E): SDRAM Minimum CAS Latency Time (tAAmin) - Least Significant Byte */
            uint8_t tAAmin_msb;             /* Byte 31 (0x01F): SDRAM Minimum CAS Latency Time (tAAmin) - Most Significant Byte */
        };
        uint16_t tAAmin;
    };
    union {
        struct {
            uint8_t tRCDmin_lsb;            /* Byte 32 (0x020): SDRAM Minimum RAS to CAS Delay Time (tRCDmin) - Least Significant Byte */
            uint8_t tRCDmin_msb;            /* Byte 33 (0x021): SDRAM Minimum RAS to CAS Delay Time (tRCDmin) - Most Significant Byte */
        };
        uint16_t tRCDmin;
    };
    union {
        struct {
            uint8_t tRPmin_lsb;             /* Byte 34 (0x022): SDRAM Minimum Row Precharge Delay Time (tRPmin) - Least Significant Byte */
            uint8_t tRPmin_msb;             /* Byte 35 (0x023): SDRAM Minimum Row Precharge Delay Time (tRPmin) - Most Significant Byte */
        };
        uint16_t tRPmin;
    };
    union {
        struct {
            uint8_t tRASmin_lsb;            /* Byte 36 (0x024): SDRAM Minimum Active to Precharge Delay Time (tRASmin) - Least Significant Byte */
            uint8_t tRASmin_msb;            /* Byte 37 (0x025): SDRAM Minimum Active to Precharge Delay Time (tRASmin) - Most Significant Byte */
        };
        uint16_t tRASmin;
    };
    union {
        struct {
            uint8_t tRCmin_lsb;             /* Byte 38 (0x026): SDRAM Minimum Active to Active/Refresh Delay Time (tRCmin) - Least Significant Byte */
            uint8_t tRCmin_msb;             /* Byte 39 (0x027): SDRAM Minimum Active to Active/Refresh Delay Time (tRCmin) - Most Significant Byte */
        };
        uint16_t tRCmin;
    };
    union {
        struct {
            uint8_t tWRmin_lsb;             /* Byte 40 (0x028): SDRAM Minimum Write Recovery Time (tWRmin) - Least Significant Byte */
            uint8_t tWRmin_msb;             /* Byte 41 (0x029): SDRAM Minimum Write Recovery Time (tWRmin) - Most Significant Byte */
        };
        uint16_t tWRmin;
    };
    union {
        struct {
            uint8_t    tRFC1_slr_min_lsb;   /* Byte 42 (0x02A): SDRAM Minimum Refresh Recovery Delay Time (tRFC1min, tRFC1_slr min) - Least Significant Byte */
            uint8_t tRFC1_slr_min_msb;      /* Byte 43 (0x02B): SDRAM Minimum Refresh Recovery Delay Time (tRFC1min, tRFC1_slr min) - Most Significant Byte */
        };
        uint16_t tRFC1_slr_min;
    };
    union {
        struct {
            uint8_t    tRFC2_slr_min_lsb;   /* Byte 44 (0x02C): SDRAM Minimum Refresh Recovery Delay Time (tRFC2min, tRFC2_slr min) - Least Significant Byte */
            uint8_t tRFC2_slr_min_msb;      /* Byte 45 (0x02D): SDRAM Minimum Refresh Recovery Delay Time (tRFC2min, tRFC2_slr min) - Most Significant Byte */
        };
        uint16_t tRFC2_slr_min;
    };
    union {
        struct {
            uint8_t    tRFCsb_slr_min_lsb;  /* Byte 46 (0x02E): SDRAM Minimum Refresh Recovery Delay Time (tRFCsbmin, tRFCsb_slr min) - Least Significant Byte */
            uint8_t tRFCsb_slr_min_msb;     /* Byte 47 (0x02F): SDRAM Minimum Refresh Recovery Delay Time (tRFCsbmin, tRFCsb_slr min) - Most Significant Byte */
        };
        uint16_t tRFCsb_slr_min;
    };
    union {
        struct {
            uint8_t    tRFC1_dlr_min_lsb;   /* Byte 48 (0x030): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC1_dlr min) - Least Significant Byte */
            uint8_t tRFC1_dlr_min_msb;      /* Byte 49 (0x031): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC1_dlr min) - Most Significant Byte */
        };
        uint16_t tRFC1_dlr_min;
    };
    union {
        struct {
            uint8_t    tRFC2_dlr_lsb;       /* Byte 50 (0x032): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC2_dlr min) - Least Significant Byte */
            uint8_t tRFC2_dlr_msb;          /* Byte 51 (0x033): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC2_dlr min) - Most Significant Byte */
        };
        uint16_t tRFC2_dlr_min;
    };
    union {
        struct {
            uint8_t tRFCsb_dlr_min_lsb;     /* Byte 52 (0x034): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFCsb_dlr min) - Least Significant Byte*/
            uint8_t tRFCsb_dlr_min_msb;     /* Byte 53 (0x035): SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFCsb_dlr min) - Most Significant Byte */
        };
        uint16_t tRFCsb_dlr_min;
    };
    union {
        struct {
            uint8_t sdram_refresh_mgnt_lsb; /* Byte 54 (0x036): SDRAM Refresh Management, First Byte, First SDRAM */
            uint8_t sdram_refresh_mgnt_msb; /* Byte 55 (0x037): SDRAM Refresh Management, Second Byte, First SDRAM */
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
            uint8_t sdram_adapt_A_refresh_lsb;              /* Byte 58 (0x03A): SDRAM Adaptive Refresh Management - ARFM level A, Least Significant Byte*/
            uint8_t sdram_adapt_A_refresh_msb;              /* Byte 59 (0x03B): SDRAM Adaptive Refresh Management - ARFM level A, Most Significant Byte */
        };
        uint16_t sdram_adapt_A_refresh;
    };
    union {
        struct {
            uint8_t second_sdram_adapt_A_refresh_lsb;       /* Byte 60 (0x03C): second SDRAM Adaptive Refresh Management - ARFM level A, Least Significant Byte*/
            uint8_t second_sdram_adapt_A_refresh_msb;       /* Byte 61 (0x03D): second SDRAM Adaptive Refresh Management - ARFM level A, Most Significant Byte */
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
            uint8_t second_sdram_adapt_B_refresh_lsb;       /* Byte 64 (0x040): second SDRAM Adaptive Refresh Management - ARFM level B, Least Significant Byte*/
            uint8_t second_sdram_adapt_B_refresh_msb;       /* Byte 65 (0x041): second SDRAM Adaptive Refresh Management - ARFM level B, Most Significant Byte */
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
            uint8_t second_sdram_adapt_C_refresh_lsb;       /* Byte 68 (0x044): second SDRAM Adaptive Refresh Management - ARFM level C, Least Significant Byte*/
            uint8_t second_sdram_adapt_C_refresh_msb;       /* Byte 69 (0x045): second SDRAM Adaptive Refresh Management - ARFM level C, Most Significant Byte */
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
} __attribute__((packed)) SPD_DDR5_t;


typedef    union tag_SPD_DDR {
    SPD_DDR4_t SPD_DDR4;
    SPD_DDR5_t SPD_DDR5;
} SPD_DDR_t;

typedef struct tag_ddr4_t {
    uint32_t tRCDmin_ps;            // 122 Fine Offset for Minimum RAS to CAS Delay Time tRCDmin -> pSpd->tRCDmin_p
    uint32_t tRPmin_ps;            //26 121 Fine Offset for Minimum Row Precharge Delay Time (tRPmin) -> spd_D4->tRP_min_mtb
    uint32_t tRCmin_ps;            //27 e 29
    uint32_t tRASmin_ps;            //4 bits 28 -> 8 bits
    uint32_t ddr4_tcl_tck;            //Byte 24 (0x018): Minimum CAS Latency Time (tAAmin)
    uint32_t tRFC1min_ps;
    uint32_t tRFC2min_ps;
    uint32_t tRFC4min_ps;
    uint32_t tCKAVGmax_ps;
    uint32_t tCKAVGmin_ps;
    uint32_t tWRmin_ps;
    uint32_t tAAmin_ps;
    uint32_t tWTR_Smin_ps;
    uint32_t tWTR_Lmin_ps;
    uint32_t tCCD_Lmin_ps;
    uint32_t tRRD_Lmin_ps;
    uint32_t tRRD_Smin_ps;
    uint32_t tFAWmin_ps;
    uint32_t ddr4_tcl_rdbi_tck;
    uint32_t ddr4_tcwl_1st_set_tck;
    uint32_t ddr4_tcwl_2nd_set_tck;
    uint32_t sg_tck_ps;            // -> byte 18 125
    uint64_t cas_latency_supported;
} auxDDR4_t;

typedef struct tag_ddr5_t {
    uint32_t ddr5_twr_ps;
    uint32_t sg_tck_ps;
    uint32_t tRCmin_ps;
    uint32_t ddr5_tcl_tck;
    uint32_t tCKAVGmin;
    uint32_t tCKAVGmax;
    uint32_t tAAmin_ps;
    uint32_t tWRmin_ps;
    uint32_t tRASmin_ps;
    uint32_t tRCDmin_ps;
    uint32_t tRPmin_ps;
    uint32_t tRFC1_slr_min_ns;
    uint32_t tRFC2_slr_min_ns;
    uint32_t tRFCsb_slr_min_ns;
    uint32_t tRFC1_dlr_min_ns;
    uint32_t tRFC2_dlr_min_ns;
    uint32_t tRFCsb_dlr_min_ns;
    uint64_t cas_latency_supported;
    //uint8_t rfm_raa_en;            //RAA counters enable
    //uint8_t rfm_raaimt;         //RAA Initial Management Threshold (RAAIMT). equal to MR58 OP[4:1] of the DDR device.
    //uint8_t rfm_raa_thr;        //Threshold for RAA counter expiration  based on MR58 OP[7:1]. Any value not less than RAAIMT and not larger than RAAMMT
    //uint8_t rfm_raa_ref_decr;    //The value should match the setting on MR59 OP[7:6] of the DDR device. Select the RAA counters' decreasing value per REF command.
} auxDDR5_t;

typedef struct tag_SPD_aux {
    uint32_t sdram_protocol; //!< Basic memory type
    uint32_t module_type; //!< SDRAM Module type
    uint32_t tck_ps[UMCTL2_FREQUENCY_NUM]; //!< Operating clock period ps
    uint32_t num_ranks; //!<Number of ranks
    uint32_t sdram_width_bits[DDRCTL_CINIT_MAX_DEV_NUM]; //!<SDRAM width (bits) [x4, x8, x16, x32]
    uint32_t module_width_bits; //!<Module width (bits)
    uint32_t sdram_capacity_mbits[DDRCTL_CINIT_MAX_DEV_NUM]; //!<SDRAM capacity (megabits)
    uint32_t sdram_capacity_mbits_lp45_mp[DDRCTL_CINIT_MAX_DEV_NUM]; //!<SDRAM capacity (megabits)
    uint8_t ecc_supported; //!<ECC supported (0-not supported, 1-supported)
    uint8_t addr_mirror; //!<Address mirroring support (0-not supported, 1-supported)
    uint8_t shared_ac;
    uint8_t cid_width[DDRCTL_CINIT_MAX_DEV_NUM]; //Number of 3DS CIDs in use 1-2H 2-4H per phyisical rank
    //The following structure members are calculated for you in the subsys_SetSpd() function. No need to set them
    uint32_t dram_raw[DDRCTL_CINIT_MAX_DEV_NUM]; //!<Row address bits
    uint32_t dram_caw[DDRCTL_CINIT_MAX_DEV_NUM]; //!<Column address bits
    uint32_t dram_baw[DDRCTL_CINIT_MAX_DEV_NUM]; //!<Bank address bits
    uint32_t dram_bgw[DDRCTL_CINIT_MAX_DEV_NUM]; //!<Bank group address bits
    uint8_t num_ranks_per_dimm; //!<
    uint8_t num_dimm; //!< Number of DIMM
    uint8_t use_ddr4_tcwl_1st_set; //!< When calculating cwl_x use the lower set of values for tcwl
    uint8_t tAL; //!< Additive Latency can be 0, CL-1, CL-2
    uint8_t tAL_RDBI; //!< Read DBI Additive Latency
    uint8_t use_lpddr4x; //!< The SDRAM is a variant of LPDDR4
    uint32_t ftb_ps;
    uint32_t mtb_ps;
    uint32_t revision;
    union {
        auxDDR4_t DDR4;
        auxDDR5_t DDR5;
    };
} SPD_aux_t;

extern SPD_DDR_t SPD_ddr;
extern SPD_aux_t SPD_aux;

#endif /* __DWC_DDRCTL_CINIT_STRUCT_SPD_H__ */
