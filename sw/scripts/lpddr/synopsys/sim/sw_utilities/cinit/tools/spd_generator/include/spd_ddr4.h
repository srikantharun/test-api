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


#ifndef TOOLS_SPDGENERATOR_INCLUDE_SPD_DDR4_H_
#define TOOLS_SPDGENERATOR_INCLUDE_SPD_DDR4_H_

#include "spd_generator.h"

typedef struct spd_ddr4_s {
    uint8_t bytes_total_used;                               /* Byte  0 (0x000): Number of Bytes Used / Number of Bytes in SPD Device */
    uint8_t revision;                                       /* Byte  1 (0x001): SPD Revision */
    uint8_t kb_dram_device_type;                            /* Byte  2 (0x002): Key Byte / DRAM Device Type */
    uint8_t kb_module_type;                                 /* Byte  3 (0x003): Key Byte / Module Type */
    uint8_t sdram_density_banks;                            /* Byte  4 (0x004): SDRAM Density and Banks */
    uint8_t sdram_addressing;                               /* Byte  5 (0x005): SDRAM Addressing */
    uint8_t primary_sdram_package_type;                     /* Byte  6 (0x006): Primary SDRAM Package Type */
    uint8_t sdram_optional_features;                        /* Byte  7 (0x007): SDRAM Optional Features */
    uint8_t sdram_thermal_and_refresh_options;              /* Byte  8 (0x008): SDRAM Thermal and Refresh Options */
    uint8_t other_sdram_optional_features;                  /* Byte  9 (0x009): Other SDRAM Optional Features */
    uint8_t secondary_sdram_package_type;                   /* Byte 10 (0x00A): Secondary SDRAM Package Type */
    uint8_t module_nom_voltage_vdd;                         /* Byte 11 (0x00B): Module Nominal Voltage, VDD */
    uint8_t module_organization;                            /* Byte 12 (0x00C): Module Organization */
    uint8_t module_memory_bus_width;                        /* Byte 13 (0x00D): Module Memory Bus Width */
    uint8_t module_thermal_sensor;                          /* Byte 14 (0x00E): Module Thermal Sensor */
    uint8_t extended_module_type;                           /* Byte 15 (0x00F): Extended Module Type */
    uint8_t _RESERVED0;                                     /* Byte 16 (0x010): Reserved */
    uint8_t timebases;                                      /* Byte 17 (0x011): Timebases */
    uint8_t tCKAVG_min_mtb;                                 /* Byte 18 (0x012): SDRAM Minimum Cycle Time (tCKAVGmin) */
    uint8_t tCKAVG_max_mtb;                                 /* Byte 19 (0x013): SDRAM Maximum Cycle Time (tCKAVGmax) */
    union {
        struct {
            uint8_t CL_supported_byte0;                     /* Byte 20 (0x014): CAS Latencies Supported, First Byte */
            uint8_t CL_supported_byte1;                     /* Byte 21 (0x015): CAS Latencies Supported, Second Byte */
            uint8_t CL_supported_byte2;                     /* Byte 22 (0x016): CAS Latencies Supported, Third Byte */
            uint8_t CL_supported_byte3;                     /* Byte 23 (0x017): CAS Latencies Supported, Fourth Byte */
        };
        uint32_t CL_supported;
    };
    uint8_t tAA_min_mtb;                                    /* Byte 24 (0x018): Minimum CAS Latency Time (tAAmin) */
    uint8_t tRCD_min_mtb;                                   /* Byte 25 (0x019): Minimum RAS to CAS Delay Time (tRCDmin) */
    uint8_t tRP_min_mtb;                                    /* Byte 26 (0x01A): Minimum Row Precharge Delay Time (tRPmin) */
    uint8_t tRAS_min_tRC_min_mtb_msb;                       /* Byte 27 (0x01B): Upper Nibbles for tRASmin and tRCmin */
    uint8_t tRAS_min_mtb_lsb;                               /* Byte 28 (0x01C): Minimum Active to Precharge Delay Time (tRASmin), Least Significant Byte */
    uint8_t tRC_min_mtb_lsb;                                /* Byte 29 (0x01D): Minimum Active to Active/Refresh Delay Time (tRCmin), Least Significant Byte */
    union {
        struct {
            uint8_t tRFC1_min_mtb_lsb;                      /* Byte 30 (0x01E): Minimum Refresh Recovery Delay Time (tRFC1min), Least Significant Byte */
            uint8_t tRFC1_min_mtb_msb;                      /* Byte 31 (0x01F): Minimum Refresh Recovery Delay Time (tRFC1min), Most Significant Byte */
        };
        uint16_t tRFC1_min_mtb;
    };
    union {
        struct {
            uint8_t tRFC2_min_mtb_lsb;                      /* Byte 32 (0x020): Minimum Refresh Recovery Delay Time (tRFC2min), Least Significant Byte */
            uint8_t tRFC2_min_mtb_msb;                      /* Byte 33 (0x021): Minimum Refresh Recovery Delay Time (tRFC2min), Most Significant Byte */
        };
        uint16_t tRFC2_min_mtb;
    };
    union {
        struct {
            uint8_t tRFC4_min_mtb_lsb;                      /* Byte 34 (0x022): Minimum Refresh Recovery Delay Time (tRFC4min), Least Significant Byte */
            uint8_t tRFC4_min_mtb_msb;                      /* Byte 35 (0x023): Minimum Refresh Recovery Delay Time (tRFC4min), Most Significant Byte */
        };
        uint16_t tRFC4_min_mtb;
    };
    uint8_t tFAW_min_mtb_msb;                               /* Byte 36 (0x024): Upper Nibble for tFAW */
    uint8_t tFAW_min_mtb_lsb;                               /* Byte 37 (0x025): Minimum Four Activate Window Delay Time (tFAWmin), Least Significant Byte */
    uint8_t tRRD_S_min_mtb;                                 /* Byte 38 (0x026): Minimum Activate to Activate Delay Time (tRRD_Smin), different bank group */
    uint8_t tRRD_L_min_mtb;                                 /* Byte 39 (0x027): Minimum Activate to Activate Delay Time (tRRD_Lmin), same bank group */
    uint8_t tCCD_L_min_mtb;                                 /* Byte 40 (0x028): Minimum CAS to CAS Delay Time (tCCD_Lmin), same bank group */
    uint8_t tWR_min_mtb_msb;                                /* Byte 41 (0x029): Upper Nibble for tWRmin */
    uint8_t tWR_min_mtb_lsb;                                /* Byte 42 (0x02A): Minimum Write Recovery Time (tWRmin) */
    uint8_t tWTR_L_min_tWTR_S_min_mtb_msb;                  /* Byte 43 (0x02B): Upper Nibbles for tWTRmin */
    uint8_t tWTR_S_min_mtb_lsb;                             /* Byte 44 (0x02C): Minimum Write to Read Time (tWTR_Smin), different bank group */
    uint8_t tWTR_L_min_mtb_lsb;                             /* Byte 45 (0x02D): Minimum Write to Read Time (tWTR_Lmin), same bank group */
    uint8_t _RESERVED1[14];                                 /* Byte 46~59 (0x02E~0x03B): Reserved, Base Configuration Section */
    uint8_t connector_to_SDRAM_bit_mapping[18];             /* Bytes 60~77 (0x03C~0x04D): Connector to SDRAM Bit Mapping */
    uint8_t _RESERVED2[39];                                 /* Bytes 78~116 (0x04E~0x074): Reserved, Base Configuration Section */
    int8_t tCCD_L_min_ftb;                                  /* Byte 117 (0x075): Fine Offset for Minimum CAS to CAS Delay Time (tCCD_Lmin), same bank group */
    int8_t tRRD_L_min_ftb;                                  /* Byte 118 (0x076): Fine Offset for Minimum Activate to Activate Delay Time (tRRD_Lmin), same bank group */
    int8_t tRRD_S_min_ftb;                                  /* Byte 119 (0x077): Fine Offset for Minimum Activate to Activate Delay Time (tRRD_Smin), different bank group */
    int8_t tRC_min_ftb;                                     /* Byte 120 (0x078): Fine Offset for Minimum Active to Active/Refresh Delay Time (tRCmin) */
    int8_t tRP_min_ftb;                                     /* Byte 121 (0x079): Fine Offset for Minimum Row Precharge Delay Time (tRPmin) */
    int8_t tRCD_min_ftb;                                    /* Byte 122 (0x07A): Fine Offset for Minimum RAS to CAS Delay Time (tRCDmin) */
    int8_t tAA_min_ftb;                                     /* Byte 123 (0x07B): Fine Offset for Minimum CAS Latency Time (tAAmin) */
    int8_t tCKAVG_max_ftb;                                  /* Byte 123 (0x07B): Fine Offset for Minimum CAS Latency Time (tAAmin) */
    int8_t tCKAVG_min_ftb;                                  /* Byte 125 (0x07D): Fine Offset for SDRAM Minimum Cycle Time (tCKAVGmin) */
    union {
        struct {
            uint8_t crc_lsb;                                /* Byte 126 (0x07E): Cyclical Redundancy Code (CRC) for Base Configuration Section, Least Significant Byte */
            uint8_t crc_msb;                                /* Byte 127 (0x07F): Cyclical Redundancy Code (CRC) for Base Configuration Section, Most Significant Byte */
        };
        uint16_t crc;
    };
    union {
        struct {
            uint8_t raw_card_extension_module_nom_height;   /* Byte 128 (0x080) (Unbuffered): Raw Card Extension, Module Nominal Height */
            uint8_t module_max_thickness;                   /* Byte 129 (0x081) (Unbuffered): Module Maximum Thickness */
            uint8_t ref_raw_card_used;                      /* Byte 130 (0x082) (Unbuffered): Reference Raw Card Used */
            uint8_t address_mapping_from_edge_connector_to_dram;     /* Byte 131 (0x083) (Unbuffered): Address Mapping from Edge Connector to DRAM */
            uint8_t _RESERVED0[121];                        /* Bytes 132~253 (0x084~0x0FD) (Unbuffered): Reserved */
            union {
                struct {
                    uint8_t crc_lsb;                        /* Byte 254 (0x0FE) (Unbuffered): Cyclical Redundancy Code (CRC) for SPD Block 1, Least Significant Byte */
                    uint8_t crc_msb;                        /* Byte 255 (0x0FF) (Unbuffered): Cyclical Redundancy Code (CRC) for SPD Block 1, Most Significant Byte */
                };
                uint16_t crc;
            };
        } UDIMM;
        struct {
            uint8_t raw_card_extension_module_nom_height;   /* Byte 128 (0x080) (Registered): Raw Card Extension, Module Nominal Height */
            uint8_t module_max_thickness;                   /* Byte 129 (0x081) (Registered): Module Maximum Thickness */
            uint8_t ref_raw_card_used;                      /* Byte 130 (0x082) (Registered): Reference Raw Card */
            uint8_t dimm_attributes;                        /* Byte 131 (0x083) (Registered): DIMM Attributes */
            uint8_t rdimm_thermal_heat_spreader_solution;   /* Byte 132 (0x084) (Registered): RDIMM Thermal Heat Spreader Solution */
            uint8_t register_mfr_id_code_lsb;               /* Byte 133 (0x085) (Registered): Register Manufacturer ID Code, First Byte */
            uint8_t register_mfr_id_code_msb;               /* Byte 134 (0x086) (Registered): Register Manufacturer ID Code, Second Byte */
            uint8_t register_rev_number;                    /* Byte 135 (0x087) (Registered): Register Revision Number */
            uint8_t address_mapping_from_register_to_dram;  /* Byte 136 (0x088) (Registered): Address Mapping from Register to DRAM */
            uint8_t register_output_ds_for_control_and_ca;  /* Byte 137 (0x089) (Registered): Register Output Drive Strength for Control and Command/ Address */
            uint8_t register_output_ds_for_clk;             /* Byte 138 (0x08A) (Registered): Register Output Drive Strength for Clock */
            uint8_t _RESERVED0[115];                        /* Bytes 139~253 (0x08B~0x0FD) (Registered): Reserved */
            union {
                struct {
                    uint8_t crc_lsb;                        /* Byte 254 (0x0FE) (Registered): Cyclical Redundancy Code (CRC) for SPD Block 1, Least Significant Byte */
                    uint8_t crc_msb;                        /* Byte 255 (0x0FF) (Registered): Cyclical Redundancy Code (CRC) for SPD Block 1, Most Significant Byte */
                };
                uint16_t crc;
            };
        } RDIMM;
        struct {
            uint8_t raw_card_extension_module_nom_height;   /* Byte 128 (0x080) (Load Reduced): Raw Card Extension, Module Nominal Height */
            uint8_t module_max_thickness;                   /* Byte 129 (0x081) (Load Reduced): Module Maximum Thickness */
            uint8_t ref_raw_card_used;                      /* Byte 130 (0x082) (Load Reduced): Reference Raw Card Used */
            uint8_t dimm_attributes;                        /* Byte 131 (0x083) (Load Reduced): DIMM Attributes */
            uint8_t lrdimm_thermal_heat_spreader_solution;  /* Byte 132 (0x084) (Load Reduced): LRDIMM Thermal Heat Spreader Solution */
            uint8_t register_and_db_mfr_id_code_lsb;        /* Byte 133 (0x085) (Load Reduced): Register and Data Buffer Manufacturer ID Code, First Byte */
            uint8_t register_and_db_mfr_id_code_msb;        /* Byte 134 (0x086) (Load Reduced): Register and Data Buffer Manufacturer ID Code, Most Significant Byte */
            uint8_t register_rev_number;                    /* Byte 135 (0x087) (Load Reduced): Register Revision Number */
            uint8_t address_mapping_from_register_to_dram;  /* Byte 136 (0x088) (Load Reduced): Address Mapping from Register to DRAM */
            uint8_t register_output_ds_for_control_and_ca;  /* Byte 137 (0x089) (Load Reduced): Register Output Drive Strength for Control and Command/Address */
            uint8_t register_output_ds_for_clk_and_db;      /* Byte 138 (0x08A) (Load Reduced): Register Output Drive Strength for Clock and Data Buffer Control */
            uint8_t db_rev_number;                          /* Byte 139 (0x08B) (Load Reduced): Data Buffer Revision Number */
            uint8_t dram_VrefDQ_for_package_rank0;          /* Byte 140 (0x08C) (Load Reduced): DRAM VrefDQ for Package Rank 0 */
            uint8_t dram_VrefDQ_for_package_rank1;          /* Byte 141 (0x08D) (Load Reduced): DRAM VrefDQ for Package Rank 1 */
            uint8_t dram_VrefDQ_for_package_rank2;          /* Byte 142 (0x08E) (Load Reduced): DRAM VrefDQ for Package Rank 2 */
            uint8_t dram_VrefDQ_for_package_rank3;          /* Byte 143 (0x08F) (Load Reduced): DRAM VrefDQ for Package Rank 3 */
            uint8_t db_VrefDQ_for_dram_if;                  /* Byte 144 (0x090) (Load Reduced): Data Buffer VrefDQ for DRAM Interface */
            uint8_t db_ds_and_rtt_for_mdq_lte1866;          /* Byte 145 (0x091) (Load Reduced): Data Buffer MDQ Drive Strength and RTT for data rate < 1866 */
            uint8_t db_ds_and_rtt_for_mdq_gt1866_lte2400;   /* Byte 146 (0x092) (Load Reduced): Data Buffer MDQ Drive Strength and RTT for 1866 < data rate < 2400 */
            uint8_t db_ds_and_rtt_for_mdq_gt2400_lte3200;   /* Byte 147 (0x093) (Load Reduced): Data Buffer MDQ Drive Strength and RTT for 2400 < data rate < 3200 */
            uint8_t dram_ds;                                /* Byte 148 (0x094) (Load Reduced): DRAM Drive Strength (for data rates < 1866, 1866 < data rate < 2400, and 2400 < data rate < 3200) */
            uint8_t dram_rtt_wr_rtt_nom_lte1866;            /* Byte 149 (0x095) (Load Reduced): DRAM ODT (RTT_WR and RTT_NOM) for data rate < 1866 */
            uint8_t dram_rtt_wr_rtt_nom_gt1866_lte2400;     /* Byte 150 (0x096) (Load Reduced): DRAM ODT (RTT_WR and RTT_NOM) for 1866 < data rate < 2400 */
            uint8_t dram_rtt_wr_rtt_nom_gt2400_lte3200;     /* Byte 151 (0x097) (Load Reduced): DRAM ODT (RTT_WR and RTT_NOM) for 2400 < data rate < 3200 */
            uint8_t dram_rtt_park_lte1866;                  /* Byte 152 (0x098) (Load Reduced): DRAM ODT (RTT_PARK) for data rate < 1866 */
            uint8_t dram_rtt_park_gt1866_lte2400;           /* Byte 153 (0x099) (Load Reduced): DRAM ODT (RTT_PARK) for 1866 < data rate < 2400 */
            uint8_t dram_rtt_park_gt2400_lte3200;           /* Byte 154 (0x09A) (Load Reduced): DRAM ODT (RTT_PARK) for 2400 < data rate < 3200 */
            uint8_t db_VrefDQ_for_dram_if_range;            /* Byte 155 (0x09B) (Load Reduced): Data Buffer VrefDQ for DRAM Interface Range */
            uint8_t db_dq_dfe;                              /* Byte 156 (0x09C) (Load Reduced): Data Buffer DQ Decision Feedback Equalization (DFE) */
            uint8_t _RESERVED0[97];                         /* Bytes 157~253 (0x09D~0x0FD) (Load Reduced): Reserved */
            union {
                struct {
                    uint8_t crc_lsb;                        /* Bytes 254 (0x0FE) (Load Reduced): Cyclical Redundancy Code (CRC) for SPD Block 1, Least Significant Byte */
                    uint8_t crc_msb;                        /* Bytes 255 (0x0FF) (Load Reduced): Cyclical Redundancy Code (CRC) for SPD Block 1, Most Significant Byte */
                };
                uint16_t crc;
            };
        } LRDIMM;
    };                                                      /* Module-Specific Section: Bytes 128~256 (0x080~0x0FF) */
    uint8_t _RESERVED3[256];                                /* Bytes 256~512 (0x100~0x1FF): Reserved */
} __attribute__((packed)) spd_ddr4_t;

int core_ddr4(app_options_t *options);

#endif /* TOOLS_SPDGENERATOR_INCLUDE_SPD_DDR4_H_ */
