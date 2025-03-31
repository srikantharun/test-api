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


#include "spd_ddr4.h"
#include "spd_utils.h"

static bool parser_conf_file_ddr4(char * spd_ini_path, spd_ddr4_t *ddr4);

int core_ddr4(app_options_t *options)
{
    spd_ddr4_t ddr4;
    FILE * spd_bin_file;
    bool rtrn;

    if (NULL == options) {
        return EXIT_FAILURE;
    }

    if ((NULL == options->spd_ini_path) || (NULL == options->spd_bin_path)) {
        return EXIT_FAILURE;
    }

    memset(&ddr4, '\0', sizeof(ddr4));

    ddr4.bytes_total_used = 0x23;                       /* 000 */
    ddr4.revision = 0x11;                               /* 001 */
    ddr4.kb_dram_device_type = 0x0c;                    /* 002 */
    ddr4.kb_module_type = 0x02;                         /* 003 */
    ddr4.sdram_density_banks = 0x86;                    /* 004 */
    ddr4.sdram_addressing = 0x29;                       /* 005 */
    ddr4.primary_sdram_package_type = 0x00;             /* 006 */
    ddr4.sdram_optional_features = 0x08;                /* 007 */
    ddr4.sdram_thermal_and_refresh_options = 0x00;      /* 008 */
    ddr4.other_sdram_optional_features = 0x60;          /* 009 */
    ddr4.secondary_sdram_package_type = 0x00;           /* 010 */
    ddr4.module_nom_voltage_vdd = 0x03;                 /* 011 */
    ddr4.module_organization = 0x01;                    /* 012 */
    ddr4.module_memory_bus_width = 0x0B;                /* 013 */
    ddr4.module_thermal_sensor = 0x00;//0x80;           /* 014 */
    ddr4.extended_module_type = 0x00;                   /* 015 */
                                                        /* 016 */
    ddr4.timebases = 0x00;                              /* 017 */
    ddr4.tCKAVG_min_mtb = 0x05;                         /* 018 */
    ddr4.tCKAVG_max_mtb = 0x0d;                         /* 019 */
    ddr4.CL_supported = 0x002ffff8;                     /* 020 ~ 023 */
    ddr4.tAA_min_mtb = 0x6e;                            /* 024 */
    ddr4.tRCD_min_mtb = 0x6e;                           /* 025 */
    ddr4.tRP_min_mtb = 0x6e;                            /* 026 */
    ddr4.tRAS_min_tRC_min_mtb_msb = 0x11;               /* 027 */
    ddr4.tRAS_min_mtb_lsb = 0x00;                       /* 028 */
    ddr4.tRC_min_mtb_lsb = 0x6e;                        /* 029 */
    ddr4.tRFC1_min_mtb = 0x0af0;                        /* 030 ~ 031 */
    ddr4.tRFC2_min_mtb = 0x0820;                        /* 032 ~ 033 */
    ddr4.tRFC4_min_mtb = 0x0500;                        /* 034 ~ 035 */
    ddr4.tFAW_min_mtb_msb = 0x00;                       /* 036 */
    ddr4.tFAW_min_mtb_lsb = 0xa8;                       /* 037 */
    ddr4.tRRD_S_min_mtb = 0x14;                         /* 038 */
    ddr4.tRRD_L_min_mtb = 0x28;                         /* 039 */
    ddr4.tCCD_L_min_mtb = 0x28;                         /* 040 */
    ddr4.tWR_min_mtb_msb = 0x00;                        /* 041 */
    ddr4.tWR_min_mtb_lsb = 0x78;                        /* 042 */
    ddr4.tWTR_L_min_tWTR_S_min_mtb_msb = 0x00;          /* 043 */
    ddr4.tWTR_S_min_mtb_lsb = 0x14;                     /* 044 */
    ddr4.tWTR_L_min_mtb_lsb = 0x3c;                     /* 045 */
                                                        /* 046 ~ 059 */
    ddr4.connector_to_SDRAM_bit_mapping[0] = 0x16;      /* 060 */
    ddr4.connector_to_SDRAM_bit_mapping[1] = 0x36;      /* 061 */
    ddr4.connector_to_SDRAM_bit_mapping[2] = 0x16;      /* 062 */
    ddr4.connector_to_SDRAM_bit_mapping[3] = 0x36;      /* 063 */
    ddr4.connector_to_SDRAM_bit_mapping[4] = 0x16;      /* 064 */
    ddr4.connector_to_SDRAM_bit_mapping[5] = 0x36;      /* 065 */
    ddr4.connector_to_SDRAM_bit_mapping[6] = 0x16;      /* 066 */
    ddr4.connector_to_SDRAM_bit_mapping[7] = 0x36;      /* 067 */
    ddr4.connector_to_SDRAM_bit_mapping[8] = 0x16;      /* 068 */
    ddr4.connector_to_SDRAM_bit_mapping[9] = 0x36;      /* 069 */
    ddr4.connector_to_SDRAM_bit_mapping[10] = 0x16;     /* 070 */
    ddr4.connector_to_SDRAM_bit_mapping[11] = 0x36;     /* 071 */
    ddr4.connector_to_SDRAM_bit_mapping[12] = 0x16;     /* 072 */
    ddr4.connector_to_SDRAM_bit_mapping[13] = 0x36;     /* 073 */
    ddr4.connector_to_SDRAM_bit_mapping[14] = 0x16;     /* 074 */
    ddr4.connector_to_SDRAM_bit_mapping[15] = 0x36;     /* 075 */
    ddr4.connector_to_SDRAM_bit_mapping[16] = 0x16;     /* 076 */
    ddr4.connector_to_SDRAM_bit_mapping[17] = 0x36;     /* 077 */
                                                        /* 078 ~ 116 */
    ddr4.tCCD_L_min_ftb = 0x00;                         /* 117 */
    ddr4.tRRD_L_min_ftb = 0x9c;                         /* 118 */
    ddr4.tRRD_S_min_ftb = 0x00;                         /* 119 */
    ddr4.tRC_min_ftb = 0x00;                            /* 120 */
    ddr4.tRP_min_ftb = 0x00;                            /* 121 */
    ddr4.tRCD_min_ftb = 0x00;                           /* 122 */
    ddr4.tAA_min_ftb = 0x00;                            /* 123 */
    ddr4.tCKAVG_max_ftb = 0xe7;                         /* 124 */
    ddr4.tCKAVG_min_ftb = 0x00;                         /* 125 */


    switch (ddr4.kb_module_type & 0x07) {
        case 2:
            /* UDIMM */
            ddr4.UDIMM.raw_card_extension_module_nom_height = 0x11;            /* 128 */
            ddr4.UDIMM.module_max_thickness = 0x01;                            /* 129 */
            ddr4.UDIMM.ref_raw_card_used = 0x43;                               /* 130 */
            ddr4.UDIMM.address_mapping_from_edge_connector_to_dram = 0x00;     /* 131 */
                                                                               /* 132 ~ 191 */
            break;
        case 1:
            /* RDIMM */
            ddr4.RDIMM.raw_card_extension_module_nom_height = 0x00;      /* 128 */
            ddr4.RDIMM.module_max_thickness = 0x00;                      /* 129 */
            ddr4.RDIMM.ref_raw_card_used = 0x00;                         /* 130 */
            ddr4.RDIMM.dimm_attributes = 0x00;                           /* 131 */
            ddr4.RDIMM.rdimm_thermal_heat_spreader_solution = 0x00;      /* 132 */
            ddr4.RDIMM.register_mfr_id_code_lsb = 0x00;                  /* 133 */
            ddr4.RDIMM.register_mfr_id_code_msb = 0x00;                  /* 134 */
            ddr4.RDIMM.register_rev_number = 0x00;                       /* 135 */
            ddr4.RDIMM.address_mapping_from_register_to_dram = 0x00;     /* 136 */
            ddr4.RDIMM.register_output_ds_for_control_and_ca = 0x00;     /* 137 */
            ddr4.RDIMM.register_output_ds_for_clk = 0x00;                /* 138 */
                                                                         /* 132 ~ 191 */
            break;
        case 4:
            /* LRDIMM */
            ddr4.LRDIMM.raw_card_extension_module_nom_height = 0x00;       /* 128 */
            ddr4.LRDIMM.module_max_thickness = 0x00;                       /* 129 */
            ddr4.LRDIMM.ref_raw_card_used = 0x00;                          /* 130 */
            ddr4.LRDIMM.dimm_attributes = 0x00;                            /* 131 */
            ddr4.LRDIMM.lrdimm_thermal_heat_spreader_solution = 0x00;      /* 132 */
            ddr4.LRDIMM.register_and_db_mfr_id_code_lsb = 0x00;            /* 133 */
            ddr4.LRDIMM.register_and_db_mfr_id_code_msb = 0x00;            /* 134 */
            ddr4.LRDIMM.register_rev_number = 0x00;                        /* 135 */
            ddr4.LRDIMM.address_mapping_from_register_to_dram = 0x00;      /* 136 */
            ddr4.LRDIMM.register_output_ds_for_control_and_ca = 0x00;      /* 137 */
            ddr4.LRDIMM.register_output_ds_for_clk_and_db = 0x00;          /* 138 */
            ddr4.LRDIMM.db_rev_number = 0x00;                              /* 139 */
            ddr4.LRDIMM.dram_VrefDQ_for_package_rank0 = 0x00;              /* 140 */
            ddr4.LRDIMM.dram_VrefDQ_for_package_rank1 = 0x00;              /* 141 */
            ddr4.LRDIMM.dram_VrefDQ_for_package_rank2 = 0x00;              /* 142 */
            ddr4.LRDIMM.dram_VrefDQ_for_package_rank3 = 0x00;              /* 143 */
            ddr4.LRDIMM.db_VrefDQ_for_dram_if = 0x00;                      /* 144 */
            ddr4.LRDIMM.db_ds_and_rtt_for_mdq_lte1866 = 0x00;              /* 145 */
            ddr4.LRDIMM.db_ds_and_rtt_for_mdq_gt1866_lte2400 = 0x00;       /* 146 */
            ddr4.LRDIMM.db_ds_and_rtt_for_mdq_gt2400_lte3200 = 0x00;       /* 147 */
            ddr4.LRDIMM.dram_ds = 0x00;                                    /* 148 */
            ddr4.LRDIMM.dram_rtt_wr_rtt_nom_lte1866 = 0x00;                /* 149 */
            ddr4.LRDIMM.dram_rtt_wr_rtt_nom_gt1866_lte2400 = 0x00;         /* 150 */
            ddr4.LRDIMM.dram_rtt_wr_rtt_nom_gt2400_lte3200 = 0x00;         /* 151 */
            ddr4.LRDIMM.dram_rtt_park_lte1866 = 0x00;                      /* 152 */
            ddr4.LRDIMM.dram_rtt_park_gt1866_lte2400 = 0x00;               /* 153 */
            ddr4.LRDIMM.dram_rtt_park_gt2400_lte3200 = 0x00;               /* 154 */
            ddr4.LRDIMM.db_VrefDQ_for_dram_if_range = 0x00;                /* 155 */
            ddr4.LRDIMM.db_dq_dfe = 0x00;                                  /* 156 */
                                                                           /* 157 ~ 191 */
            break;
        default:
            return EXIT_FAILURE;
    }

    rtrn = parser_conf_file_ddr4(options->spd_ini_path, &ddr4);
    if (false == rtrn) {
        return EXIT_FAILURE;
    }

    /* 126 ~ 127 */    ddr4.crc = crc16_calc((uint8_t *)&ddr4, (uint8_t *)&ddr4.crc - (uint8_t *)&ddr4);

    switch (ddr4.kb_module_type & 0x07) {
        case 2:
            /* UDIMM */
            /* 254 ~ 255 */    ddr4.UDIMM.crc = crc16_calc((uint8_t *)&ddr4.UDIMM, (uint8_t *)&ddr4.UDIMM.crc - (uint8_t *)&ddr4.UDIMM);
            break;
        case 1:
            /* RDIMM */
            /* 254 ~ 255 */    ddr4.RDIMM.crc = crc16_calc((uint8_t *)&ddr4.RDIMM, (uint8_t *)&ddr4.RDIMM.crc - (uint8_t *)&ddr4.RDIMM);
            break;
        case 4:
            /* LRDIMM */
            /* 254 ~ 255 */    ddr4.LRDIMM.crc = crc16_calc((uint8_t *)&ddr4.LRDIMM, (uint8_t *)&ddr4.LRDIMM.crc - (uint8_t *)&ddr4.LRDIMM);
            break;
    }

    spd_bin_file = fopen(options->spd_bin_path, "w");
    if (NULL == spd_bin_file) {
        perror("SPD bin file open error: ");
        return EXIT_SUCCESS;
    }

    fwrite(&ddr4, sizeof(ddr4), 1, spd_bin_file);
    printf("ddr4 Binary SPD dump file = %lu bytes\n", sizeof(ddr4));
    fclose(spd_bin_file);


    return EXIT_SUCCESS;
}


static bool parser_conf_file_ddr4(char * spd_ini_path, spd_ddr4_t *ddr4)
{
    uint32_t value, tmp;
    char name[30];
    FILE * spd_ini_file;
    bool rtrn = true;

    spd_ini_file = fopen(spd_ini_path, "r");
    if (NULL == spd_ini_file) {
        fprintf(stderr, "SPD ini file (%s) open failed: %s\n", spd_ini_path, strerror(errno));
        return false;
    }

    printf("Fundamental Memory Class = DDR4 SDRAM\n");
    while (fscanf(spd_ini_file, "%s %u", &name[0], &value) == 2)
    {
        tmp = value;
        if (SNPS_COMP_STR(name, "type")) {
            ddr4->kb_module_type &= ~0x0f;
            switch (value) {
                case 1:
                    printf("Base Module Type = RDIMM\n");
                    break;
                case 2:
                    printf("Base Module Type = UDIMM\n");
                    break;
                case 4:
                    printf("Base Module Type = LRDIMM\n");
                    break;
                default:
                    printf("Invalid Base Module Type\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->kb_module_type |= value;
        } else if (SNPS_COMP_STR(name, "capacity")) {
            ddr4->sdram_density_banks &= ~0x0f;
            switch (value) {
                case 0:
                    printf("Module Capacity = 256 Mb\n");
                    break;
                case 1:
                    printf("Module Capacity = 512 Mb\n");
                    break;
                case 2:
                    printf("Module Capacity = 1 Gb\n");
                    break;
                case 3:
                    printf("Module Capacity = 2 Gb\n");
                    break;
                case 4:
                    printf("Module Capacity = 4 Gb\n");
                    break;
                case 5:
                    printf("Module Capacity = 8 Gb\n");
                    break;
                case 6:
                    printf("Module Capacity = 16 Gb\n");
                    break;
                case 7:
                    printf("Module Capacity = 32 Gb\n");
                    break;
                case 8:
                    printf("Module Capacity = 12 Gb\n");
                    break;
                case 9:
                    printf("Module Capacity = 24 Gb\n");
                    break;
                default:
                    printf("Invalid Module Capacity\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->sdram_density_banks |= value;
        } else if (SNPS_COMP_STR(name, "banks")) {
            ddr4->sdram_density_banks &= ~0x30;
            switch (value) {
                case 0:
                    printf("Number of Bank Addresses = 2 bits (4 banks)\n");
                    break;
                case 1:
                    printf("Number of Bank Addresses = 3 bits (8 banks)\n");
                    break;
                default:
                    printf("Invalid Number of Bank Addresses\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->sdram_density_banks |= (value << 4);
        } else if (SNPS_COMP_STR(name, "col_address")) {
            ddr4->sdram_addressing &= ~0x07;
            switch (value) {
                case 0:
                    printf("Number of Column Addresses = 9 bits\n");
                    break;
                case 1:
                    printf("Number of Column Addresses = 10 bits\n");
                    break;
                case 2:
                    printf("Number of Column Addresses = 11 bits\n");
                    break;
                case 3:
                    printf("Number of Column Addresses = 12 bits\n");
                    break;
                default:
                    printf("Invalid Number of Column Addresses\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->sdram_addressing |= value;
        } else if (SNPS_COMP_STR(name, "row_address")) {
            ddr4->sdram_addressing &= ~0x38;
            switch (value) {
                case 0:
                    printf("Number of Row Addresses = 12 bits\n");
                    break;
                case 1:
                    printf("Number of Row Addresses = 13 bits\n");
                    break;
                case 2:
                    printf("Number of Row Addresses = 14 bits\n");
                    break;
                case 3:
                    printf("Number of Row Addresses = 15 bits\n");
                    break;
                case 4:
                    printf("Number of Row Addresses = 16 bits\n");
                    break;
                case 5:
                    printf("Number of Row Addresses = 17 bits\n");
                    break;
                case 6:
                    printf("Number of Row Addresses = 18 bits\n");
                    break;
                default:
                    printf("Invalid Number of Row Addresses\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->sdram_addressing |= value << 3;
        } else if (SNPS_COMP_STR(name, "bank_group")) {
            ddr4->sdram_density_banks &= ~0xc0;
            switch (value) {
                case 0:
                    printf("Bank Group Addressing = 0 bit (no groups)\n");
                    break;
                case 1:
                    printf("Bank Group Addressing = 1 bit (2 groups)\n");
                    break;
                case 2:
                    printf("Bank Group Addressing = 2 bits (4 groups)\n");
                    break;
                default:
                    printf("Invalid Bank Group Addressing\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->sdram_density_banks |= (value << 6);
        } else if (SNPS_COMP_STR(name, "device_width")) {
            ddr4->module_organization &= ~0x07;
            switch (value) {
                case 0:
                    printf("DRAM Device Width = 4 bits\n");
                    break;
                case 1:
                    printf("DRAM Device Width = 8 bits\n");
                    break;
                case 2:
                    printf("DRAM Device Width = 16 bits\n");
                    break;
                case 3:
                    printf("DRAM Device Width = 32 bits\n");
                    break;
                default:
                    printf("Invalid DRAM Device Width\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->module_organization |= value;
        } else if (SNPS_COMP_STR(name, "device_ranks")) {
            ddr4->module_organization &= ~0x18;
            if (value > 7) {
                printf("Invalid Number of DIMM Ranks\n");
                rtrn = false;
                goto close_and_return;
            } else {
                printf("Number of DIMM Ranks = %u\n", value + 1);
            }
            ddr4->module_organization |= value << 3;
        } else if (SNPS_COMP_STR(name, "bus_width")) {
            ddr4->module_memory_bus_width &= ~0x07;
            switch (value) {
                case 0:
                    printf("Primary Memory Bus Width = 8 bits\n");
                    break;
                case 1:
                    printf("Primary Memory Bus Width = 16 bits\n");
                    break;
                case 2:
                    printf("Primary Memory Bus Width = 32 bits\n");
                    break;
                case 3:
                    printf("Primary Memory Bus Width = 64 bits\n");
                    break;
                default:
                    printf("Invalid Primary Memory Bus Width\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->module_memory_bus_width |= value;
        } else if (SNPS_COMP_STR(name, "ecc")) {
            ddr4->module_memory_bus_width &= ~0x18;
            if (value > 1) {
                printf("Invalid Memory Bus Width Extension\n");
                rtrn = false;
                goto close_and_return;
            }
            ddr4->module_memory_bus_width |= value << 3;
            printf("Memory Bus Width Extension = %u bits\n", ((ddr4->module_memory_bus_width & 0x18) >> 3) * 8);
        } else if (SNPS_COMP_STR(name, "address_mirror")) {
            if ((value != 0) && (value != 1)) {
                printf("Invalid Address Mirror configuration, supported 0 - disable, 1 - enable\n");
                rtrn = false;
                goto close_and_return;
            }
            switch (ddr4->kb_module_type & 0xf) {
                case 1:
                    ddr4->UDIMM.address_mapping_from_edge_connector_to_dram = value & 0x01;
                    break;
                case 2:
                    ddr4->RDIMM.address_mapping_from_register_to_dram = value & 0x01;
                    break;
                default:
                    printf("Address mirror is only supported in RDIMM and UDIMM configs\n");
                    rtrn = false;
                    goto close_and_return;
            }
            printf("Address Mirror = %u\n", value);
        } else if (SNPS_COMP_STR(name, "package_type")) {
            ddr4->primary_sdram_package_type &= ~0x80;
            if (value) {
                printf("DRAM Device Package = Non-Standard Monolithic\n");
                ddr4->primary_sdram_package_type |= 0x80;
            } else {
                printf("DRAM Device Package = Standard Monolithic\n");
            }
        } else if (SNPS_COMP_STR(name, "die_count")) {
            ddr4->primary_sdram_package_type &= ~0x70;
            switch (value) {
                case 0:
                    printf("DRAM Device Die Count = Single die\n");
                    break;
                case 1:
                    printf("DRAM Device Die Count = 2 die\n");
                    break;
                case 2:
                    printf("DRAM Device Die Count = 3 die\n");
                    break;
                case 3:
                    printf("DRAM Device Die Count = 4 die\n");
                    break;
                case 4:
                    printf("DRAM Device Die Count = 5 die\n");
                    break;
                case 5:
                    printf("DRAM Device Die Count = 6 die\n");
                    break;
                case 6:
                    printf("DRAM Device Die Count = 7 die\n");
                    break;
                case 7:
                    printf("DRAM Device Die Count = 8 die\n");
                    break;
                default:
                    printf("Invalid DRAM Device Die Count\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->primary_sdram_package_type |= value << 4;
        } else if (SNPS_COMP_STR(name, "signal_loading")) {
            ddr4->primary_sdram_package_type &= ~0x02;
            switch (value) {
                case 0:
                    printf("Signal Loading = Not specified\n");
                    break;
                case 1:
                    printf("Signal Loading = Multi load stack\n");
                    break;
                case 2:
                    printf("Signal Loading = Single load stack (3DS)\n");
                    break;
                default:
                    printf("Invalid Signal Loading\n");
                    rtrn = false;
                    goto close_and_return;
            }
            ddr4->primary_sdram_package_type |= value;
        } else if (SNPS_COMP_STR(name, "CL_supported")) {
            printf("CAS Latencies Supported:");
            uint8_t i;
            if (value & 0x80000000) {
                //High range
                for (i = 52, tmp = 0x20000000; i > 22; i--, tmp >>= 1) {
                    if (value & tmp)
                        printf(" %uT", i);
                }
            } else {
                //Low range
                for (i = 36, tmp = 0x20000000; i > 6; i--, tmp >>= 1) {
                    if (value & tmp)
                        printf(" %uT", i);
                }
            }
            printf("\n");
            ddr4->CL_supported = value;
        } else if (SNPS_COMP_STR(name, "tCKAVGmin")) {
            reverse_calculation(value, &ddr4->tCKAVG_min_mtb, &ddr4->tCKAVG_min_ftb);
            printf("Minimum Clock Cycle Time (tCK min):\t\t\t%u ps\t\ttCKAVG_min_mtb = %u\ttCKAVG_min_ftb = %d\n", value, ddr4->tCKAVG_min_mtb, ddr4->tCKAVG_min_ftb);
        } else if (SNPS_COMP_STR(name, "tCKAVGmax")) {
            reverse_calculation(value, &ddr4->tCKAVG_max_mtb, &ddr4->tCKAVG_max_ftb);
            printf("Maximum Clock Cycle Time (tCK max):\t\t\t%u ps\t\ttCKAVG_max_mtb = %u\ttCKAVG_max_ftb = %d\n", value, ddr4->tCKAVG_max_mtb, ddr4->tCKAVG_max_ftb);
        } else if (SNPS_COMP_STR(name, "tAAmin")) {
            reverse_calculation(value, &ddr4->tAA_min_mtb, &ddr4->tAA_min_ftb);
            printf("CAS# Latency Time (tAA min):\t\t\t\t%u ps\ttAA_min_mtb = %u\ttAA_min_ftb = %d\n", value, ddr4->tAA_min_mtb, ddr4->tAA_min_ftb);
        } else if (SNPS_COMP_STR(name, "tRCDmin")) {
            reverse_calculation(value, &ddr4->tRCD_min_mtb, &ddr4->tRCD_min_ftb);
            printf("RAS# to CAS# Delay Time (tRCD min):\t\t\t%u ps\ttRCD_min_mtb = %u\ttRCD_min_ftb = %d\n", value, ddr4->tRCD_min_mtb, ddr4->tRCD_min_ftb);
        } else if (SNPS_COMP_STR(name, "tRPmin")) {
            reverse_calculation(value, &ddr4->tRP_min_mtb, &ddr4->tRP_min_ftb);
            printf("Row Precharge Delay Time (tRP min):\t\t\t%u ps\ttRP_min_mtb = %u\ttRP_min_ftb = %d\n", value, ddr4->tRP_min_mtb, ddr4->tRP_min_ftb);
        } else if (SNPS_COMP_STR(name, "tRASmin")) {
            tmp /= MTB;
            ddr4->tRAS_min_tRC_min_mtb_msb &= ~0xf0;
            ddr4->tRAS_min_tRC_min_mtb_msb |= (tmp & 0x00000f00) >> 4;
            ddr4->tRAS_min_mtb_lsb = tmp & 0x000000ff;
            printf("Active to Precharge Delay Time (tRAS min):\t\t%u ps\ttRAS_min_mtb = %u\n", value, ((ddr4->tRAS_min_tRC_min_mtb_msb & 0xf0) << 4) | ddr4->tRAS_min_mtb_lsb);
        } else if (SNPS_COMP_STR(name, "tRCmin")) {
            tmp /= MTB;
            ddr4->tRAS_min_tRC_min_mtb_msb &= ~0x0f;
            ddr4->tRAS_min_tRC_min_mtb_msb |= (tmp & 0x00000f00) >> 8;
            ddr4->tRC_min_mtb_lsb = tmp & 0x000000ff;
            printf("Act to Act/Refresh Delay Time (tRC min):\t\t%u ps\ttRC_min_mtb = %u\n", value, ((ddr4->tRAS_min_tRC_min_mtb_msb & 0x0f) << 8) | ddr4->tRC_min_mtb_lsb);
        } else if (SNPS_COMP_STR(name, "tRFC1min")) {
            tmp /= MTB;
            ddr4->tRFC1_min_mtb = tmp;
            printf("Normal Refresh Recovery Delay Time (tRFC1 min):\t\t%u ps\ttRFC1_min_mtb = %u\n", value, ddr4->tRFC1_min_mtb);
        } else if (SNPS_COMP_STR(name, "tRFC2min")) {
            tmp /= MTB;
            ddr4->tRFC2_min_mtb = tmp;
            printf("2x mode Refresh Recovery Delay Time (tRFC2 min):\t%u ps\ttRFC2_min_mtb = %u\n", value, ddr4->tRFC2_min_mtb);
        } else if (SNPS_COMP_STR(name, "tRFC4min")) {
            tmp /= MTB;
            ddr4->tRFC4_min_mtb = tmp;
            printf("4x mode Refresh Recovery Delay Time (tRFC4 min):\t%u ps\ttRFC4_min_mtb = %u\n", value, ddr4->tRFC4_min_mtb);
        } else if (SNPS_COMP_STR(name, "tRRD_S_min")) {
            reverse_calculation(value, &ddr4->tRRD_S_min_mtb, &ddr4->tRRD_S_min_ftb);
            printf("Short Row Active to Row Active Delay (tRRD_S min):\t%u ps\t\ttRRD_S_min_mtb = %u\ttRRD_S_min_ftb = %d\n", value, ddr4->tRRD_S_min_mtb, ddr4->tRRD_S_min_ftb);
        } else if (SNPS_COMP_STR(name, "tRRD_L_min")) {
            reverse_calculation(value, &ddr4->tRRD_L_min_mtb, &ddr4->tRRD_L_min_ftb);
            printf("Long Row Active to Row Active Delay (tRRD_L min):\t%u ps\t\ttRRD_L_min_mtb = %u\ttRRD_L_min_ftb = %d\n", value, ddr4->tRRD_L_min_mtb, ddr4->tRRD_L_min_ftb);
        } else if (SNPS_COMP_STR(name, "tWRmin"))  {
            tmp /= MTB;
            ddr4->tWR_min_mtb_msb = (tmp & 0x00000f00) >> 8;
            ddr4->tWR_min_mtb_lsb = tmp & 0x000000ff;
            printf("Write Recovery Time (tWR min):\t\t\t\t%u ps\ttWR_min_mtb = %u\n", value, (ddr4->tWR_min_mtb_msb << 8) | ddr4->tWR_min_mtb_lsb);
        } else if (SNPS_COMP_STR(name, "tWTR_S_min")) {
            tmp /= MTB;
            ddr4->tWTR_L_min_tWTR_S_min_mtb_msb &= ~0x0f;
            ddr4->tWTR_L_min_tWTR_S_min_mtb_msb |= (tmp & 0x00000f00) >> 8;
            ddr4->tWTR_S_min_mtb_lsb = tmp & 0x000000ff;
            printf("Short Write to Read Command Delay (tWTR_S min):\t\t%u ps\t\ttWTR_S_min_mtb = %u\n", value, ((ddr4->tWTR_L_min_tWTR_S_min_mtb_msb & 0x0f) << 8) | ddr4->tWTR_S_min_mtb_lsb);
        } else if (SNPS_COMP_STR(name, "tWTR_L_min")) {
            tmp /= MTB;
            ddr4->tWTR_L_min_tWTR_S_min_mtb_msb &= ~0xf0;
            ddr4->tWTR_L_min_tWTR_S_min_mtb_msb |= (tmp & 0x00000f00) >> 4;
            ddr4->tWTR_L_min_mtb_lsb = tmp & 0x000000ff;
            printf("Long Write to Read Command Delay (tWTR_L min):\t\t%u ps\t\ttWTR_L_min_mtb = %u\n", value, ((ddr4->tWTR_L_min_tWTR_S_min_mtb_msb & 0xf0) << 4) | ddr4->tWTR_L_min_mtb_lsb);
        } else if (SNPS_COMP_STR(name, "tCCD_L_min")) {
            reverse_calculation(value, &ddr4->tCCD_L_min_mtb, &ddr4->tCCD_L_min_ftb);
            printf("Long CAS to CAS Delay Time (tCCD_L min):\t\t%u ps\t\ttCCD_L_min_mtb = %u\ttCCD_L_min_ftb = %d\n", value, ddr4->tCCD_L_min_mtb, ddr4->tCCD_L_min_ftb);
        } else if (SNPS_COMP_STR(name, "tFAWmin")) {
            tmp /= MTB;
            ddr4->tFAW_min_mtb_msb = (tmp & 0x00000f00) >> 8;
            ddr4->tFAW_min_mtb_lsb = tmp & 0x000000ff;
            printf("Four Active Windows Delay (tFAW min):\t\t\t%u ps\ttFAW_min_mtb = %u\n", value, (ddr4->tFAW_min_mtb_msb << 8) | ddr4->tFAW_min_mtb_lsb);
        } else {
            printf("Invalid tag %s\n", name);
            rtrn = false;
            goto close_and_return;
        }
    }

close_and_return:
    fclose(spd_ini_file);
    return rtrn;
}
