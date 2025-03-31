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


#include "spd_ddr5.h"
#include "spd_utils.h"

static bool parser_conf_file_ddr5(char * spd_ini_path, spd_ddr5_t *ddr5);

int core_ddr5(app_options_t *options)
{
    spd_ddr5_t ddr5;
    FILE * spd_bin_file;
    bool rtrn;


    if (NULL == options) {
        return EXIT_FAILURE;
    }

    if ((NULL == options->spd_ini_path) || (NULL == options->spd_bin_path)) {
        return EXIT_FAILURE;
    }

    memset(&ddr5, '\0', sizeof(ddr5));

    ddr5.bytes_total_used = 0x30;                       /* 000 */
    ddr5.revision = 0x09;                               /* 001 */
    ddr5.kb_dram_device_type = 0x12;                    /* 002 */
    ddr5.kb_module_type = 0x01;                         /* 003 */
    ddr5.sdram_density_package = 0x04;                  /* 004 */
    ddr5.sdram_addressing = 0x20;                       /* 005 */
    ddr5.sdram_width = 0x00;                            /* 006 */
    ddr5.sdram_bkg_bpbg = 0x62;                         /* 007 */
    ddr5.second_sdram_density_package = 0x00;           /* 008 */
    ddr5.second_sdram_addressing = 0x00;                /* 009 */
    ddr5.second_sdram_width = 0x00;                     /* 010 */
    ddr5.second_sdram_bkg_bpbg = 0x00;                  /* 011 */
    ddr5.sdram_bl32_ppr = 0x10;                         /* 012 */
    ddr5.sdram_duty_cycle = 0x02;                       /* 013 */
    ddr5.fault_handling = 0x05;                         /* 014 */
                                                        /* 015 */
    ddr5.vdd = 0x00;                                    /* 016 */
    ddr5.vddq = 0x00;                                   /* 017 */
    ddr5.vpp = 0x00;                                    /* 018 */
                                                        /* 019 */
    ddr5.tCKAVGmin = 0x0165;                            /* 020 ~ 021 */
    ddr5.tCKAVGmax = 0x03f2;                            /* 022 ~ 023 */
    ddr5.CASlatency_byte0 = 0x7a;                       /* 024 */
    ddr5.CASlatency_byte1 = 0xad;                       /* 025 */
    ddr5.CASlatency_byte2 = 0x00;                       /* 026 */
    ddr5.CASlatency_byte3 = 0x00;                       /* 027 */
    ddr5.CASlatency_byte4 = 0x00;                       /* 028 */
                                                        /* 029 */
    ddr5.tAAmin = 0x3e80;                               /* 030 ~ 031 */
    ddr5.tRCDmin = 0x3e80;                              /* 032 ~ 033 */
    ddr5.tRPmin = 0x3e80;                               /* 034 ~ 035 */
    ddr5.tRASmin = 0x7d00;                              /* 036 ~ 037 */
    ddr5.tRCmin = 0xbb80;                               /* 038 ~ 039 */
    ddr5.tWRmin = 0x7530;                               /* 040 ~ 041 */
    ddr5.tRFC1_slr_min = 0x0127;                        /* 042 ~ 043 */
    ddr5.tRFC2_slr_min = 0x00a0;                        /* 044 ~ 045 */
    ddr5.tRFCsb_slr_min = 0x0082;                       /* 046 ~ 047 */
    ddr5.tRFC1_dlr_min = 0x0000;                        /* 048 ~ 049 */
    ddr5.tRFC2_dlr_min = 0x0000;                        /* 050 ~ 051 */
    ddr5.tRFCsb_dlr_min = 0x0000;                       /* 052 ~ 053 */
    ddr5.sdram_refresh_mgnt = 0x0000;                   /* 054 ~ 055 */
    ddr5.second_sdram_refresh_mgt = 0x0000;             /* 056 ~ 057 */
    ddr5.sdram_adapt_A_refresh = 0x0000;                /* 058 ~ 059 */
    ddr5.second_sdram_adapt_A_refresh = 0x0000;         /* 060 ~ 061 */
    ddr5.sdram_adapt_B_refresh = 0x0000;                /* 062 ~ 063 */
    ddr5.second_sdram_adapt_B_refresh = 0x0000;         /* 064 ~ 065 */
    ddr5.sdram_adapt_C_refresh = 0x0000;                /* 066 ~ 067 */
    ddr5.second_sdram_adapt_C_refresh = 0x0000;         /* 068 ~ 069 */
                                                        /* 070 ~ 191 */

    ddr5.second_sdram_adapt_C_refresh_lsb = 0x1B;
    ddr5.second_sdram_adapt_C_refresh_msb = 0x2B;

    rtrn = parser_conf_file_ddr5(options->spd_ini_path, &ddr5);
    if (false == rtrn) {
        return EXIT_FAILURE;
    }

    ddr5.crc = crc16_calc((uint8_t *)&ddr5, (uint8_t *)&ddr5.crc - (uint8_t *)&ddr5); /* 126 ~ 127 */

    if (print_and_validate_ddr5_spd(&ddr5) > 0) {
        return EXIT_FAILURE;
    }

    spd_bin_file = fopen(options->spd_bin_path, "w");
    if (NULL == spd_bin_file) {
        perror("SPD bin file open error: ");
        return EXIT_SUCCESS;
    }

    fwrite(&ddr5, sizeof(ddr5), 1, spd_bin_file);

    printf("ddr5 Binary SPD dump file = %lu bytes\n", sizeof(ddr5));

    fclose(spd_bin_file);

    return EXIT_SUCCESS;
}


static bool parser_conf_file_ddr5(char * spd_ini_path, spd_ddr5_t *ddr5)
{
    uint64_t    value;
    char name[30];
    char        value_str[30];
    FILE * spd_ini_file;
    bool rtrn = true;

    spd_ini_file = fopen(spd_ini_path, "r");
    if (NULL == spd_ini_file) {
        fprintf(stderr, "SPD ini file (%s) open failed: %s\n", spd_ini_path, strerror(errno));
        return false;
    }

    while (fscanf(spd_ini_file, "%s %s", name, value_str) == 2) {
        value = strtoll(value_str, NULL, 0);

        if (SNPS_COMP_STR(name, "type")) {
            SNPS_WRITE_FIELD(ddr5->kb_module_type, 0, 0x1F, value);
        } else if (SNPS_COMP_STR(name, "first_capacity")) {
            SNPS_WRITE_FIELD(ddr5->sdram_density_package, 0, 0x1F, value);
        } else if (SNPS_COMP_STR(name, "second_capacity")) {
            SNPS_WRITE_FIELD(ddr5->second_sdram_density_package, 0, 0x1F, value);
        } else if (SNPS_COMP_STR(name, "first_banks")) {
            SNPS_WRITE_FIELD(ddr5->sdram_bkg_bpbg, 0, 0x07, value);
        } else if (SNPS_COMP_STR(name, "second_banks")) {
            SNPS_WRITE_FIELD(ddr5->second_sdram_bkg_bpbg, 0, 0x07, value);
        } else if (SNPS_COMP_STR(name, "first_col_address")) {
            SNPS_WRITE_FIELD(ddr5->sdram_addressing, 5, 0xE0, value);
        } else if (SNPS_COMP_STR(name, "second_col_address")) {
            SNPS_WRITE_FIELD(ddr5->second_sdram_addressing, 5, 0xE0, value);
        } else if (SNPS_COMP_STR(name, "first_row_address")) {
            SNPS_WRITE_FIELD(ddr5->sdram_addressing, 0, 0x1F, value);
        } else if (SNPS_COMP_STR(name, "second_row_address")) {
            SNPS_WRITE_FIELD(ddr5->second_sdram_addressing, 0, 0x1F, value);
        } else if (SNPS_COMP_STR(name, "first_bank_group")) {
            SNPS_WRITE_FIELD(ddr5->sdram_bkg_bpbg, 5, 0xE0, value);
        } else if (SNPS_COMP_STR(name, "second_bank_group")) {
            SNPS_WRITE_FIELD(ddr5->second_sdram_bkg_bpbg, 5, 0xE0, value);
        } else if (SNPS_COMP_STR(name, "first_device_width")) {
            SNPS_WRITE_FIELD(ddr5->sdram_width, 5, 0xF0, value);
        } else if (SNPS_COMP_STR(name, "second_device_width")) {
            SNPS_WRITE_FIELD(ddr5->second_sdram_width, 5, 0xF0, value);
        } else if (SNPS_COMP_STR(name, "CL_supported")) {
            ddr5->CASlatency_byte0 = value & 0xFF;
            ddr5->CASlatency_byte1 = (value >>  8) & 0xFF;
            ddr5->CASlatency_byte2 = (value >> 16) & 0xFF;
            ddr5->CASlatency_byte3 = (value >> 24) & 0xFF;
            ddr5->CASlatency_byte4 = (value >> 32) & 0xFF;
        } else if (SNPS_COMP_STR(name, "tCKAVGmin")) {
            ddr5->tCKAVGmin = value;
        } else if (SNPS_COMP_STR(name, "tCKAVGmax")) {
            ddr5->tCKAVGmax = value;
        } else if (SNPS_COMP_STR(name, "tAAmin")) {
            ddr5->tAAmin = value;
        } else if (SNPS_COMP_STR(name, "tRCDmin")) {
            ddr5->tRCDmin = value;
        } else if (SNPS_COMP_STR(name, "tRPmin")) {
            ddr5->tRPmin = value;
        } else if (SNPS_COMP_STR(name, "tRASmin")) {
            ddr5->tRASmin = value;
        } else if (SNPS_COMP_STR(name, "tRCmin")) {
            ddr5->tRCmin = value;
        } else if (SNPS_COMP_STR(name, "tRFC1_slr_min")) {
            ddr5->tRFC1_slr_min = value;
        } else if (SNPS_COMP_STR(name, "tRFC2_slr_min")) {
            ddr5->tRFC2_slr_min = value;
        } else if (SNPS_COMP_STR(name, "tRFCsb_slr_min")) {
            ddr5->tRFCsb_slr_min = value;
        } else if (SNPS_COMP_STR(name, "tRFC1_dlr_min")) {
            ddr5->tRFC1_dlr_min = value;
        } else if (SNPS_COMP_STR(name, "tRFC2_dlr_min")) {
            ddr5->tRFC2_dlr_min = value;
        } else if (SNPS_COMP_STR(name, "tRFCsb_dlr_min")) {
            ddr5->tRFCsb_dlr_min = value;
        } else if (SNPS_COMP_STR(name, "tWRmin"))  {
            ddr5->tWRmin = value;
        } else if (SNPS_COMP_STR(name, "number_package_ranks_channel"))  {
            if (0 == value) {
                printf("Invalid number of package ranks channel 0, supported 1-8\n");
                rtrn = false;
                goto close_and_return;
            }
            SNPS_WRITE_FIELD(ddr5->module_organization, 3, 0x38, value - 1);
        } else if (SNPS_COMP_STR(name, "primary_bus_width"))  {
            SNPS_WRITE_FIELD(ddr5->memory_channel_bus_width, 0, 0x07, value);
        } else if (SNPS_COMP_STR(name, "bus_width_extension"))  {
            SNPS_WRITE_FIELD(ddr5->memory_channel_bus_width, 3, 0x18, value);
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


uint16_t print_and_validate_ddr5_spd(spd_ddr5_t *ddr5)
{
    uint64_t    value;
    uint64_t    tmp;
    uint16_t    err_count = 0;

    printf("DDR5 SDRAM\n");

    switch (SNPS_READ_FIELD(ddr5->kb_module_type, 0, 0x1F)) {
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
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->sdram_density_package, 0, 0x1F)) {
        case 1:
            printf("First Module Capacity = 4 Gb\n");
            break;
        case 2:
            printf("First Module Capacity = 8 Gb\n");
            break;
        case 3:
            printf("First Module Capacity = 12 Gb\n");
            break;
        case 4:
            printf("First Module Capacity = 16 Gb\n");
            break;
        case 5:
            printf("First Module Capacity = 24 Gb\n");
            break;
        case 6:
            printf("First Module Capacity = 32 Gb\n");
            break;
        case 7:
            printf("First Module Capacity = 48 Gb\n");
            break;
        case 8:
            printf("First Module Capacity = 64 Gb\n");
            break;
        default:
            printf("Invalid First Module Capacity\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->second_sdram_density_package, 0, 0x1F)) {
        case 1:
            printf("Second Module Capacity = 4 Gb\n");
            break;
        case 2:
            printf("Second Module Capacity = 8 Gb\n");
            break;
        case 3:
            printf("Second Module Capacity = 12 Gb\n");
            break;
        case 4:
            printf("Second Module Capacity = 16 Gb\n");
            break;
        case 5:
            printf("Second Module Capacity = 24 Gb\n");
            break;
        case 6:
            printf("Second Module Capacity = 32 Gb\n");
            break;
        case 7:
            printf("Second Module Capacity = 48 Gb\n");
            break;
        case 8:
            printf("Second Module Capacity = 64 Gb\n");
            break;
        default:
            printf("Invalid Second Module Capacity\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->sdram_bkg_bpbg, 0, 0x07)) {
        case 0:
            printf("First Number of Bank Addresses = 1 banks\n");
            break;
        case 1:
            printf("First Number of Bank Addresses = 2 banks\n");
            break;
        case 2:
            printf("First Number of Bank Addresses = 3 banks\n");
            break;
        default:
            printf("Invalid First Number of Bank Addresses\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->second_sdram_bkg_bpbg, 0, 0x07)) {
        case 0:
            printf("Second Number of Bank Addresses = 1 banks\n");
            break;
        case 1:
            printf("Second Number of Bank Addresses = 2 banks\n");
            break;
        case 2:
            printf("Second Number of Bank Addresses = 3 banks\n");
            break;
        default:
            printf("Invalid Second Number of Bank Addresses\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->sdram_addressing, 5, 0xE0)) {
        case 0:
            printf("First Number of Column Addresses = 10 bits\n");
            break;
        case 1:
            printf("First Number of Column Addresses = 11 bits\n");
            break;
        default:
            printf("Invalid First Number of Column Addresses\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->second_sdram_addressing, 5, 0xE0)) {
        case 0:
            printf("Second Number of Column Addresses = 10 bits\n");
            break;
        case 1:
            printf("Second Number of Column Addresses = 11 bits\n");
            break;
        default:
            printf("Invalid Second Number of Column Addresses\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->sdram_addressing, 0, 0x1F)) {
        case 0:
            printf("First Number of Row Addresses = 16 bits\n");
            break;
        case 1:
            printf("First Number of Row Addresses = 17 bits\n");
            break;
        case 2:
            printf("First Number of Row Addresses = 18 bits\n");
            break;
        default:
            printf("Invalid First Number of Row Addresses\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->second_sdram_addressing, 0, 0x1F)) {
        case 0:
            printf("Second Number of Row Addresses = 16 bits\n");
            break;
        case 1:
            printf("Second Number of Row Addresses = 17 bits\n");
            break;
        case 2:
            printf("Second Number of Row Addresses = 18 bits\n");
            break;
        default:
            printf("Invalid Second Number of Row Addresses\n");
        err_count += 1;;
    }

    switch (SNPS_READ_FIELD(ddr5->sdram_bkg_bpbg, 5, 0xE0)) {
        case 0:
            printf("First Bank Group Addressing = 1 bank group\n");
            break;
        case 1:
            printf("First Bank Group Addressing = 2 bank group\n");
            break;
        case 2:
            printf("First Bank Group Addressing = 4 bank group\n");
            break;
        case 3:
            printf("First Bank Group Addressing = 8 bank group\n");
            break;
        default:
            printf("Invalid First Bank Group Addressing\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->second_sdram_bkg_bpbg, 5, 0xE0)) {
        case 0:
            printf("Second Bank Group Addressing = 1 bank group\n");
            break;
        case 1:
            printf("Second Bank Group Addressing = 2 bank group\n");
            break;
        case 2:
            printf("Second Bank Group Addressing = 4 bank group\n");
            break;
        case 3:
            printf("Second Bank Group Addressing = 8 bank group\n");
            break;
        default:
            printf("Invalid Second Bank Group Addressing\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->sdram_width, 5, 0xF0)) {
        case 0:
            printf("First DRAM Device Width = x4\n");
            break;
        case 1:
            printf("First DRAM Device Width = x8\n");
            break;
        case 2:
            printf("First DRAM Device Width = x16\n");
            break;
        case 3:
            printf("First DRAM Device Width = x32\n");
            break;
        default:
            printf("Invalid First DRAM Device Width\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->second_sdram_width, 5, 0xF0)) {
        case 0:
            printf("Second DRAM Device Width = x4\n");
            break;
        case 1:
            printf("Second DRAM Device Width = x8\n");
            break;
        case 2:
            printf("Second DRAM Device Width = x16\n");
            break;
        case 3:
            printf("Second DRAM Device Width = x32\n");
            break;
        default:
            printf("Invalid Second DRAM Device Width\n");
        err_count += 1;
    }

    printf("CAS Latencies Supported:");

    value = ddr5->CASlatency_byte0;
    value = value | (ddr5->CASlatency_byte1 << 8);
    value = value | (ddr5->CASlatency_byte2 << 16);
    value = value | (ddr5->CASlatency_byte3 << 24);
    value = value | (((uint64_t)ddr5->CASlatency_byte4) << 32);
    tmp = 1;
    for (uint8_t i = 20; i < 98; i+=2) {
        if (value & tmp) {
              printf(" %uT", i);
        }
        tmp = tmp << 1;
    }
    printf("\n");

    printf("Minimum Clock Cycle Time (tCK min):\t\t\t%u ps\n", ddr5->tCKAVGmin);
    printf("Maximum Clock Cycle Time (tCK max):\t\t\t%u ps\n", ddr5->tCKAVGmax);
    printf("CAS# Latency Time (tAA min):\t\t\t\t%u ps\n", ddr5->tAAmin);
    printf("RAS# to CAS# Delay Time (tRCD min):\t\t\t%u ps\n", ddr5->tRCDmin);
    printf("Row Precharge Delay Time (tRP min):\t\t\t%u ps\n", ddr5->tRPmin);
    printf("Active to Precharge Delay Time (tRAS min):\t\t%u ps\n", ddr5->tRASmin);
    printf("Act to Act/Refresh Delay Time (tRC min):\t\t%u ps\n", ddr5->tRCmin);
    printf("SDRAM Minimum Refresh Recovery Delay Time (tRFC1min, tRFC1_slr min):\t%u ns\n", ddr5->tRFC1_slr_min);
    printf("SDRAM Minimum Refresh Recovery Delay Time (tRFC2min, tRFC2_slr min):\t%u ns\n", ddr5->tRFC2_slr_min);
    printf("SDRAM Minimum Refresh Recovery Delay Time (tRFCsbmin, tRFCsb_slr min):\t%u ns\n", ddr5->tRFCsb_slr_min);
    printf("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC1_dlr min):\t%u ns\n", ddr5->tRFC1_dlr_min);
    printf("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC2_dlr min):\t%u ns\n", ddr5->tRFC2_dlr_min);
    printf("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFCsb_dlr min):\t%u ns\n", ddr5->tRFCsb_dlr_min);
    printf("Write Recovery Time (tWR min):\t\t\t\t%u ps\n", ddr5->tWRmin);

    switch (SNPS_READ_FIELD(ddr5->module_organization, 3, 0x38)) {
        case 0:
            printf("Number of Package Ranks per channel = 1 Package rank\n");
            break;
        case 1:
            printf("Number of Package Ranks per channel = 2 Package rank\n");
            break;
        case 2:
            printf("Number of Package Ranks per channel = 3 Package rank\n");
            break;
        case 3:
            printf("Number of Package Ranks per channel = 4 Package rank\n");
            break;
        case 4:
            printf("Number of Package Ranks per channel = 5 Package rank\n");
            break;
        case 5:
            printf("Number of Package Ranks per channel = 6 Package rank\n");
            break;
        case 6:
            printf("Number of Package Ranks per channel = 7 Package rank\n");
            break;
        case 7:
            printf("Number of Package Ranks per channel = 8 Package rank\n");
            break;
        default:
            printf("Invalid Number of Package Ranks per channel\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->memory_channel_bus_width, 0, 0x07)) {
        case 0:
            printf("Primary bus width per channel = 8 bits\n");
            break;
        case 1:
            printf("Primary bus width per channel = 16 bits\n");
            break;
        case 2:
            printf("Primary bus width per channel = 32 bits\n");
            break;
        case 3:
            printf("Primary bus width per channel = 64 bits\n");
            break;
        default:
            printf("Invalid Primary bus width per channel\n");
        err_count += 1;
    }

    switch (SNPS_READ_FIELD(ddr5->memory_channel_bus_width, 3, 0x18)) {
        case 0:
            printf("Bus width extension per channel = 0 bits (no extension)\n");
            break;
        case 1:
            printf("Bus width extension per channel = 4 bits (no extension)\n");
            break;
        case 2:
            printf("Bus width extension per channel = 8 bits (no extension)\n");
            break;
        default:
            printf("Invalid Bus width extension per channel\n");
        err_count += 1;
    }

    return err_count;
}
