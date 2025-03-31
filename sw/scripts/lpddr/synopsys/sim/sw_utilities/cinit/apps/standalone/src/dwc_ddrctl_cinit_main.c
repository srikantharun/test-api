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
#include "dwc_cinit_log.h"
#include "dwc_ddrctl_cinit_convert_config.h"
#include "ddrctl_regmap.h"
#include <getopt.h>
#include <errno.h>
#include <time.h>

#define DWC_CINIT_USE_ARB_TCK

typedef struct standalone_cfg_e {
    ddrctl_bool_t defconfig_create;
    ddrctl_bool_t phy_setup;
} standalone_cfg_t;

SubsysHdlr_t cinit_cfg;

/**
 * This test is to compile CINIT standalone and to generate an executable.
 *
 * NB this test can only be compiled in the workspace
 *
 * The flow is setup a configuration in SPD initialize
 * all the registers to reset values get and run-time options setup the
 * address map calculate JEDEC timings
 */


/**
 * @brief Main function only used in STD_ALONE mode when an executable is
 * created
 */
void cinit_standalone(standalone_cfg_t *stand_cfg)
{
    memset(&cinit_cfg, 0, sizeof(SubsysHdlr_t));
    hdlr = &cinit_cfg;

    dwc_ddrctl_cinit_begin(hdlr);

    if (DDRCTL_TRUE == stand_cfg->defconfig_create) {
        SNPS_LOG("Create defconfig file");
        ddr_bsp_log_file_create(SNPS_DEFCONFIG_LOG);
        dwc_ddrctl_cinit_convert_config();
        dwc_ddrctl_cinit_convert_params(hdlr);
        ddr_bsp_log_file_close(SNPS_DEFCONFIG_LOG);
    }

    dwc_cinit_set_operational_clk_period(hdlr);

    SNPS_LOG("Initialize the controller registers");
    dwc_ddrctl_cinit_main(hdlr);

    if (DDRCTL_TRUE == stand_cfg->phy_setup) {
        SNPS_LOG("Phy init configuration:");
        dwc_cinit_phyinit_setuserinput(hdlr);
    }

    dwc_ddrctl_cinit_end();
}


static void print_usage(char *program)
{
    printf("Usage: %s [OPTIONS]\n", program);
    printf("\t-d,  --defconfig_create       create a defconfig based on the configuration (for debug only)\n");
    printf("\t-p,  --phy_setup              run PHY init\n");
    printf("\t-h,  --help                   this help\n");
}


int main(int argc, char *argv[])
{
    int option;
    int option_index = 0;
    standalone_cfg_t stand_cfg = {DDRCTL_FALSE, DDRCTL_FALSE};
    ddrctl_error_t rslt;
    uint32_t value = 0;
    uint32_t addr  = 0;
    uint32_t count = 0;
    char     *endptr = NULL;

    static struct option long_options[] = {
            {"defconfig_create", no_argument,  0, 'd'},
            {"phy_setup",        no_argument,  0, 'p'},
            {"read",             required_argument,  0, 'r'},
            {"write",            required_argument,  0, 'w'},
            {"help",             no_argument,  0, 'h'},
            {NULL, 0, NULL, 0}
    };

    while ((option = getopt_long(argc, argv, "dphr:w:m",
            long_options, &option_index)) != -1) {
        switch(option) {
            case 'd':
                stand_cfg.defconfig_create = DDRCTL_TRUE;
                break;
            case 'p':
                stand_cfg.phy_setup = DDRCTL_TRUE;
                break;
            case 'r':
                errno = 0;
                addr = strtol(optarg, &endptr, 0);
                if (0 == errno && (*endptr == 0)) {
                    rslt = ddrctl_regmap_read(addr, &value);
                } else {
                    rslt = ddrctl_regmap_read_field_by_fullname(optarg, &value);
                }

                if (DDRCTL_SUCCESS != rslt) {
                    printf("Read failed of \"%s\" (%d)\n", optarg, rslt);
                    return EXIT_FAILURE;
                }

                printf("Read %s = 0x%x\n", optarg, value);
                return EXIT_SUCCESS;
            case 'w':
                errno = 0;
                value = 0xFF00FF;
                addr = strtol(optarg, &endptr, 0);
                if (0 == errno && (*endptr == 0)) {
                    rslt = ddrctl_regmap_write(addr, value);
                    ddrctl_regmap_read(addr, &value);
                } else {
                    rslt = ddrctl_regmap_write_field_by_fullname(optarg, value);
                    ddrctl_regmap_read_field_by_fullname(optarg, &value);
                }

                if (DDRCTL_SUCCESS != rslt) {
                    printf("Write failed of \"%s\" (%d)\n", optarg, rslt);
                    return EXIT_FAILURE;
                }

                printf("Writed %s = 0x%x\n", optarg, value);
                return EXIT_SUCCESS;
            case 'h':
                print_usage(argv[0]);
                exit(EXIT_SUCCESS);
                break;
            default:
                printf ("Invalid parameter \"%c\"\n", option);
                print_usage(argv[0]);
                return EXIT_FAILURE;
        }
    }

    cinit_standalone(&stand_cfg);

    return EXIT_SUCCESS;
}
