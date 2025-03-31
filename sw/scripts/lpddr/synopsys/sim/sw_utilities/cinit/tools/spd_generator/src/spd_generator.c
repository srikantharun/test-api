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


#include <getopt.h>
#include "spd_generator.h"
#include "spd_ddr4.h"
#include "spd_ddr5.h"


void print_usage(char *program)
{
    printf("Usage: %s [OPTIONS]\n", program);
    printf("\t-v,  --verbose             enable verbose mode(disabled by default).\n");
    printf("\t-p,  --procotol            memory protocol, supported values (%d, %d)\n", DDR4_PROTOCOL, DDR5_PROTOCOL);
    printf("\t-i,  --spd_ini_file        SPD definition ini file\n");
    printf("\t-o,  --spd_bin_file        SPD binary file\n");
    printf("\t-h,  --help                this help.\n");
}


int main(int argc, char *argv[])
{
    int             option;
    int             option_index = 0;
    app_options_t   app_options = {0, 0x0, 4, NULL, NULL};

    static struct option long_options[] = {
            {"procotol",        required_argument,  0, 'p'},
            {"spd_ini_file",    required_argument,  0, 'i'},
            {"spd_bin_file",    required_argument,  0, 'o'},
            {"verbose",         no_argument,        0, 'v'},
            {"help",            no_argument,        0, 'h'},
            {NULL, 0, NULL, 0}
    };

    while ((option = getopt_long(argc, argv, "vp:i:o:h",
            long_options, &option_index)) != -1) {

        switch(option) {
            case 'i':
                if (optarg == NULL) {
                    printf ("SPD ini file missing\n");
                    goto print_help_and_exit;
                }
                app_options.spd_ini_path = optarg;
                break;
            case 'o':
                if (optarg == NULL) {
                    printf ("SPD binary output missing\n");
                    goto print_help_and_exit;
                }
                app_options.spd_bin_path = optarg;
                break;
            case 'p':
                if (optarg == NULL) {
                    printf ("Protocol value missing\n");
                    goto print_help_and_exit;
                }
                app_options.protocol = strtol(optarg, NULL, 0);
                break;
            case 'v':
                app_options.verbose = 1;
                break;
            case 'h':
                print_usage(argv[0]);
                exit(EXIT_SUCCESS);
                break;
            default:
                printf ("Invalid parameter \"%c\"\n", option);
                goto print_help_and_exit;
                break;
        }
    }

    if (NULL == app_options.spd_ini_path) {
        printf("You need to define SPD ini file, -i <spd_ini_file>\n");
        goto print_help_and_exit;
    }

    if (NULL == app_options.spd_bin_path) {
        printf("You need to define SPD output binary file, -o <spd_bin_file>\n");
        goto print_help_and_exit;
    }

    if (0 == app_options.protocol) {
        printf("You need to define the Memory  output binary file\n");
        goto print_help_and_exit;
    }

    switch (app_options.protocol) {
        case DDR4_PROTOCOL:
            if (core_ddr4(&app_options) != EXIT_SUCCESS) {
                printf("SPD DDR4 process failed\n");
                goto print_help_and_exit;
            }
            break;
        case DDR5_PROTOCOL:
            if (core_ddr5(&app_options) != EXIT_SUCCESS) {
                printf("SPD DDR5 process failed\n");
                goto print_help_and_exit;
            }
            break;
        default:
            printf("SPD protocol not supported %d\n", app_options.protocol);
            goto print_help_and_exit;
    }

    return EXIT_SUCCESS;

print_help_and_exit:
    print_usage(argv[0]);
    return EXIT_FAILURE;
}
