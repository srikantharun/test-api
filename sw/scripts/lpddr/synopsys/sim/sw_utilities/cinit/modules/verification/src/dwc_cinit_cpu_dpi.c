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
#include "dwc_ddrctl_cinit_common_sequences.h"
#include "dwc_ddr_sinit_vrfy_io.h"

/**
 * @brief entry point to CPU DPI mode
 * @note the method will execute APB transactions and is time consuming
 */
void dwc_ddrphy_cinit_cpu_dpi_main(SubsysHdlr_t *phdlr, dwc_ddrctl_cinit_seq_e cinit_seq)
{
    ddrctl_error_t rslt;
    hdlr = phdlr;

    switch(cinit_seq) {
        case CINIT_SEQ_INITIALIZATION :
            dwc_cinit_setup(hdlr);
            if (dwc_ddrctl_cinit_seq_initialization() == true) {
                SNPS_LOG("Initialization completed successfully");
            } else {
                SNPS_ERROR("Initialization failed");
                dwc_ddrctl_cinit_exit(1);
            }

            dwc_ddr_sinit_vrfy_io_signal_tb(CINIT_SEND_WR_RD_TRAFFIC);

            dwc_ddrctl_cinit_io_wait_ddrc_clk(512);

            if (dwc_ddrctl_cinit_seq_wait_ctrlr_idle(5 * DWC_DDRCTL_MAX_APB_POLLING) == false) {
                SNPS_ERROR("Error in seq_wait_ctrlr_idle");
                dwc_ddrctl_cinit_exit(1);
            }
            break;
        case CINIT_SEQ_CLK_REMOVAL :
            if(dwc_ddrctl_cinit_sw_seq_clocks_disable() == false) {
                SNPS_ERROR("Clock removal failed");
                dwc_ddrctl_cinit_exit(1);
            }
            SNPS_LOG("Clock removal completed successfully");

            dwc_ddrctl_cinit_io_usleep(5);

            if(dwc_ddrctl_cinit_sw_seq_clocks_enable() == false) {
                SNPS_ERROR("Clock re-enable failed");
                dwc_ddrctl_cinit_exit(1);
            }
            SNPS_LOG("Clock re-enable completed successfully");
            break;
        case CINIT_SEQ_PWR_REMOVAL :
            dwc_ddr_sinit_vrfy_io_block_appl(true);
            if(dwc_ddrctl_cinit_sw_seq_power_disable()== false) {
                SNPS_ERROR("Power removal failed");
                dwc_ddrctl_cinit_exit(1);
            }

            SNPS_LOG("Power removal completed successfully");

            dwc_ddrctl_cinit_io_usleep(5);

            if(dwc_ddrctl_cinit_sw_seq_power_enable()== false) {
                SNPS_ERROR("Power re-enable failed");
                dwc_ddrctl_cinit_exit(1);
            }

            SNPS_LOG("Power re-enable completed successfully");
            break;
#ifdef DDRCTL_DDR
        case CINIT_SEQ_MPSM :
            if(dwc_ddrctl_cinit_sw_seq_max_power_saving_enable()== false) {
                SNPS_ERROR("MPSM enable failed");
                dwc_ddrctl_cinit_exit(1);
            }
            SNPS_LOG("MPSM enable completed successfully");

            dwc_ddrctl_cinit_io_usleep(5);

            if(dwc_ddrctl_cinit_sw_seq_max_power_saving_disable()== false) {
                SNPS_ERROR("MPSM disable failed");
                dwc_ddrctl_cinit_exit(1);
            }

            SNPS_LOG("MPSM disable completed successfully");
            break;
        case CINIT_SEQ_DDR5_FGR :
            rslt = dwc_ddrctl_cinit_sw_seq_ddr5_fgr_mode(phdlr, (ddrctl_fgr_mode_t) QDYN.fgr_mode);
            if(DDRCTL_SUCCESS != rslt) {
                SNPS_ERROR("FGR mode failed");
                dwc_ddrctl_cinit_exit(1);
            }

            SNPS_LOG("FGR mode entered in DDR5");

            dwc_ddrctl_cinit_io_usleep(5);
            break;
#endif // DDRCTL_DDR
#ifdef DDRCTL_LPDDR
        case CINIT_SEQ_LPDDR5_DSM:
            if(dwc_ddrctl_cinit_seq_enter_dsm(0,0) == false) {
                SNPS_ERROR("Enter DSM failed");
                dwc_ddrctl_cinit_exit(1);
            }
            SNPS_LOG("Enter DSM completed successfully");

            // just wait some clock cycles in DSM mode
            dwc_ddrctl_cinit_io_wait_ddrc_clk(512);
            if(dwc_ddrctl_cinit_seq_exit_dsm(0,0) == false) {
                SNPS_ERROR("Exit DSM failed");
                dwc_ddrctl_cinit_exit(1);
            }
            SNPS_LOG("Exit DSM completed successfully");
            break;
        case CINIT_SEQ_SWFFC_WITH_FSP:
            if (dwc_ddrctl_cinit_seq_swffc_with_fsp(1) == false) {
                SNPS_ERROR("Enter SWFFC with FSP failed");
                dwc_ddrctl_cinit_exit(1);
            }
            SNPS_LOG("Enter SWFFC with FSP completed successfully");
            // send some traffic at the new frequency
            dwc_ddr_sinit_vrfy_io_signal_tb(CINIT_SEND_WR_RD_TRAFFIC);
            dwc_ddrctl_cinit_io_wait_ddrc_clk(512);
            if (dwc_ddrctl_cinit_seq_wait_ctrlr_idle(5 * DWC_DDRCTL_MAX_APB_POLLING) == false) {
                SNPS_ERROR("Error in seq_wait_ctrlr_idle");
                dwc_ddrctl_cinit_exit(1);
            }
            break;
        case CINIT_SEQ_LPDDR5_RFM_LEVEL:
            if(dwc_ddrctl_cinit_sw_seq_change_rfm_level(1) == false) {
                SNPS_ERROR("LPDDR5 RFM level mode changed failed");
                dwc_ddrctl_cinit_exit(1);
            }
            SNPS_LOG("LPDDR5 RFM level mode changed");
            break;
        case CINIT_SEQ_LPDDR5_SREF_RETRAIN_PPT2:
            if( dwc_ddrctl_cinit_sw_seq_selfref_with_retrain_ppt2() == false) {
                SNPS_ERROR("LPDDR5 SREF with retraining PPT2 failed");
                dwc_ddrctl_cinit_exit(1);
            }
            SNPS_LOG("LPDDR5 SREF with retraining PPT2 passed");
            break;
#endif // DDRCTL_LPDDR
        default:
            SNPS_ERROR("Software Sequence %u not yet supported or invalid ", cinit_seq);
            break;
    }
    // In dev_init DPI hangs simulation on exit for unknown reason.
    // using a signal to tell the testbench to end the simulation
    // this is a workaround
    if (CFG->phy_training != DWC_PHY_SKIP_TRAINING)
        dwc_ddr_sinit_vrfy_io_signal_tb(CINIT_SEND_DPI_MAIN_DONE);
    return;
}

#ifdef DWC_DDRCTL_CINIT_CPU_DPI_MODE
/** @brief this method is implemented in the PVE and imported through DPI
 *  we re-define it here to avoid going back into SV world from PHYINIT.
 */
void waitFwDone_sv(void) {
    dwc_ddrctl_cinit_wait_fw_done();
}
#endif // DWC_DDRCTL_CINIT_CPU_DPI_MODE

