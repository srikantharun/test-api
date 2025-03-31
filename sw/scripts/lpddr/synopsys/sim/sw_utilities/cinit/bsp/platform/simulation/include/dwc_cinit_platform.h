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


#ifndef CINIT_BSP_PLATFORM_SIMULATION_DWC_CINIT_PLATFORM_H_
#define CINIT_BSP_PLATFORM_SIMULATION_DWC_CINIT_PLATFORM_H_

#include "dwc_cinit_types.h"

#define ABORT_SIMULATION(str) abort_simulation(str)

// imported DPI function to exit the simulation gracefully.
extern void abort_simulation(char *msg);

extern void ddrctl_sim_is_reg_access_enable(unsigned int *data);

extern void dwc_ddrctl_cinit_sim_io_write32(unsigned int address, unsigned int data);
extern void dwc_ddrctl_cinit_sim_io_read32(unsigned int address, unsigned int *data);

extern void dwc_ddrctl_cinit_sim_io_secure_write32(unsigned int address, unsigned int data);
extern void dwc_ddrctl_cinit_sim_io_secure_read32(unsigned int address, unsigned int *data);


extern void dwc_ddrctl_cinit_sim_io_power(unsigned int enable);
extern void dwc_ddrctl_cinit_sim_io_presetn(unsigned int enable);
extern void dwc_ddrctl_cinit_sim_io_aresetn(unsigned int enable);
extern void dwc_ddrctl_cinit_sim_io_ddrc_rstn(unsigned int enable);
extern void dwc_ddrctl_cinit_sim_io_wait_pclk(unsigned int cycles);
extern void dwc_ddrctl_cinit_sim_io_wait_ddrc_clk(unsigned int cycles);
extern void dwc_ddrctl_cinit_sim_io_set_pclk(unsigned int enable);
extern void dwc_ddrctl_cinit_sim_io_set_axi_clk(unsigned int enable);
extern void dwc_ddrctl_cinit_sim_io_set_ddrc_clk(unsigned int enable);
extern void dwc_ddrctl_cinit_sim_io_nsleep(unsigned int sleep_ns);
extern void dwc_ddrctl_cinit_sim_io_usleep(unsigned int sleep_us);
extern void dwc_ddrctl_cinit_sim_io_send_wr_rd(void);
extern void dwc_ddrctl_cinit_sim_io_switch_clk(unsigned int target_freq_num);

extern void dwc_ddrctl_cinit_sim_io_training_chk_enable(uint32_t en);

extern void dwc_ddrctl_cinit_custom_sim_io_smbus_write (int p_ch, int p_msg, int p_smbus_info);
extern void dwc_ddrctl_cinit_sim_io_set_ime_cfg_lock(uint16_t ch, uint32_t value);
extern void dwc_ddrctl_cinit_sim_io_set_ime_cfg_key_lock(uint16_t ch, uint32_t value);

#endif /* CINIT_BSP_PLATFORM_SIMULATION_DWC_CINIT_PLATFORM_H_ */
