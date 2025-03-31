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


#ifndef __DWC_DDRCTL_CINIT_IO_H__
#define __DWC_DDRCTL_CINIT_IO_H__

#include "dwc_cinit_io.h"

void dwc_ddrctl_cinit_io_write32(uint64_t address, uint32_t data);
void dwc_ddrctl_cinit_io_secure_write32(uint64_t address, uint32_t data);

uint32_t dwc_ddrctl_cinit_io_read32(uint64_t address);
uint32_t dwc_ddrctl_cinit_io_secure_read32(uint64_t address);
uint32_t dwc_ddrctl_cinit_io_read_field(uint64_t address, uint8_t bit_offset, uint32_t mask);
uint32_t dwc_ddrctl_cinit_io_secure_read_field(uint64_t address, uint8_t bit_offset, uint32_t mask);

void dwc_ddrctl_cinit_io_power(bool enable);

void dwc_ddrctl_cinit_io_presetn(bool enable);
void dwc_ddrctl_cinit_io_aresetn(bool enable);
void dwc_ddrctl_cinit_io_ddrc_rstn(bool enable);

void dwc_ddrctl_cinit_io_wait_pclk(uint32_t cycles);
void dwc_ddrctl_cinit_io_wait_ddrc_clk(uint32_t cycles);

void dwc_ddrctl_cinit_io_set_pclk(bool enable);
void dwc_ddrctl_cinit_io_set_axi_clk(bool enable);
void dwc_ddrctl_cinit_io_set_ddrc_clk(bool enable);

void dwc_ddrctl_cinit_io_nsleep(uint32_t time);
void dwc_ddrctl_cinit_io_usleep(uint32_t time);

bool dwc_ddrctl_cinit_io_i2c_config(void);
bool dwc_ddrctl_cinit_io_i2c_enable(void);
bool dwc_ddrctl_cinit_io_i2c_disable(void);
bool dwc_ddrctl_cinit_io_i2c_read(uint16_t address, uint8_t *data, uint16_t bytes);
bool dwc_ddrctl_cinit_io_smbus_write(uint16_t ch, uint32_t msg, uint32_t smbus_info);

void dwc_ddrctl_cinit_io_switch_clk(uint32_t target_freq_num);
// dwc_ddrctl_training_chk_enable method purely for simulation purposes.
// It is used to disable certain VIP checkers during PHY training.

void dwc_ddrctl_cinit_io_training_chk_enable(uint32_t en);

#endif /* __DWC_DDRCTL_CINIT_IO_H__ */
