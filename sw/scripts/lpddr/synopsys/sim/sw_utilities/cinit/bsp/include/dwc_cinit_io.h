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


#ifndef CINIT_BSP_INCLUDE_DWC_CINIT_IO_H_
#define CINIT_BSP_INCLUDE_DWC_CINIT_IO_H_

#include "dwc_cinit_bsp.h"
#include "dwc_cinit_types.h"

void ddrctl_user_custom_set_io_ctrl(uint8_t channel, ddrctl_io_t io_pin,
                                    ddrctl_status_t status);

void dwc_ddrctl_cinit_custom_io_write32(uint64_t address, uint32_t data);
void dwc_ddrctl_cinit_custom_io_secure_write32(uint64_t address, uint32_t data);


uint32_t dwc_ddrctl_cinit_custom_io_read32(uint64_t address);
uint32_t dwc_ddrctl_cinit_custom_io_secure_read32(uint64_t address);

void dwc_ddrctl_cinit_custom_io_power(bool enable);

void dwc_ddrctl_cinit_custom_io_presetn(bool enable);
void dwc_ddrctl_cinit_custom_io_aresetn(bool enable);
void dwc_ddrctl_cinit_custom_io_ddrc_rstn(bool enable);

void dwc_ddrctl_cinit_custom_io_wait_pclk(uint32_t cycles);
void dwc_ddrctl_cinit_custom_io_wait_ddrc_clk(uint32_t cycles);

void dwc_ddrctl_cinit_custom_io_set_pclk(bool enable);
void dwc_ddrctl_cinit_custom_io_set_axi_clk(bool enable);
void dwc_ddrctl_cinit_custom_io_set_ddrc_clk(bool enable);

void dwc_ddrctl_cinit_custom_io_switch_clk(uint32_t target_freq_num);

void dwc_ddrctl_cinit_custom_io_usleep(uint32_t time);
void dwc_ddrctl_cinit_custom_io_nsleep(uint32_t time);

bool dwc_ddrctl_cinit_custom_io_i2c_config(void);
bool dwc_ddrctl_cinit_custom_io_i2c_enable(void);
bool dwc_ddrctl_cinit_custom_io_i2c_disable(void);
bool dwc_ddrctl_cinit_custom_io_i2c_read(uint16_t address, uint8_t *data, uint16_t bytes);
bool dwc_ddrctl_cinit_custom_io_smbus_write(uint16_t ch, uint32_t msg, uint32_t smbus_info);


/**
 * @brief ustom method used when switching clock frequencies
 *
 * @param target_freq_num
 */
void dwc_ddrctl_cinit_custom_io_switch_clk(uint32_t target_freq_num);

/**
 * @brief Signal to the enable/disable checkers during training
 *
 */
void dwc_ddrctl_cinit_custom_io_training_chk_enable(uint32_t en);

#endif /* CINIT_BSP_INCLUDE_DWC_CINIT_IO_H_ */
