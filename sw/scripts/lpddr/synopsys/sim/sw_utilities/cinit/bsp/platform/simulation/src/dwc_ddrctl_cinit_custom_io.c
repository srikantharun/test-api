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


#include "dwc_cinit_io.h"
#include "dwc_cinit_platform.h"
#include "dwc_cinit_log.h"
#include "ddrctl_regmap.h"

static FILE * i2c;


void dwc_ddrctl_cinit_custom_io_write32(uint64_t address, uint32_t data)
{
    ddrctl_error_t  rslt;
    uint32_t        status = 0;

    // Store register in internal regmap
    rslt = ddrctl_regmap_write(address, data);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_WARN("Internal register write failed %d", rslt);
    }

    ddrctl_sim_is_reg_access_enable(&status);
    if (status != 0)  {
        dwc_ddrctl_cinit_sim_io_write32(address, data);
    }
}


uint32_t dwc_ddrctl_cinit_custom_io_read32(uint64_t address)
{
    ddrctl_error_t  rslt;
    uint32_t        data   = 0;
    uint32_t        status = 0;

    ddrctl_sim_is_reg_access_enable(&status);
    if (status != 0)  {
        dwc_ddrctl_cinit_sim_io_read32(address, &data);
    } else {
        // Read register from internal regmap
        rslt = ddrctl_regmap_read(address, &data);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_WARN("Internal register read failed %d", rslt);
        }
    }
    return data;
}


void dwc_ddrctl_cinit_custom_io_secure_write32(uint64_t address, uint32_t data)
{
    ddrctl_error_t  rslt;
    uint32_t        status = 0;

    // Store register in internal regmap
    rslt = ddrctl_regmap_write(address, data);
    if (rslt != DDRCTL_SUCCESS) {
        SNPS_WARN("Internal register write failed %d", rslt);
    }

    ddrctl_sim_is_reg_access_enable(&status);
    if (status != 0)  {
        dwc_ddrctl_cinit_sim_io_secure_write32(address, data);
    }
}


uint32_t dwc_ddrctl_cinit_custom_io_secure_read32(uint64_t address)
{
    ddrctl_error_t  rslt;
    uint32_t        data   = 0;
    uint32_t        status = 0;

    ddrctl_sim_is_reg_access_enable(&status);
    if (status != 0)  {
        dwc_ddrctl_cinit_sim_io_secure_read32(address, &data);
    } else {
        // Read register from internal regmap
        rslt = ddrctl_regmap_read(address, &data);
        if (rslt != DDRCTL_SUCCESS) {
            SNPS_WARN("Internal register read failed %d", rslt);
        }
    }

    return data;
}


void dwc_ddrctl_cinit_custom_io_power(bool enable)
{
    dwc_ddrctl_cinit_sim_io_power((uint32_t)enable);
}

void dwc_ddrctl_cinit_custom_io_presetn(bool enable)
{
    if (enable == false) {
        ddrctl_regmap_reset();
    }

    dwc_ddrctl_cinit_sim_io_presetn((uint32_t)enable);
}

void dwc_ddrctl_cinit_custom_io_aresetn(bool enable)
{
    dwc_ddrctl_cinit_sim_io_aresetn((uint32_t)enable);
}

void dwc_ddrctl_cinit_custom_io_ddrc_rstn(bool enable)
{
    dwc_ddrctl_cinit_sim_io_ddrc_rstn((uint32_t)enable);
}

void dwc_ddrctl_cinit_custom_io_wait_pclk(uint32_t cycles)
{
    dwc_ddrctl_cinit_sim_io_wait_pclk(cycles);
}

void dwc_ddrctl_cinit_custom_io_wait_ddrc_clk(uint32_t cycles)
{
    dwc_ddrctl_cinit_sim_io_wait_ddrc_clk(cycles);
}

void dwc_ddrctl_cinit_custom_io_set_pclk(bool enable)
{
    dwc_ddrctl_cinit_sim_io_set_pclk((uint32_t)enable);
}

void dwc_ddrctl_cinit_custom_io_set_axi_clk(bool enable)
{
    dwc_ddrctl_cinit_sim_io_set_axi_clk((uint32_t)enable);
}

void dwc_ddrctl_cinit_custom_io_set_ddrc_clk(bool enable)
{
    dwc_ddrctl_cinit_sim_io_set_ddrc_clk((uint32_t)enable);
}

void dwc_ddrctl_cinit_custom_io_usleep(uint32_t time)
{
    dwc_ddrctl_cinit_sim_io_usleep(time);
}

void dwc_ddrctl_cinit_custom_io_nsleep(uint32_t time)
{
    dwc_ddrctl_cinit_sim_io_nsleep(time);
}

bool dwc_ddrctl_cinit_custom_io_i2c_config(void)
{
    return true;
}

bool dwc_ddrctl_cinit_custom_io_i2c_enable(void)
{
    if (i2c)
        return true;

    i2c = fopen("./SPD.bin", "rb");

    if (!i2c)
        return false;

    return true;
}

bool dwc_ddrctl_cinit_custom_io_i2c_disable(void)
{
    if (!i2c)
        return true;

    if (!fclose(i2c)) {
        i2c = NULL;
    }

    return true;
}

bool dwc_ddrctl_cinit_custom_io_i2c_read(uint16_t address, uint8_t *data, uint16_t bytes)
{
    if (!i2c)
        return false;

    if (fseek(i2c, address, SEEK_SET))
        return false;

    if (fread(data, 1, bytes, i2c) == bytes)
        return true;
    else
        return false;
}

/** @brief custom method used when switching clock frequencies */
void dwc_ddrctl_cinit_custom_io_switch_clk(uint32_t target_freq_num)
{
    dwc_ddrctl_cinit_sim_io_switch_clk(target_freq_num);
}


/** @brief Signal to the simulation to disable VIP checkers during training
 * * @note This may not be possible in all customer implementations.
 * dwc_ddrctl_cinit_sim_io_training_chk_enable must be DPI method exported by the
 * testbench.
 */
void dwc_ddrctl_cinit_custom_io_training_chk_enable(uint32_t en)
{
	dwc_ddrctl_cinit_sim_io_training_chk_enable(en);

}

bool dwc_ddrctl_cinit_custom_io_smbus_write(uint16_t ch, uint32_t msg, uint32_t smbus_info)
{
	dwc_ddrctl_cinit_custom_sim_io_smbus_write(ch, msg, smbus_info);
	return true;
}

void ddrctl_user_custom_set_io_ctrl(uint8_t channel, ddrctl_io_t io_pin,
                                    ddrctl_status_t status)
{
    SNPS_INFO("IO control %s = %s", ddrctl_io_to_str(io_pin),
                                    ddrctl_status_to_str(status));

    switch (io_pin) {
        case DDRCTL_IO_IME_CFG_LOCK:
            dwc_ddrctl_cinit_sim_io_set_ime_cfg_lock((uint16_t) channel, (uint32_t) status);
            break;
        case DDRCTL_IO_IME_CFG_KEY_LOCK:
            dwc_ddrctl_cinit_sim_io_set_ime_cfg_key_lock((uint16_t) channel, (uint32_t) status);
            break;
        default:
            SNPS_WARN("IO pin %d not supported", io_pin);
    }
}


