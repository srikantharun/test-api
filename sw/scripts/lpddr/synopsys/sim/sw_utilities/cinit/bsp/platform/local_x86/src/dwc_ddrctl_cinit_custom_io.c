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
#include "dwc_cinit_log.h"
#include "ddrctl_regmap.h"

static FILE * i2c;


void dwc_ddrctl_cinit_custom_io_write32(uint64_t address, uint32_t data)
{
    ddrctl_error_t rslt;

    rslt = ddrctl_regmap_write(address, data);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Register write: 0x%08x = 0x%08x (error %d)", address, data, rslt);
    }
}


uint32_t dwc_ddrctl_cinit_custom_io_read32(uint64_t address)
{
    ddrctl_error_t  rslt;
    uint32_t        data;

    rslt = ddrctl_regmap_read(address, &data);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Register read: 0x%08x (error %d)", address, rslt);
        return 0;
    }
    return data;
}


void dwc_ddrctl_cinit_custom_io_secure_write32(uint64_t address, uint32_t data)
{
    dwc_ddrctl_cinit_custom_io_write32(address, data);
}

uint32_t dwc_ddrctl_cinit_custom_io_secure_read32(uint64_t address)
{
    return dwc_ddrctl_cinit_custom_io_read32(address);
}

void dwc_ddrctl_cinit_custom_io_power(bool enable)
{
    CINIT_UNUSED(enable);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_presetn(bool enable)
{
    if (enable == false) {
        ddrctl_regmap_reset();
    }
}

void dwc_ddrctl_cinit_custom_io_aresetn(bool enable)
{
    CINIT_UNUSED(enable);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_ddrc_rstn(bool enable)
{
    CINIT_UNUSED(enable);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_wait_pclk(uint32_t cycles)
{
    CINIT_UNUSED(cycles);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_wait_ddrc_clk(uint32_t cycles)
{
    CINIT_UNUSED(cycles);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_set_pclk(bool enable)
{
    CINIT_UNUSED(enable);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_set_axi_clk(bool enable)
{
    CINIT_UNUSED(enable);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_set_ddrc_clk(bool enable)
{
    CINIT_UNUSED(enable);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_usleep(uint32_t time)
{
    CINIT_UNUSED(time);
    /*
     * This section is reserved for customer adaptation for its platform
     */
}

void dwc_ddrctl_cinit_custom_io_nsleep(uint32_t time)
{
    CINIT_UNUSED(time);
    /*
     * This section is reserved for customer adaptation for its platform
     */
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


    if (!i2c) {

        return false;
    }

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
    CINIT_UNUSED(target_freq_num);
}

void dwc_ddrctl_cinit_custom_io_block_appl(bool block)
{
	CINIT_UNUSED(block);
}

void dwc_ddrctl_cinit_custom_io_training_chk_enable(uint32_t en)
{
	CINIT_UNUSED(en);

}

bool dwc_ddrctl_cinit_custom_io_smbus_write(uint16_t ch, uint32_t msg, uint32_t smbus_info)

{
	CINIT_UNUSED(ch);
	CINIT_UNUSED(msg);
	CINIT_UNUSED(smbus_info);
	/*
	 * This section is reserved for customer adaptation for its platform
	 */
	return true;
}

void ddrctl_user_custom_set_io_ctrl(uint8_t channel, ddrctl_io_t io_pin,
                                    ddrctl_status_t status)
{
    SNPS_INFO("IO control %s = %s (report only)",
              ddrctl_io_to_str(io_pin), ddrctl_status_to_str(status));
}
