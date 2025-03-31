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


#include "dwc_ddrctl_cinit_io.h"
#include "dwc_cinit_io.h"
#include "dwc_cinit_log.h"
#include "dwc_ddrctl_cinit_util.h"


void dwc_ddrctl_cinit_io_write32(uint64_t address, uint32_t data)
{
    dwc_ddrctl_cinit_custom_io_write32(address, data);
}

uint32_t dwc_ddrctl_cinit_io_read32(uint64_t address)
{
    uint32_t data = 0;

    data = dwc_ddrctl_cinit_custom_io_read32(address);
    SNPS_LOG("Read IO address(0x%.8x) = 0x%.8x", address, data);

    return data;
}

#ifdef DDRCTL_SECURE
void dwc_ddrctl_cinit_io_secure_write32(uint64_t address, uint32_t data)
{
    SNPS_TRACE("Entering");

    SNPS_LOG("Secure Write IO address(0x%.8x) = 0x%.8x", address, data);
    SNPS_LOG_REG_WRITE_SEQ(address, data);

    dwc_ddrctl_cinit_custom_io_secure_write32(address, data);

    SNPS_TRACE("Leaving");
}


uint32_t dwc_ddrctl_cinit_io_secure_read_field(uint64_t address, uint8_t bit_offset, uint32_t mask)
{
    return SNPS_READ_EXPLICIT_FIELD(dwc_ddrctl_cinit_io_secure_read32(address), bit_offset, mask);
}


uint32_t dwc_ddrctl_cinit_io_secure_read32(uint64_t address)
{
    SNPS_TRACE("Entering");
    uint32_t data = 0;

    data = dwc_ddrctl_cinit_custom_io_secure_read32(address);
    SNPS_LOG("Secure Read IO address(0x%.8x) = 0x%.8x", address, data);

    SNPS_TRACE("Leaving");
    return data;
}
#endif // DDRCTL_SECURE

uint32_t dwc_ddrctl_cinit_io_read_field(uint64_t address, uint8_t bit_offset, uint32_t mask)
{
    return SNPS_READ_EXPLICIT_FIELD(dwc_ddrctl_cinit_io_read32(address), bit_offset, mask);
}




void dwc_ddrctl_cinit_io_power(bool enable)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_power(enable);
    SNPS_LOG("Drive power pin %s", enable ? "high" : "low");

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_presetn(bool enable)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_presetn(enable);
    SNPS_LOG("Drive presetn pin %s", enable ? "high" : "low");

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_aresetn(bool enable)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_aresetn(enable);
    SNPS_LOG("Drive aresetn pin %s", enable ? "high" : "low");

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_ddrc_rstn(bool enable)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_ddrc_rstn(enable);
    SNPS_LOG("Drive ddrc rstn pin %s", enable ? "high" : "low");

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_wait_pclk(uint32_t cycles)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_wait_pclk(cycles);
    SNPS_LOG("Wait pclk for %u cycles", cycles);

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_wait_ddrc_clk(uint32_t cycles)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_wait_ddrc_clk(cycles);
    SNPS_LOG("Wait core clk for %u cycles", cycles);

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_set_pclk(bool enable)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_set_pclk(enable);
    SNPS_LOG("Set pclk %sable", enable ? "en" : "dis");

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_set_axi_clk(bool enable)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_set_axi_clk(enable);
    SNPS_LOG("Set axi clk %sable", enable ? "en" : "dis");

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_set_ddrc_clk(bool enable)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_set_ddrc_clk(enable);
    SNPS_LOG("Set ddr clk %sable", enable ? "en" : "dis");

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_nsleep(uint32_t time)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_nsleep(time);
    // this debug print gets prints thousands of times during PHY training, so
    // removing
    /*SNPS_LOG("nsleep for %u ns", time);*/

    SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_io_usleep(uint32_t time)
{
    SNPS_TRACE("Entering");

    dwc_ddrctl_cinit_custom_io_usleep(time);
    SNPS_LOG("usleep for %u us", time);

    SNPS_TRACE("Leaving");
}

bool dwc_ddrctl_cinit_io_i2c_config(void)
{
    SNPS_TRACE("Entering");
    bool res = false;

    res = dwc_ddrctl_cinit_custom_io_i2c_config();
    if (res)
        SNPS_LOG("i2c config", NULL);
    else
        SNPS_ERROR("Unable to config i2c", NULL);

    SNPS_TRACE("Leaving");
    return res;
}

bool dwc_ddrctl_cinit_io_i2c_enable(void)
{
    SNPS_TRACE("Entering");
    bool res = false;

    res = dwc_ddrctl_cinit_custom_io_i2c_enable();

    if (res)
        SNPS_LOG("i2c enabled", NULL);
    else
        SNPS_ERROR("Unable to enable i2c", NULL);

    SNPS_TRACE("Leaving");
    return res;
}

bool dwc_ddrctl_cinit_io_i2c_disable(void)
{
    SNPS_TRACE("Entering");
    bool res = false;

    res = dwc_ddrctl_cinit_custom_io_i2c_disable();
    if (res)
        SNPS_LOG("i2c disabled", NULL);
    else
        SNPS_ERROR("Unable to disable i2c", NULL);

    SNPS_TRACE("Leaving");
    return res;
}

bool dwc_ddrctl_cinit_io_i2c_read(uint16_t address, uint8_t *data, uint16_t bytes)
{
    bool res = false;

    res = dwc_ddrctl_cinit_custom_io_i2c_read(address, data, bytes);
    if (false == res) {
        SNPS_ERROR("Unable to read i2c address (0x%.4x)", address);
    }

    return res;
}

/** @brief Call to switch the core clock frequency
 *
 *  @param target_freq_num number of the target frequency
 */
void dwc_ddrctl_cinit_io_switch_clk(uint32_t target_freq_num)
{
    dwc_ddrctl_cinit_custom_io_switch_clk(target_freq_num);
}


/***********************************
 *  Simulation specific functions
 ***********************************/

/** @brief Enable/disable VIP checkers during traning
 * @note This may not be possible in all customer implementations.
 */
void dwc_ddrctl_cinit_io_training_chk_enable(uint32_t en)
{
	dwc_ddrctl_cinit_custom_io_training_chk_enable(en);
}

bool dwc_ddrctl_cinit_io_smbus_write(uint16_t ch, uint32_t msg, uint32_t smbus_info)
{
	SNPS_TRACE("Entering");
	bool res = false;

	res = dwc_ddrctl_cinit_custom_io_smbus_write(ch, msg, smbus_info);
	if (res) {
		SNPS_LOG("SMBus write done ch = %u, msg = 0x%.4x smbus_info = 0x%.4x",ch, msg, smbus_info);
	} else {
		SNPS_ERROR("Unable to perform dwc_ddrctl_cinit_custom_io_smbus_write",NULL);
	}

	SNPS_TRACE("Leaving");
	return res;
}


