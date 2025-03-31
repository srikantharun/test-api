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


#ifndef __DWC_DDRCTL_CINIT_UTIL_H__
#define __DWC_DDRCTL_CINIT_UTIL_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_io.h"

#define CINIT_IS_DDR4(cfg)          ((cfg)->spdData_m.sdram_protocol == DWC_DDR4   ? DDRCTL_TRUE : DDRCTL_FALSE)
#define CINIT_IS_DDR5(cfg)          ((cfg)->spdData_m.sdram_protocol == DWC_DDR5   ? DDRCTL_TRUE : DDRCTL_FALSE)
#define CINIT_IS_LPDDR4(cfg)        ((cfg)->spdData_m.sdram_protocol == DWC_LPDDR4 ? DDRCTL_TRUE : DDRCTL_FALSE)
#define CINIT_IS_LPDDR5(cfg)        ((cfg)->spdData_m.sdram_protocol == DWC_LPDDR5 ? DDRCTL_TRUE : DDRCTL_FALSE)

#define CINIT_IS_NODIMM(cfg)        ((cfg)->spdData_m.module_type == DWC_NODIMM ? DDRCTL_TRUE : DDRCTL_FALSE)
#define CINIT_IS_UDIMM(cfg)         ((cfg)->spdData_m.module_type == DWC_UDIMM  ? DDRCTL_TRUE : DDRCTL_FALSE)
#define CINIT_IS_RDIMM(cfg)         ((cfg)->spdData_m.module_type == DWC_RDIMM  ? DDRCTL_TRUE : DDRCTL_FALSE)
#define CINIT_IS_LRDIMM(cfg)        ((cfg)->spdData_m.module_type == DWC_LRDIMM ? DDRCTL_TRUE : DDRCTL_FALSE)

// Memories package types
#define CINIT_PKG_TYPE_MONO     0
#define CINIT_PKG_TYPE_3DS_2H   1
#define CINIT_PKG_TYPE_3DS_4H   2
#define CINIT_PKG_TYPE_3DS_8H   3
#define CINIT_PKG_TYPE_3DS_16H  4

#define CINIT_GET_PKG_TYPE(cfg, n)  ((cfg)->spdData_m.cid_width[n])

#define CINIT_IS_3DS(cfg, n)        ((CINIT_GET_PKG_TYPE(cfg, n) != CINIT_PKG_TYPE_MONO) ? DDRCTL_TRUE : DDRCTL_FALSE)

#define CINIT_GET_LRANKS(cfg, n)    ((cfg)->spdData_m.cid_width[n])

#define CINIT_512MBIT     512
#define CINIT_1GBIT      1024
#define CINIT_2GBIT      2048
#define CINIT_3GBIT      3072
#define CINIT_4GBIT      4096
#define CINIT_6GBIT      6144
#define CINIT_8GBIT      8192
#define CINIT_16GBIT    16384
#define CINIT_24GBIT    24576
#define CINIT_32GBIT    32768
#define CINIT_64GBIT    65536


/**
 * @brief Macro utility to set a single bit
 * @param reg           variable to set bit
 * @param bit_offset    bit offset
 * @param val           value to set (0 / 1)
 *
 * @note: unsafe macro due to variable and mask duplication
 */
#define SNPS_SET_BIT(reg, bit_offset, val) \
    reg = (((reg) & ~(1 << (bit_offset))) | (((val) & 0x1) << (bit_offset)))

/**
 * @brief Macro utility to retrieve value of single bit
 * @param reg           value to extract bit value
 * @param bit_offset    bit offset
 */
#define SNPS_GET_BIT(reg, bit_offset) \
    (((reg) >> (bit_offset)) & 0x1)


 /**
 * @brief Macro to acess the mask of a field
 * @param field
 * @return field mask macro
 */
#define SNPS_MASK(field) field##_MASK

 /**
 * @brief Macro to acess the bit_offset of a field
 * @param field
 * @return field bit_offset macro
 */
#define SNPS_BIT_OFFSET(field) field##_BIT_OFFSET

 /**
 * @brief Macro to help read the variables fields
 *
 * @param variable
 * @param field
 * @return field value
 */
#define SNPS_READ_FIELD(reg_value, field) \
	(((reg_value) & (SNPS_MASK(field))) >> (SNPS_BIT_OFFSET(field)))

/**
 * @brief Macro to help set the variables fields
 *
 * @param variable
 * @param field
 * @param value  field value
 *
 * @note: unsafe macro due to variable and mask duplication
 */
#define SNPS_WRITE_FIELD(reg_value, field, field_value) \
    ((reg_value) = (((reg_value) & (~(SNPS_MASK(field)))) | (((field_value) << (SNPS_BIT_OFFSET(field))) & (SNPS_MASK(field)))))




/**
 * @brief Macro to help set the variables fields
 *
 * @param variable
 * @param bit_offset
 * @param value  field value
 * 
 * @note: unsafe macro due to variable
 */
#define SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(reg_value, bit_offset, field_value) \
    ((reg_value) = ((reg_value) | ((field_value) << (bit_offset))))


static inline bool dwc_ddctl_poll_bitfield(uint32_t address, uint32_t bit_offset, uint32_t mask,
                                           uint32_t expect_val, uint32_t timeout, uint32_t interval)
{
    while(SNPS_READ_EXPLICIT_FIELD(dwc_ddrctl_cinit_io_read32(address), bit_offset, mask) != expect_val) {
        if (timeout == 0) {
            return false;
        }
        timeout--;
        if (interval > 0) {
            dwc_ddrctl_cinit_io_wait_pclk(interval);
        }

    }
    return true;
}

static inline ddrctl_error_t dwc_ddctl_secure_poll_bitfield(uint32_t address, uint32_t bit_offset,
                                                            uint32_t mask, uint32_t expect_val,
                                                            uint32_t timeout_cnt, uint32_t interval_pclk)
{
    while(SNPS_READ_EXPLICIT_FIELD(dwc_ddrctl_cinit_io_secure_read32(address), bit_offset, mask) != expect_val) {
        if (timeout_cnt == 0) {
            return DDRCTL_TIMEOUT;
        }
        timeout_cnt--;
        if (interval_pclk > 0) {
            dwc_ddrctl_cinit_io_wait_pclk(interval_pclk);
        }
    }
    return DDRCTL_SUCCESS;
}


static inline ddrctl_error_t cinit_poll_bitfield(uint32_t address, uint32_t bit_offset, uint32_t mask,
                                                 uint32_t expect_val, uint32_t timeout_cnt, uint32_t interval_pclk)
{
    while(SNPS_READ_EXPLICIT_FIELD(dwc_ddrctl_cinit_io_read32(address), bit_offset, mask) != expect_val) {
        if (timeout_cnt == 0) {
            return DDRCTL_TIMEOUT;
        }
        timeout_cnt--;
        if (interval_pclk > 0) {
            dwc_ddrctl_cinit_io_wait_pclk(interval_pclk);
        }

    }
    return DDRCTL_SUCCESS;
}

void dwc_cinit_memset32(void *dest, uint32_t value, size_t size);

#endif /* __DWC_DDRCTL_CINIT_UTIL_H__ */
