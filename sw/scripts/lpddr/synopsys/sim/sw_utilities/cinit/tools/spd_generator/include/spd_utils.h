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


#ifndef TOOLS_SPDGENERATOR_INCLUDE_SPD_UTILS_H_
#define TOOLS_SPDGENERATOR_INCLUDE_SPD_UTILS_H_

#include "spd_generator.h"

#define SNPS_COMP_STR(a, b)    (strlen(a) == strlen(b) && !strncmp((a), (b), strlen(a)))

/**
 * @brief Macro to help read the variables fields
 *
 * @param value
 * @param bit_offset
 * @param mask
 * @return field value
 */
#define SNPS_READ_FIELD(reg_value, bit_offset, mask) \
	(((reg_value) & (mask)) >> (bit_offset))


/**
 * @brief Macro to help set the variables fields
 *
 * @param variable
 * @param bit_offset
 * @param mask
 * @param value  field value
 *
 * @note: unsafe macro due to variable and mask duplication
 */
#define SNPS_WRITE_FIELD(reg_value, bit_offset, mask, field_value) \
    ((reg_value) = (((reg_value) & (~(mask))) | (((field_value) << (bit_offset)) & (mask))))

void reverse_calculation(uint32_t value, uint8_t* tMTB,  int8_t* tFTB);

uint16_t crc16_calc(uint8_t *ptr, uint16_t count);

#endif /* TOOLS_SPDGENERATOR_INCLUDE_SPD_UTILS_H_ */
