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


#ifndef __BIT_MACROS_H__
#define __BIT_MACROS_H__

/*************************************************************************
* T Y P E D E F S    &    D E F I N E S
*************************************************************************/


/**
 * @brief Macro utility to create a bit mask with bits sets.
 *
 * For example, SNPS_BITMASK(6:4) yields 0x00000070
 *
 * @param msb Most significant bit of set mask
 * @param lsb Least significant bit of set mask
 * 
 * @deprecated shouldn't be used
 */
#define SNPS_BITMASK(msb, lsb) \
    (((uint32_t) - 1 >> (31 - (msb))) & ~((1U << (lsb)) - 1))

/**
 * @brief Macro utility to get a selection of bits within a 32-bit value
 *
 * @param reg 32-bit register value
 * @param msb Most significant bit
 * @param lsb Least significant bit
 * @return Bit field value
 * 
 * @deprecated use only SNPS_READ_FIELD
 */
#define SNPS_GETBITMASK(reg, msb, lsb) \
    (((reg) & SNPS_BITMASK(msb, lsb)) >> (lsb))

#endif /* __BIT_MACROS_H__ */
