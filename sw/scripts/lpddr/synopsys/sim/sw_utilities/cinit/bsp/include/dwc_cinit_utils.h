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


#ifndef CINIT_BSP_INCLUDE_DWC_CINIT_UTILS_H_
#define CINIT_BSP_INCLUDE_DWC_CINIT_UTILS_H_

#include "dwc_cinit_os_bsp.h"

#define MAX_STRING_BUFFER   500
#define MAX_NAME_SIZE       150


#ifndef max
#define max(a, b)    (((a) > (b)) ? (a) : (b))
#endif

#ifndef min
#define min(a, b)    (((a) < (b)) ? (a) : (b))
#endif

#define GET_ARR_NELEMS(arr_symbol) (sizeof(arr_symbol) / sizeof(arr_symbol[0]))


/**
 * @brief Macro to help read the variables fields
 *
 * @param value
 * @param bit_offset
 * @param mask
 * @return field value
 */
#define SNPS_READ_EXPLICIT_FIELD(reg_value, bit_offset, mask) \
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
#define SNPS_WRITE_EXPLICIT_FIELD(reg_value, bit_offset, mask, field_value) \
    ((reg_value) = (((reg_value) & (~(mask))) | (((field_value) << (bit_offset)) & (mask))))


/* ASSERT Definitions, both for simulation and production  code */
#ifndef DISABLE_ASSERT
#define CINIT_ASSERT(check) \
    do { \
        if (0 == (check)) { \
            dwc_ddrctl_cinit_assert_exit(#check, basename(__FILE__), __func__, __LINE__); \
        } \
    } while (0)
#else /* NDEBUG */
# define CINIT_ASSERT(check) (void)0
#endif /* NDEBUG */


#define CONSTRAIN_INSIDE(value, min_constrain, max_constrain) \
    do { \
          CINIT_ASSERT(((value) >= (min_constrain)) && ((value) <= (max_constrain))); \
    } while (0)

#define CONSTRAIN_MIN(value, constrain) \
    do { \
            CINIT_ASSERT((value) >= (constrain)); \
    } while (0)

#define CONSTRAIN_MAX(value, constrain) \
    do { \
            CINIT_ASSERT(value <= constrain); \
    } while (0)

#define CONSTRAIN_NE(value, constrain) \
    do { \
            CINIT_ASSERT(value != constrain); \
    } while (0)

#define CONSTRAIN_EQ(value, constrain) \
    do { \
            CINIT_ASSERT(value == constrain); \
    } while (0)

#endif /* CINIT_BSP_INCLUDE_DWC_CINIT_UTILS_H_ */
