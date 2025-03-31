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


#ifndef CINIT_BSP_DDRCTRL_INCLUDE_DDRCTRL_REG_TYPES_H_
#define CINIT_BSP_DDRCTRL_INCLUDE_DDRCTRL_REG_TYPES_H_

#include "dwc_cinit_bsp.h"
#include "dwc_cinit_types.h"
#include "dwc_cinit_utils.h"
#include "dwc_cinit_platform.h"

typedef enum ddrctl_access_type_e {
        ACCESS_UNKNOWN          = 0,
        ACCESS_READ             = 1,
        ACCESS_WRITE            = 2,
        ACCESS_READ_WRITE       = ACCESS_READ | ACCESS_WRITE,
        ACCESS_WRITE_ONCE       = 4,
        ACCESS_READ_WRITE_ONCE  = ACCESS_READ | ACCESS_WRITE_ONCE,
} ddrctl_access_type_t;

typedef enum ddrctl_security_e {
        SEC_NON_SECURE  = 0,
        SEC_ROOT        = 1,
        SEC_SECURE      = 2,
        SEC_REALM       = 3,
} ddrctl_security_t;

typedef enum ddrctl_prog_mode_e {
        PROG_UNKNOWN            = 0,
        PROG_STATIC             = 1,
        PROG_DYNAMIC            = 2,
        PROG_QUASI_DYNAMIC      = 3,
} ddrctl_prog_mode_t;


typedef struct ddrctl_field_s {
        char                    *name;
        uint8_t                 offset;
        uint8_t                 width;
        ddrctl_access_type_t    access_type;
        ddrctl_prog_mode_t      prog_mode;
} ddrctl_field_t;


typedef struct ddrctl_reg_s {
        uint32_t                addr;
        const char              *name;
        uint32_t                reset_value;
        uint32_t                value;
        ddrctl_security_t       security;
        const ddrctl_field_t    *field_table;
} ddrctl_reg_t;


typedef struct ddrctl_block_s {
        uint32_t                addr;
        const char              *name;
        ddrctl_reg_t            *reg_table;
} ddrctl_block_t;

#endif /* CINIT_BSP_DDRCTRL_INCLUDE_DDRCTRL_REG_TYPES_H_ */
