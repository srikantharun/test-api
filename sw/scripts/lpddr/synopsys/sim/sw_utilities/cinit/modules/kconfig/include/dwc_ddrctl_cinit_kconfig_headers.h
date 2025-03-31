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


#ifndef __DWC_DDRCTL_CINIT_KCONFIG_HEADERS_H__
#define __DWC_DDRCTL_CINIT_KCONFIG_HEADERS_H__

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include ".autoconf.h"

#define DO_EXPAND(VAL)  VAL ## 1
#define EXPAND(VAL)     DO_EXPAND(VAL)

#define NO_OTHER_MACRO_STARTS_WITH_THIS_NAME_
#define IS_EMPTY(name) defined(NO_OTHER_MACRO_STARTS_WITH_THIS_NAME_ ## name)
#define EMPTY(name) IS_EMPTY(name)

#endif /* __DWC_DDRCTL_CINIT_KCONFIG_HEADERS_H__ */

