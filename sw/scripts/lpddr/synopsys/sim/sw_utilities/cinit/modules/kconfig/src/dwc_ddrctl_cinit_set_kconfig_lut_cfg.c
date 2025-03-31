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


#include "dwc_ddrctl_cinit_kconfig_headers.h"
#include "dwc_ddrctl_lut_defines.h"

/**
 * @brief Function to set LUT confguration values from Kconfig.
 */
void dwc_ddrctl_cinit_set_kconfig_lut_cfg(void)
{
#if defined(DDRCTL_LUT_ADDRMAP)

#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 0
    CFG->lut_entry[0] = DWC_DDRCTL_CINIT_LUT_ENTRY_0;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 0 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 1
    CFG->lut_entry[1] = DWC_DDRCTL_CINIT_LUT_ENTRY_1;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 1 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 2
    CFG->lut_entry[2] = DWC_DDRCTL_CINIT_LUT_ENTRY_2;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 2 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 3
    CFG->lut_entry[3] = DWC_DDRCTL_CINIT_LUT_ENTRY_3;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 3 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 4
    CFG->lut_entry[4] = DWC_DDRCTL_CINIT_LUT_ENTRY_4;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 4 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 5
    CFG->lut_entry[5] = DWC_DDRCTL_CINIT_LUT_ENTRY_5;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 5 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 6
    CFG->lut_entry[6] = DWC_DDRCTL_CINIT_LUT_ENTRY_6;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 6 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 7
    CFG->lut_entry[7] = DWC_DDRCTL_CINIT_LUT_ENTRY_7;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 7 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 8
    CFG->lut_entry[8] = DWC_DDRCTL_CINIT_LUT_ENTRY_8;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 8 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 9
    CFG->lut_entry[9] = DWC_DDRCTL_CINIT_LUT_ENTRY_9;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 9 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 10
    CFG->lut_entry[10] = DWC_DDRCTL_CINIT_LUT_ENTRY_10;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 10 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 11
    CFG->lut_entry[11] = DWC_DDRCTL_CINIT_LUT_ENTRY_11;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 11 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 12
    CFG->lut_entry[12] = DWC_DDRCTL_CINIT_LUT_ENTRY_12;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 12 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 13
    CFG->lut_entry[13] = DWC_DDRCTL_CINIT_LUT_ENTRY_13;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 13 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 14
    CFG->lut_entry[14] = DWC_DDRCTL_CINIT_LUT_ENTRY_14;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 14 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 15
    CFG->lut_entry[15] = DWC_DDRCTL_CINIT_LUT_ENTRY_15;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 15 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 16
    CFG->lut_entry[16] = DWC_DDRCTL_CINIT_LUT_ENTRY_16;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 16 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 17
    CFG->lut_entry[17] = DWC_DDRCTL_CINIT_LUT_ENTRY_17;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 17 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 18
    CFG->lut_entry[18] = DWC_DDRCTL_CINIT_LUT_ENTRY_18;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 18 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 19
    CFG->lut_entry[19] = DWC_DDRCTL_CINIT_LUT_ENTRY_19;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 19 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 20
    CFG->lut_entry[20] = DWC_DDRCTL_CINIT_LUT_ENTRY_20;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 20 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 21
    CFG->lut_entry[21] = DWC_DDRCTL_CINIT_LUT_ENTRY_21;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 21 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 22
    CFG->lut_entry[22] = DWC_DDRCTL_CINIT_LUT_ENTRY_22;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 22 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 23
    CFG->lut_entry[23] = DWC_DDRCTL_CINIT_LUT_ENTRY_23;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 23 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 24
    CFG->lut_entry[24] = DWC_DDRCTL_CINIT_LUT_ENTRY_24;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 24 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 25
    CFG->lut_entry[25] = DWC_DDRCTL_CINIT_LUT_ENTRY_25;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 25 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 26
    CFG->lut_entry[26] = DWC_DDRCTL_CINIT_LUT_ENTRY_26;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 26 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 27
    CFG->lut_entry[27] = DWC_DDRCTL_CINIT_LUT_ENTRY_27;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 27 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 28
    CFG->lut_entry[28] = DWC_DDRCTL_CINIT_LUT_ENTRY_28;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 28 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 29
    CFG->lut_entry[29] = DWC_DDRCTL_CINIT_LUT_ENTRY_29;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 29 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 30
    CFG->lut_entry[30] = DWC_DDRCTL_CINIT_LUT_ENTRY_30;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 30 */
#if DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 31
    CFG->lut_entry[31] = DWC_DDRCTL_CINIT_LUT_ENTRY_31;
#endif /* DWC_DDRCTL_MAX_LUT_ENTRIES_AUX > 31 */

#endif /* DDRCTL_LUT_ADDRMAP */
}

