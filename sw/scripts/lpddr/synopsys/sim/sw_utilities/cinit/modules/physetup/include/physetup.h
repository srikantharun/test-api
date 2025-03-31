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


#ifndef __MODULES_PHYSETUP_INCLUDE_PHYSETUP_H__
#define __MODULES_PHYSETUP_INCLUDE_PHYSETUP_H__

#include "dwc_ddrctl_cinit.h"

#ifdef PHYINIT
#include "dwc_ddrphy_phyinit_userCustom.h"
#endif

void physetup_log_open();

void physetup_log_close();


ddrctl_error_t physetup_config_init(SubsysHdlr_t *config);
void physetup_config_free(SubsysHdlr_t *config);


void physetup_io_write16(uint32_t addr, uint16_t data);

uint16_t physetup_io_read16(uint32_t addr);


void physetup_set_user_input(SubsysHdlr_t *hdlr, char *field, int value);

void physetup_set_msg_block(SubsysHdlr_t *hdlr, int ps, char *field, int value, int train_2d);


ddrctl_error_t physetup_sequence(SubsysHdlr_t *config);

ddrctl_error_t physetup_restore_sequence(SubsysHdlr_t *config);

void dwc_cinit_phyinit_setuserinput(SubsysHdlr_t *hdlr);

void overrideUserInput_sv(void);

#endif /* __MODULES_PHYSETUP_INCLUDE_PHYSETUP_H__ */
