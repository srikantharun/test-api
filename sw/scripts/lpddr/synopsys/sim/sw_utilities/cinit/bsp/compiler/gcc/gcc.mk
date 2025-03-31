# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
# -------------------------------------------------------------------------------


CC    := gcc
CPP   := g++
LD    := gcc
AR    := ar

CINIT_TRACE = 1
# CINIT_TRACE_ON_LOG = 1

ifdef CINIT_TRACE
ifdef CINIT_TRACE_ON_LOG
CFLAGS  += -DCINIT_TRACE_ON_LOG
endif # CINIT_TRACE_ON_LOG

TRACE_EXCL_BSP_FN = _log_type_,ddr_bsp_,get_log_level_str,dwc_ddrctl_cinit_io,dwc_ddrctl_cinit_write,dwc_ddrctl_cinit_custom
TRACE_EXCL_REG_FN = _print_register,_get_mask,_print_register_block,_get_reg_by_addr,ddrctl_regmap_write,_sw_print_ctrl_regmap
TRACE_EXCL_CINIT_FN = dwc_cinit_memset32,dwc_ddctl_poll,cinit_ps_to_tck,dwc_cinit_get_ddr5_trfc,cinit_round_down_only_int_ddr5

CFLAGS  += -finstrument-functions
CFLAGS  += -finstrument-functions-exclude-file-list=testbench
CFLAGS  += -finstrument-functions-exclude-function-list=$(TRACE_EXCL_BSP_FN),$(TRACE_EXCL_REG_FN),$(TRACE_EXCL_CINIT_FN)
endif

CFLAGS += -W -Wall -Wextra

ifdef ANALYZER_STACK
	CFLAGS  += -fstack-usage -fdump-ipa-cgraph
endif

ifdef COVERAGE
    LDFLAGS += -lgcov
    CFLAGS  += -fprofile-arcs -ftest-coverage
endif

# Export all variables
export
