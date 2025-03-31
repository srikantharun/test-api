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



ifndef CINIT_BASE_DIR
	$(error CINIT_BASE_DIR must be defined)
endif

DEFAULT_OS       = linux
DEFAULT_ARCH     = x86_64
DEFAULT_COMPILER = gcc

ifdef CINIT_OS
	ifneq ($(DEFAULT_OS),$(CINIT_OS))
$(warning warning: CINIT_OS ($(CINIT_OS)) overrighted from the platform default,  $(DEFAULT_OS))
	endif
else
	CINIT_OS = $(DEFAULT_OS)
endif


ifdef CINIT_ARCH
	ifneq ($(DEFAULT_ARCH),$(CINIT_ARCH))
$(warning warning: CINIT_ARCH ($(CINIT_ARCH)) overrighted from the platform default,  $(DEFAULT_ARCH))
	endif
else
	CINIT_ARCH = $(DEFAULT_ARCH)
endif


ifdef CINIT_COMPILER
	ifneq ($(DEFAULT_COMPILER),$(CINIT_COMPILER))
$(warning warning: CINIT_COMPILER ($(CINIT_COMPILER)) overrighted from the platform default,  $(DEFAULT_COMPILER))
	endif
else
	CINIT_COMPILER = $(DEFAULT_COMPILER)
endif

# Export all variables
export
