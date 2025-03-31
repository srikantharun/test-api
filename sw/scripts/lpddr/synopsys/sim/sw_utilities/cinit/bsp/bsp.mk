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


ifndef MAKEFILE_BSP
MAKEFILE_BSP = 1

ifndef CINIT_BASE_DIR
	$(error CINIT_BASE_DIR must be defined)
endif

ifndef CINIT_PLATFORM
	CINIT_PLATFORM := local_x86
$(warning warning: CINIT_PLATFORM not set, using default $(CINIT_PLATFORM) (supported options: local_x86 simulation example))
endif

include	$(CINIT_BASE_DIR)/bsp/platform/$(CINIT_PLATFORM)/$(CINIT_PLATFORM).mk

CFLAGS += -I$(CINIT_BASE_DIR)/bsp/platform/$(CINIT_PLATFORM)/include

ifndef CINIT_COMPILER
	CINIT_COMPILER := gcc
$(warning warning: CINIT_COMPILER not set, default $(CINIT_COMPILER) (supported options: gcc))
endif

include	$(CINIT_BASE_DIR)/bsp/compiler/$(CINIT_COMPILER)/$(CINIT_COMPILER).mk

ifndef CINIT_ARCH
	CINIT_ARCH := $(shell uname -m | sed -e s/i.86_64/x86_64/ -e s/i.86/x86/)
$(warning warning: CINIT_ARCH not set, using the system arch $(CINIT_ARCH) (supported options: x86 x86_64 arm arc_em4))
endif

include	$(CINIT_BASE_DIR)/bsp/arch/$(CINIT_ARCH).mk

ifndef CINIT_OS
	CINIT_OS := linux
$(warning warning: CINIT_OS not set, using default $(CINIT_OS) (supported options: linux cygwin))
endif

CFLAGS += -I$(CINIT_BASE_DIR)/bsp/include

# General Flags
CFLAGS += -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function -Wno-expansion-to-defined


ifdef CINIT_ENABLE_REG_FORCE_WRITE
	CFLAGS += -DCINIT_ENABLE_REG_FORCE_WRITE
$(warning warning: Register Force write enable, all registers will be written even if the value to write match the default)
endif

include	$(CINIT_BASE_DIR)/bsp/os/$(CINIT_OS)/$(CINIT_OS).mk

include	$(CINIT_BASE_DIR)/bsp/phy/phy.mk

include	$(CINIT_BASE_DIR)/bsp/ddrctl_regmap/ddrctl_regmap.mk

ifeq ($(MAKECMDGOALS),debug)
	CFLAGS += -g -D DEBUG
endif


HW_CONFIG_INCLUDE_DIR := $(CINIT_BASE_DIR)/hw_config/include

CFLAGS += -I$(HW_CONFIG_INCLUDE_DIR) -I$(CINIT_BASE_DIR)/library -I$(CINIT_BASE_DIR)/bsp/ddrctl/include


# Export all variables
export

# close makefile guard MAKEFILE_RULES
endif
