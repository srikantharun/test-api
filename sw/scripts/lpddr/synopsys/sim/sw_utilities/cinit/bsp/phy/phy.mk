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


ifeq ($(PROTOCOL),$(filter $(PROTOCOL),ddr4 ddr4_rdimm ddr4_lrdimm))
	CFLAGS += -DCINIT_DDR4
else ifeq ($(PROTOCOL),$(filter $(PROTOCOL),ddr5 ddr5_rdimm ddr5_lrdimm))
	CFLAGS   += -DCINIT_DDR5
	ifdef PHY_VDEFINES_FILE
		ifneq ($(shell grep DDR5_PHY $(PHY_VDEFINES_FILE)),)
			ifeq ($(PROTOCOL),ddr5)
				CFLAGS   += -D_BUILD_DDR5
			endif
			ifeq ($(PROTOCOL),ddr5_rdimm)
				CFLAGS   += -D_BUILD_DDR5R
			endif
		endif
	endif
else ifeq ($(PROTOCOL),$(filter $(PROTOCOL),lpddr4 lpddr4x))
	CFLAGS   += -DCINIT_LPDDR4
	ifeq ($(PROTOCOL),lpddr4) # Need FLAG D_BUILD_LPDDR for phyinit 2020.09 and newer DWC_PHYINIT_RID_GE202009
		CFLAGS   += -D_BUILD_LPDDR4
	else  # lpddr4x
		CFLAGS   += -D_BUILD_LPDDR4X
	endif
else ifeq ($(PROTOCOL),$(filter $(PROTOCOL),lpddr5 lpddr5x))
	CFLAGS   += -DCINIT_LPDDR5
	# Need FLAG D_BUILD_LPDDR for phyinit 2020.09 and newer DWC_PHYINIT_RID_GE202009
	CFLAGS   += -D_BUILD_LPDDR5
else
	$(error No protocol defined)
endif

ifndef PHYINIT_SW_DIR
	PHYINIT_SW_DIR := $(CINIT_BASE_DIR)/../phy/software
endif

ifndef PHYINIT_FW_DIR
	PHYINIT_FW_DIR := $(CINIT_BASE_DIR)/../phy/firmware
endif

ifndef PHYINIT_MMFW_DIR
	PHYINIT_MMFW_DIR := $(CINIT_BASE_DIR)/../phy/mmfw
endif

ifeq ($(PROTOCOL),ddr5_rdimm)
	PROTOCOL_PHYINIT_FW_DIR_2D := ddr5_rdimm2d
else
	ifeq ($(PROTOCOL),ddr5_lrdimm)
		PROTOCOL_PHYINIT_FW_DIR_2D := ddr5_lrdimm
	else
		ifeq ($(PROTOCOL),ddr4_rdimm)
			PROTOCOL_PHYINIT_FW_DIR_2D := ddr4_rdimm2d
		else
			ifeq ($(PROTOCOL),ddr4_lrdimm)
				PROTOCOL_PHYINIT_FW_DIR_2D := ddr4_lrdimm2d
			else
				PROTOCOL_PHYINIT_FW_DIR_2D := $(PROTOCOL)_2d
			endif
		endif
	endif
endif

INCL_DIR = 											\
	$(PHYINIT_SW_DIR)/$(PROTOCOL)/src 				\
	$(PHYINIT_FW_DIR)/$(PROTOCOL) 					\
	$(PHYINIT_MMFW_DIR)/$(PROTOCOL) 					\
	$(PHYINIT_FW_DIR)/$(PROTOCOL_PHYINIT_FW_DIR_2D)

CFLAGS += \
	$(foreach dir,$(INCL_DIR),-I$(dir))

# Export all variables
export
