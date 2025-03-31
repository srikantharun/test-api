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


VERBOSE := @
MAKE_LOG_ID := "DDRCTL CINIT: "

LOCAL_DIR :=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ifndef CINIT_BASE_DIR
	CINIT_BASE_DIR := $(abspath $(LOCAL_DIR)/)
endif

# Configure board support package
include $(CINIT_BASE_DIR)/bsp/bsp.mk

# Checks for the required tools
include $(CINIT_BASE_DIR)/Makefile.tool_check

ifndef HW_CONFIG_INCLUDE_DIR
$(error error: HW_CONFIG_INCLUDE_DIR parameter must be defined)
endif

###
# Folder Variables
LIB_DIR               := $(CINIT_BASE_DIR)/lib

BSP_LIB_DIR           := $(CINIT_BASE_DIR)/bsp/lib/$(CINIT_ARCH)/$(CINIT_OS)_$(CINIT_COMPILER)
BSP_DIR               := $(CINIT_BASE_DIR)/bsp

LIBRARY_DIR           := $(CINIT_BASE_DIR)/library
LIBRARY_SCRIPTS_DIR   := $(LIBRARY_DIR)/scripts

MODULES_DIR           := $(CINIT_BASE_DIR)/modules
CORE_DIR              := $(MODULES_DIR)/core
PHYSETUP_DIR          := $(MODULES_DIR)/physetup
KCONFIG_DIR           := $(MODULES_DIR)/kconfig
SEQUENCES_DIR         := $(MODULES_DIR)/sequences
VERIFICATION_DIR      := $(MODULES_DIR)/verification

SCONFIG_DIR           := $(CINIT_BASE_DIR)/tools/sconfig
C_SV_CONVERTER_DIR    := $(CINIT_BASE_DIR)/tools/c_sv_converter


###
# CINIT configuration files
CINIT_CONFIG_FILE := $(LIBRARY_DIR)/.autoconf.h
DDRCTL_REGMAP_DIR := $(BSP_DIR)/ddrctl_regmap/src/regmap


###
# CINIT hardware configuration variables
MEMORY_MAP_CSV    := $(LIBRARY_DIR)/MemoryMapXml.csv

CC_CONSTANTS_FILE_UNPREFIX := $(CINIT_BASE_DIR)/../../../src/DWC_ddrctl_cc_constants.svh






CC_CONSTANTS_FILE_PREFIX :=


# If prefix file is defined it must be decoded using the unprefix file
# Note: In this case the unprefix file will contain only defines unprefix, prefix pair.
#       Use that to translate the prefixed names to unprefix
ifneq ($(CC_CONSTANTS_FILE_PREFIX),)
	CC_CONSTANTS_FILE        := $(CC_CONSTANTS_FILE_PREFIX)
	CC_CONSTANTS_DICT_OPTION := -d $(CC_CONSTANTS_FILE_UNPREFIX)
else
	CC_CONSTANTS_FILE        := $(CC_CONSTANTS_FILE_UNPREFIX)
	CC_CONSTANTS_DICT_OPTION :=
endif





IME_CC_CONSTANTS_FILE :=


CC_CONSTANTS_HDR := $(HW_CONFIG_INCLUDE_DIR)/DWC_ddrctl_cc_constants.h
ifeq ($(wildcard $(IME_CC_CONSTANTS_FILE)),)
	IME_CC_CONSTANTS_HDR :=
else
	IME_CC_CONSTANTS_HDR := $(HW_CONFIG_INCLUDE_DIR)/$(addsuffix .h, $(basename $(notdir $(IME_CC_CONSTANTS_FILE))))
endif
PHY_DEFINES_HDR := $(HW_CONFIG_INCLUDE_DIR)/$(addsuffix .h, $(basename $(notdir $(PHY_VDEFINES_FILE))))

DDR_CFG_VERILOG_H := $(CC_CONSTANTS_FILE) $(IME_CC_CONSTANTS_FILE) $(PHY_VDEFINES_FILE)
DDRCTL_CFG_H      := $(CC_CONSTANTS_HDR) $(IME_CC_CONSTANTS_HDR)
DDRPHY_CFG_H      := $(PHY_DEFINES_HDR)
DDR_CFG_H         := $(DDRCTL_CFG_H) $(DDRPHY_CFG_H)

# Add configuration headers folder to VPATH
VPATH := $(dir $(wildcard $(DDR_CFG_VERILOG_H)))


###
# Libs difinitions
LIB_CORE     := $(LIB_DIR)/libcore.a
LIB_PHYSETUP := $(LIB_DIR)/libphysetup.a
LIB_DDR_SEQ  := $(LIB_DIR)/libddr_seq.a
LIB_VERIFIC  := $(LIB_DIR)/libverific.a
LIB_KCONFIG  := $(LIB_DIR)/libkconfig.a
BSP_LIB_NAME := cinit_$(CINIT_PLATFORM)_bsp
LIB_BSP      := $(BSP_LIB_DIR)/lib$(BSP_LIB_NAME).a

ifeq ($(LINK_PHYINT),1)
	LIB_DDRCTL_PHY_NAME := _phyinit_$(PROTOCOL)
	CFLAGS +=-DPHYINIT
ifndef PHYINIT_SW_DIR
	PHYINIT_SW_DIR := $(CINIT_BASE_DIR)/../phy/software
endif
	PHYINIT_OBJ:= $(wildcard $(PHYINIT_SW_DIR)/$(PROTOCOL)_64/*.o )
else
	LIB_PHY_PREFIX_NAME :=
endif

ifdef STATIC_LIB
	LIB_DDRCTL_EXTENSION := .a
else
	CFLAGS+=-fPIC
	LIB_DDRCTL_EXTENSION := $(SHARED_EXT)
endif

LIB_DDRCTL_NAME := cinit$(LIB_DDRCTL_PHY_NAME)$(LIB_DDRCTL_EXTENSION)
LIB_DDRCTL      := $(LIB_DIR)/lib$(LIB_DDRCTL_NAME)

REQUIRED_LIBS = $(LIB_BSP) $(LIB_PHYSETUP) $(LIB_CORE) $(LIB_DDR_SEQ) $(LIB_VERIFIC)
LINKER_LIBS = -lddr_seq -l$(BSP_LIB_NAME) -lcore -lphysetup -lverific

ifdef USE_KCONFIG_DEFINITIONS
	REQUIRED_LIBS += $(LIB_KCONFIG)
	LINKER_LIBS += -lkconfig
endif

ifdef CPU_DPI_MODE
$(info    CPU_DPI_MODE enable)
	CFLAGS += -DDWC_DDRCTL_CINIT_CPU_DPI_MODE
endif


###############################
# Compilation Rules
##############

all: | $(LIB_DDRCTL)

debug :
	@echo "$(MAKE_LOG_ID)CINIT_PLATFORM    = $(CINIT_PLATFORM)"
	@echo "$(MAKE_LOG_ID)PROTOCOL          = $(PROTOCOL)"

.PHONY: all debug

###
# Generation of the header required for testbench
gen-verilog-headers:
	@echo "$(MAKE_LOG_ID)Generate required verilog headers"
	$(VERBOSE)$(MAKE) -C $(CORE_DIR) gen-verilog-headers

clean-verilog-headers:
	@echo "$(MAKE_LOG_ID)Cleaning Verilog Headers...."
	$(VERBOSE)$(MAKE) -C $(CORE_DIR) clean-verilog-headers

.PHONY: gen-verilog-headers gen-verilog-headers

###
# Loading of the Hardware configuration to C format
load-hw-config: $(DDR_CFG_H) $(MEMORY_MAP_CSV)
	$(VERBOSE)$(RM) $(DDRCTL_REGMAP_DIR)
	$(VERBOSE)$(PYTHON) $(SCONFIG_DIR)/sconfig.py --gen_c_reg_map -m $(MEMORY_MAP_CSV)  \
						-c $(DDRCTL_CFG_H)                                      \
						-o $(DDRCTL_REGMAP_DIR)

$(CC_CONSTANTS_HDR): $(CC_CONSTANTS_FILE)
	@echo "$(MAKE_LOG_ID)Converting $(<F) to c"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(PYTHON) $(C_SV_CONVERTER_DIR)/c_sv_converter.py $(CC_CONSTANTS_DICT_OPTION) -o $@ -i $< -m sv_to_c

$(IME_CC_CONSTANTS_HDR): $(IME_CC_CONSTANTS_FILE)
	@echo "$(MAKE_LOG_ID)Converting $(<F) to c"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(PYTHON) $(C_SV_CONVERTER_DIR)/c_sv_converter.py $(CC_CONSTANTS_DICT_OPTION) -o $@ -i $< -m sv_to_c

$(HW_CONFIG_INCLUDE_DIR)/%.h: %.v
	@echo "$(MAKE_LOG_ID)Converting $(<F) to c"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(PYTHON) $(C_SV_CONVERTER_DIR)/c_sv_converter.py -o $@ -i $< -m sv_to_c

clean-hw-config:
	@echo "$(MAKE_LOG_ID)Cleaning Hardware Config...."
	$(VERBOSE)$(RM) $(HW_CONFIG_INCLUDE_DIR)

.PHONY: load-hw-config clean-hw-config

###
# Library compilation
$(LIB_DIR)/%.so: $(REQUIRED_LIBS)
	@echo "$(MAKE_LOG_ID)Linking shared library $(@F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(CC) -shared $(LDFLAGS) $(CFLAGS) -L$(LIB_DIR) -L$(BSP_LIB_DIR) \
		-Wl,--whole-archive $(LINKER_LIBS) -Wl,--no-whole-archive $(PHYINIT_OBJ) -o $@

$(LIB_DIR)/%.a : $(REQUIRED_LIBS)
	@echo "$(MAKE_LOG_ID)Linking static library $(@F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(AR)  -rcT  $@ $(REQUIRED_LIBS) $(PHYINIT_OBJ)

clean: clean-modules
	@echo "$(MAKE_LOG_ID)Cleaning Lib ${LIB_DDRCTL_NAME}...."
	$(VERBOSE)$(RM) $(LIB_DDRCTL)

###
# Modules compilation
bsp: $(LIB_BSP)
$(LIB_BSP):
	@echo "$(MAKE_LOG_ID)Building BSP required lib"
	$(VERBOSE)$(MAKE) -C $(BSP_DIR) CINIT_PLATFORM=$(CINIT_PLATFORM)

core: $(LIB_CORE)
$(LIB_CORE):
	@echo "$(MAKE_LOG_ID)Building CINIT core lib"
	$(VERBOSE)$(MAKE) -C $(CORE_DIR) CINIT_PLATFORM=$(CINIT_PLATFORM)

physetup: $(LIB_PHYSETUP)
$(LIB_PHYSETUP):
	@echo "$(MAKE_LOG_ID)Building Phy Setup lib"
	$(VERBOSE)$(MAKE) -C $(PHYSETUP_DIR) CINIT_PLATFORM=$(CINIT_PLATFORM)

sequences: $(LIB_DDR_SEQ)
$(LIB_DDR_SEQ):
	@echo "$(MAKE_LOG_ID)Building Sequences lib"
	$(VERBOSE)$(MAKE) -C $(SEQUENCES_DIR) CINIT_PLATFORM=$(CINIT_PLATFORM)

verification: $(LIB_VERIFIC)
$(LIB_VERIFIC):
	@echo "$(MAKE_LOG_ID)Building Verification lib"
	$(VERBOSE)$(MAKE) -C $(VERIFICATION_DIR) CINIT_PLATFORM=$(CINIT_PLATFORM)

kconfig: $(LIB_KCONFIG)
$(LIB_KCONFIG):
	@echo "$(MAKE_LOG_ID)Building Kconfig lib"
	$(VERBOSE)$(MAKE) -C $(KCONFIG_DIR)

clean-bsp:
	@echo "$(MAKE_LOG_ID)Cleaning BSP...."
	$(VERBOSE)$(MAKE) -C $(CINIT_BASE_DIR)/bsp clean

clean-core:
	@echo "$(MAKE_LOG_ID)Cleaning Core...."
	$(VERBOSE)$(MAKE) -C $(CORE_DIR) clean CINIT_PLATFORM=$(CINIT_PLATFORM)

clean-physetup:
	@echo "$(MAKE_LOG_ID)Cleaning Phy Setup...."
	$(VERBOSE)$(MAKE) -C $(PHYSETUP_DIR) clean CINIT_PLATFORM=$(CINIT_PLATFORM)

clean-sequences:
	@echo "$(MAKE_LOG_ID)Cleaning Sequences...."
	$(VERBOSE)$(MAKE) -C $(SEQUENCES_DIR) clean CINIT_PLATFORM=$(CINIT_PLATFORM)

clean-verification:
	@echo "$(MAKE_LOG_ID)Cleaning Verification...."
	$(VERBOSE)$(MAKE) -C $(VERIFICATION_DIR) clean CINIT_PLATFORM=$(CINIT_PLATFORM)

clean-kconfig:
	@echo "$(MAKE_LOG_ID)Cleaning Kconfig...."
	$(VERBOSE)$(MAKE) -C $(KCONFIG_DIR) clean

clean-modules: clean-bsp clean-kconfig clean-verification clean-sequences clean-core clean-physetup

.PHONY: bsp core physetup sequences verification kconfig clean-bsp clean-kconfig \
		clean-verification clean-sequences clean-core clean-physetup clean-modules

###
# Load configuration
load-defconfig: $(MEMORY_MAP_CSV)
	@echo "$(MAKE_LOG_ID)Create CINIT configuration file"
	$(VERBOSE)$(RM) $(CINIT_CONFIG_FILE)
	$(VERBOSE)$(PYTHON) $(SCONFIG_DIR)/sconfig.py --gen_config_header -m $(MEMORY_MAP_CSV)  \
						-c $(DDRCTL_CFG_H)                                      \
						-d $(LIBRARY_DIR)/configs/testbench_defconfig           \
						-o $(CINIT_CONFIG_FILE)

.PHONY: load-defconfig

###
# Misc
clean-all: clean clean-modules clean-hw-config clean-verilog-headers

.PHONY: clean-all

