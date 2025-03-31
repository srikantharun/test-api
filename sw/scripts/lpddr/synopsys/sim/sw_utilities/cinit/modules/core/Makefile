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
MAKE_LOG_ID := "DDRCTL CORE: "

LOCAL_DIR :=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))

ifndef CINIT_BASE_DIR
CINIT_BASE_DIR := $(abspath $(LOCAL_DIR)../../)
endif

# Configure board support package
include $(CINIT_BASE_DIR)/bsp/bsp.mk

# Output directories
BUILD_DIR := $(LOCAL_DIR)/build
LIB_DIR   := $(CINIT_BASE_DIR)/lib

LIBNAME := core
LIB     := $(LIB_DIR)/lib$(LIBNAME).a

# Modules directories
LIBRARY_DIR           := $(CINIT_BASE_DIR)/library
LIBRARY_SCRIPTS_DIR   := $(LIBRARY_DIR)/scripts
KCONFIG_DIR           := $(CINIT_BASE_DIR)/modules/kconfig
C_SV_CONVERTER_DIR    := $(CINIT_BASE_DIR)/tools/c_sv_converter


# C headers that needs to be converted to system-verilog syntax
HDRS_CONVERT_TO_VERILOG :=								\
	$(LOCAL_DIR)/include/dwc_ddrctl_cinit_cfg.h 		\
	$(LOCAL_DIR)/include/dwc_ddrctl_cinit_types.h 		\
	$(LOCAL_DIR)/include/dwc_ddrctl_cinit_cfg_dyn.h 	\
	$(LOCAL_DIR)/include/dwc_ddrctl_cinit_cfg_qdyn.h 	\
	$(LOCAL_DIR)/include/dwc_ddrctl_cinit_cfg_static.h


#Specify jedec revision (only used for speedbin timings at the moment)
DDR4_JEDEC_SPEEDBINS_REV := JESD79_4C_DDR4_SPEEDBINS
DDR4_3DS_JEDEC_SPEEDBINS_REV := JESD79_4_1_B_DDR4_3DS_SPEEDBINS
DDR5_JEDEC_SPEEDBINS_REV := JESD79_5A_DDR5_SPEEDBINS


# Include paths to pass to compiler
INCL_DIR += 				\
	$(LOCAL_DIR)			\
	$(LOCAL_DIR)/src		\
	$(LOCAL_DIR)/include	\
	$(KCONFIG_DIR)/include

# Source file(s)
SRC := $(notdir $(wildcard $(LOCAL_DIR)/src/*.c))
SRC += $(notdir $(wildcard $(LOCAL_DIR)/src/mode_regs/ddr4/*.c))
SRC += $(notdir $(wildcard $(LOCAL_DIR)/src/ctrl_words/ddr4/*.c))
SRC += $(notdir $(wildcard $(LOCAL_DIR)/src/mode_regs/ddr5/*.c))
SRC += $(notdir $(wildcard $(LOCAL_DIR)/src/ctrl_words/ddr5/*.c))
SRC += $(notdir $(wildcard $(LOCAL_DIR)/src/sw_cmd_intf/ddr5/*.c))
# JEDEC Speed Bin and Speed Grade tables
SRC += $(notdir $(wildcard $(LOCAL_DIR)/jedec/ddr4/*.c))
SRC += $(notdir $(wildcard $(LOCAL_DIR)/jedec/ddr5/*.c))

# specify JEDEC revision used for the speed bin tables
CFLAGS += -D$(DDR4_JEDEC_SPEEDBINS_REV)
CFLAGS += -D$(DDR4_3DS_JEDEC_SPEEDBINS_REV)
CFLAGS += -D$(DDR5_JEDEC_SPEEDBINS_REV)

# Source search paths
VPATH := 								\
	$(LOCAL_DIR)/src					\
	$(LOCAL_DIR)/src/mode_regs/ddr4 	\
	$(LOCAL_DIR)/src/mode_regs/ddr5 	\
	$(LOCAL_DIR)/src/ctrl_words/ddr4 	\
	$(LOCAL_DIR)/src/ctrl_words/ddr5 	\
	$(LOCAL_DIR)/src/sw_cmd_intf/ddr5 	\
	$(LOCAL_DIR)/jedec/ddr4				\
	$(LOCAL_DIR)/jedec/ddr5

CFLAGS += $(foreach dir,$(INCL_DIR),-I$(dir))
CFLAGS += -W -Wall -Wextra -std=gnu99
CFLAGS += -fPIC

ifdef DWC_DDRCTL_CINIT_CPU_DPI_MODE
	CFLAGS += -DDWC_DDRCTL_CINIT_CPU_DPI_MODE
endif


ifdef USE_KCONFIG_DEFINITIONS
	CFLAGS += -DUSE_KCONFIG_DEFINITIONS
endif


OBJS := $(patsubst %.c,$(BUILD_DIR)/%.o,$(notdir $(SRC)))
DEP  := $(patsubst %.c,$(BUILD_DIR)/%.d,$(notdir $(SRC)))


##############################################################################
# Targets
##############################################################################
.PHONY : all clean debug gen-verilog-headers
all: $(LIB)


clean:
	@echo "$(MAKE_LOG_ID)Clean"
	$(VERBOSE)$(RM) $(BUILD_DIR) $(LIB)


debug:
	@echo "$(MAKE_LOG_ID)SRC = $(SRC)"
	@echo "$(MAKE_LOG_ID)OBJS = $(OBJS)"
	@echo "$(MAKE_LOG_ID)CFLAGS = $(CFLAGS)"
	@echo "$(MAKE_LOG_ID)LDFLAGS = $(LDFLAGS)"
	@echo "$(MAKE_LOG_ID)LIB = $(LIB)"
	@echo "$(MAKE_LOG_ID)BUILD_DIR = $(BUILD_DIR)"
	@echo "$(MAKE_LOG_ID)INCL_DIR = $(INCL_DIR)"
	@echo "$(MAKE_LOG_ID)LIB_DIR = $(LIB_DIR)"


%.svh: %.h
	@echo "$(MAKE_LOG_ID)Converting $(<F) to System Verilog"
	$(VERBOSE)$(PYTHON) $(C_SV_CONVERTER_DIR)/c_sv_converter.py -i $< -m c_to_sv



gen-verilog-headers: $(HDRS_CONVERT_TO_VERILOG:.h=.svh)
	@echo "$(MAKE_LOG_ID)Converting Files to System Verilog"


clean-verilog-headers:
	@echo "$(MAKE_LOG_ID)Cleaning Verilog Headers...."
	$(VERBOSE)$(RM) $(HDRS_CONVERT_TO_VERILOG:.h=.svh)


$(BUILD_DIR)/%.o : %.c
	$(VERBOSE)$(MKDIR) $(@D)
	@echo "$(MAKE_LOG_ID)Compiling $(@F)"
	$(VERBOSE)$(CC) $(CFLAGS) -c -o $@ $<


$(LIB_DIR)/lib$(LIBNAME).a: $(OBJS)
	@echo "$(MAKE_LOG_ID)Linking static library $(@F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(AR) $(ARFLAGS) $@ $(OBJS)


