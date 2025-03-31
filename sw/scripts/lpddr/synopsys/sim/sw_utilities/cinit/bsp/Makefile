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


VERBOSE = @
MAKE_LOG_ID := "DDRCTL BSP: "


LOCAL_DIR :=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))

ifndef CINIT_BASE_DIR
CINIT_BASE_DIR := $(abspath $(LOCAL_DIR)../)
endif

BSP_BASE_DIR := $(CINIT_BASE_DIR)/bsp

# Configure board support package
include $(BSP_BASE_DIR)/bsp.mk

CINIT_PLATFORM_DIR = $(BSP_BASE_DIR)/platform/$(CINIT_PLATFORM)/
CINIT_COMPILER_DIR = $(BSP_BASE_DIR)/compiler/$(CINIT_COMPILER)/
CINIT_OS_DIR       = $(BSP_BASE_DIR)/os/$(CINIT_OS)/
CINIT_REGMAP_DIR   = $(BSP_BASE_DIR)/ddrctl_regmap/

LIBNAME      = cinit_$(CINIT_PLATFORM)_bsp

# Output directories
BUILD_DIR = $(BSP_BASE_DIR)/build
LIB_DIR   = $(BSP_BASE_DIR)/lib/$(CINIT_ARCH)/$(CINIT_OS)_$(CINIT_COMPILER)

CFLAGS+= -fPIC
LIB := $(LIB_DIR)/lib$(LIBNAME).a

# Include paths to pass to compiler
INCL_DIR :=                                 \
	$(PLATFORM_DIR)/include                 \
	$(CINIT_CTRL_DIR)/include               \
	$(BSP_BASE_DIR)/os/$(CINIT_OS)/include

# Source file(s)
SRC_FILES := $(notdir $(wildcard $(CINIT_PLATFORM_DIR)/src/*.c))
SRC_FILES += $(notdir $(wildcard $(CINIT_COMPILER_DIR)/*.c))
SRC_FILES += $(notdir $(wildcard $(CINIT_OS_DIR)/*.c))
SRC_FILES += $(wildcard *.c) $(wildcard $(CINIT_REGMAP_DIR)/src/*.c)
SRC_FILES += $(wildcard *.c) $(wildcard $(CINIT_REGMAP_DIR)/src/regmap/*.c)
SRC_FILES += $(wildcard *.c) $(wildcard $(CINIT_REGMAP_DIR)/src/regmap/*/*.c)

# Source search paths
VPATH := $(CINIT_COMPILER_DIR)
VPATH += $(CINIT_OS_DIR)
VPATH += $(CINIT_PLATFORM_DIR)/src
VPATH += $(CINIT_REGMAP_DIR)/src
VPATH += $(dir $(wildcard $(CINIT_REGMAP_DIR)/src/regmap/*))
VPATH += $(dir $(wildcard $(CINIT_REGMAP_DIR)/src/regmap/*/*))


OBJS := $(patsubst %.c,$(BUILD_DIR)/%.o,$(notdir $(SRC_FILES)))

CFLAGS += $(foreach dir,$(INCL_DIR),-I$(dir))

##############################################################################
# Targets
##############################################################################
.PHONY : all clean debug
all: $(LIB)


clean:
	@echo "$(MAKE_LOG_ID)Clean"
	$(VERBOSE)$(RM) $(BUILD_DIR) $(LIB_DIR)


debug :
	@echo "$(MAKE_LOG_ID)BSP_BASE_DIR = $(BSP_BASE_DIR)"
	@echo "$(MAKE_LOG_ID)BUILD_DIR    = $(BUILD_DIR)"
	@echo "$(MAKE_LOG_ID)LIB_DIR      = $(LIB_DIR)"
	@echo "$(MAKE_LOG_ID)INCL_DIR     = $(INCL_DIR)"
	@echo "$(MAKE_LOG_ID)SRC_FILES    = $(SRC_FILES)"
	@echo "$(MAKE_LOG_ID)OBJS         = $(OBJS)"
	@echo "$(MAKE_LOG_ID)CFLAGS       = $(CFLAGS)"
	@echo "$(MAKE_LOG_ID)LIBNAME      = $(LIBNAME)"
	@echo "$(MAKE_LOG_ID)LIB          = $(LIB)"


$(BUILD_DIR)/%.o : %.c
	@echo "$(MAKE_LOG_ID)Compiling $(@F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(CC) $(CFLAGS) -c -o $@ $<


$(LIB_DIR)/%.a : $(OBJS)
	@echo "$(MAKE_LOG_ID)Linking static library $(@F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(AR) $(ARFLAGS) $@ $(OBJS)
