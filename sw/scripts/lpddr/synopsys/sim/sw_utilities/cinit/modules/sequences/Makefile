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
MAKE_LOG_ID := "DDRCTL SEQ: "

LOCAL_DIR :=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))

ifndef CINIT_BASE_DIR
CINIT_BASE_DIR := $(abspath $(LOCAL_DIR)../../)
endif

# Configure board support package
include $(CINIT_BASE_DIR)/bsp/bsp.mk

MODULES_LIB_DIR = $(CINIT_BASE_DIR)/modules
DDR_CORE_DIR    = $(MODULES_LIB_DIR)/core
PHY_SETUP_DIR   = $(MODULES_LIB_DIR)/physetup

# Output directories
ifndef OBJ_DIR
OBJ_DIR := $(LOCAL_DIR)build
endif

ifndef LIB_DIR
LIB_DIR   := $(CINIT_BASE_DIR)/lib
endif

LIBNAME := ddr_seq

SEQ_LIB := $(LIB_DIR)/lib$(LIBNAME).a


CFLAGS += -W -Wall -Wextra -std=gnu99
CFLAGS += -fPIC

# Include paths to pass to compiler
INCL_DIR += 										\
	$(LOCAL_DIR)									\
	$(LOCAL_DIR)/include							\
	$(DDR_CORE_DIR)/								\
	$(DDR_CORE_DIR)/include/						\
	$(PHY_SETUP_DIR)/include/



# Add included folders to compiler options
CFLAGS +=  $(foreach dir,$(INCL_DIR),-I$(dir))

# Define source file(s) to compile
SRC_FILES := $(notdir $(wildcard $(LOCAL_DIR)/src/*.c))
SRC_FILES += $(notdir $(wildcard $(LOCAL_DIR)/src/ddr/*.c))
SRC_FILES += $(notdir $(wildcard $(LOCAL_DIR)/src/ddr/ddr5/*.c))
SRC_FILES += $(notdir $(wildcard $(LOCAL_DIR)/src/phy/*.c))


# Source search paths
VPATH := $(LOCAL_DIR)/src
VPATH += $(LOCAL_DIR)/src/ddr
VPATH += $(LOCAL_DIR)/src/ddr/ddr5
VPATH += $(LOCAL_DIR)/src/phy

OBJS := $(patsubst %.c,$(OBJ_DIR)/%.o,$(notdir $(SRC_FILES)))


##############################################################################
# Targets
##############################################################################
.PHONY : all clean help debug
all: $(SEQ_LIB)

clean:
	@echo "$(MAKE_LOG_ID)Clean"
	$(VERBOSE)$(RM) $(OBJ_DIR) $(SEQ_LIB)

debug:
	@echo "$(MAKE_LOG_ID)CINIT_BASE_DIR  = $(CINIT_BASE_DIR)"
	@echo "$(MAKE_LOG_ID)OBJ_DIR         = $(OBJ_DIR)"
	@echo "$(MAKE_LOG_ID)INCL_DIR        = $(INCL_DIR)"
	@echo "$(MAKE_LOG_ID)DDR_STATIC_LIBS = $(DDR_CINIT_LIBS)"
	@echo "$(MAKE_LOG_ID)SRC_FILES       = $(SRC_FILES)"
	@echo "$(MAKE_LOG_ID)OBJS            = $(OBJS)"
	@echo "$(MAKE_LOG_ID)CFLAGS          = $(CFLAGS)"
	@echo "$(MAKE_LOG_ID)LIB             = $(LIB)"


$(OBJ_DIR)/%.o: %.c
	@echo "$(MAKE_LOG_ID)Compiling $(@F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(CC) $(CFLAGS) -c -o $@ $<


$(LIB_DIR)/%.a: $(OBJS)
	@echo "$(MAKE_LOG_ID)Linking static library $(@F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(AR) $(ARFLAGS) $@ $(OBJS)

