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

MAKE_LOG_ID := "SPD_GEN: "

RM    := rm -Rf
MKDIR := mkdir -p
LD    := gcc
CC    := gcc

LOCAL_DIR :=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))

# Define folders
BUILD_DIR     	= $(LOCAL_DIR)/build/
BIN_DIR       	= $(LOCAL_DIR)/bin/

# Define target binary name
BIN := $(BIN_DIR)/spd_generator

# Add all needed included folders
INCL_DIR := $(LOCAL_DIR)/include

CFLAGS  += -W -Wall -Wextra
CFLAGS  += $(foreach dir,$(INCL_DIR),-I$(dir))
LDFLAGS += -lm

# Define source file(s) to compile
SRC_FILES := $(notdir $(wildcard $(LOCAL_DIR)/src/*.c))

# Source search paths
VPATH := $(LOCAL_DIR)/src

OBJS := $(patsubst %.c,$(BUILD_DIR)/%.o,$(notdir $(SRC_FILES)))

##############################################################################
# Targets
##############################################################################
all : $(BIN)

.PHONY : all debug

debug :
	@echo "$(MAKE_LOG_ID)LOCAL_DIR       = $(LOCAL_DIR)"
	@echo "$(MAKE_LOG_ID)BUILD_DIR       = $(BUILD_DIR)"
	@echo "$(MAKE_LOG_ID)INCL_DIR        = $(INCL_DIR)"
	@echo "$(MAKE_LOG_ID)SRC_FILES       = $(SRC_FILES)"
	@echo "$(MAKE_LOG_ID)OBJS            = $(OBJS)"
	@echo "$(MAKE_LOG_ID)CFLAGS	         = $(CFLAGS)"
	@echo "$(MAKE_LOG_ID)BIN             = $(BIN)"

clean:
	@echo "$(MAKE_LOG_ID)Clean objects and binary"
	$(VERBOSE)$(RM) $(BIN) $(OBJS) $(BUILD_DIR)


$(BUILD_DIR)/%.o : %.c
	$(VERBOSE)$(MKDIR) $(@D)
	@echo "$(MAKE_LOG_ID)Compiling $(<F)"
	$(VERBOSE)$(CC) $(CFLAGS) -c -o $@ $<

$(BIN): $(OBJS)
	$(VERBOSE)$(MKDIR) $(@D)
	@echo "$(MAKE_LOG_ID)Creating binary: $(@F)"
	$(VERBOSE)$(LD) $(OBJS) $(LDFLAGS) $(CFLAGS) -o $@
