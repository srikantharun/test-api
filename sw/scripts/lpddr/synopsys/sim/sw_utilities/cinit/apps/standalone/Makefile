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
MAKE_LOG_ID := "DDRCTL STANDALONE: "

LOCAL_DIR :=$(dir $(abspath $(lastword $(MAKEFILE_LIST))))

ifndef CINIT_PLATFORM
CINIT_PLATFORM := local_x86
endif

ifndef CINIT_BASE_DIR
CINIT_BASE_DIR := $(abspath $(LOCAL_DIR)../../)
endif

# Configure board support package
include $(CINIT_BASE_DIR)/bsp/bsp.mk

# Define folders
BUILD_DIR     	      = $(LOCAL_DIR)build
BIN_DIR       	      = $(LOCAL_DIR)bin
DDR_LIB_DIR   	      = $(CINIT_BASE_DIR)/lib

MODULES_LIB_DIR       = $(CINIT_BASE_DIR)/modules
LIBRARY_DIR           = $(CINIT_BASE_DIR)/library


LIB_DIR_LIST  	= $(DDR_LIB_DIR)

# Define target binary name
BIN := $(BIN_DIR)/cinit$(PROG_EXT)


LIB_DDRCTL_NAME = cinit
LIB_DDRCTL      := $(DDR_LIB_DIR)/lib$(LIB_DDRCTL_NAME).a


STD_LIBS_NAMES   := $(LIB_DDRCTL_NAME)
STD_LIBS_INCLUDE := $(foreach lib,$(STD_LIBS_NAMES),-l$(lib))
STD_LIBS         := $(LIB_DDRCTL)


# Tell the linker where to search for libraries with -L
STD_LDFLAGS  = $(LDFLAGS)
STD_LDFLAGS += $(foreach dir,$(LIB_DIR_LIST),-L$(dir))
STD_LDFLAGS += -Xlinker --start-group $(STD_LIBS_INCLUDE) -Xlinker --end-group -lm

# Add all needed included folders
INCL_DIR += \
	$(LOCAL_DIR)/include                     \
	$(MODULES_LIB_DIR)/core/include          \
	$(MODULES_LIB_DIR)/verification/include  \
	$(MODULES_LIB_DIR)/physetup/include

# Add included folders to compiler options
STD_CFLAGS  = $(CFLAGS)
STD_CFLAGS += -DSTD_ALONE
STD_CFLAGS +=  $(foreach dir,$(INCL_DIR),-I$(dir))


# Define source file(s) to compile
SRC_FILES := $(notdir $(wildcard $(LOCAL_DIR)/src/*.c))

# Source search paths
VPATH := $(LOCAL_DIR)/src

OBJS := $(patsubst %.c,$(BUILD_DIR)/%.o,$(notdir $(SRC_FILES)))

##############################################################################
# Targets
##############################################################################
.PHONY : all clean help debug
all : $(BIN)

debug :
	@echo "$(MAKE_LOG_ID)CINIT_PLATFORM  = $(CINIT_PLATFORM)"
	@echo "$(MAKE_LOG_ID)PROTOCOL        = $(PROTOCOL)"
	@echo "$(MAKE_LOG_ID)BIN             = $(BIN)"
	@echo "$(MAKE_LOG_ID)CFLAGS          = $(CFLAGS)"

help :
	@echo -e 'Usage:'
	@echo -e '    make           - builds standalone app'
	@echo -e '    make clean     - deletes standalone bin and objects'
	@echo -e '    make clean-all - deletes all generated files'
	@echo -e '    make help      - prints this help'

clean:
	$(VERBOSE)$(RM) $(BIN) $(OBJS) *.log core* *.seq

clean-all: clean
	$(VERBOSE)$(MAKE) -C $(CINIT_BASE_DIR) clean CINIT_PLATFORM=$(CINIT_PLATFORM) STATIC_LIB=1

$(BUILD_DIR)/%.o : %.c
	@echo "$(MAKE_LOG_ID)Compiling $(<F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(CC) $(STD_CFLAGS) -c -o $@ $<

$(BIN): $(STD_LIBS) $(OBJS)
	@echo "$(MAKE_LOG_ID)Linking binary: $(@F)"
	$(VERBOSE)$(MKDIR) $(@D)
	$(VERBOSE)$(LD) $(OBJS) $(STD_LDFLAGS) $(STD_CFLAGS) -o $@

$(LIB_DDRCTL):
	@echo "$(MAKE_LOG_ID)Building DDRCTRL SW lib"
	$(VERBOSE)$(MAKE) -C $(CINIT_BASE_DIR) $(LIB_DDRCTL) CINIT_PLATFORM=$(CINIT_PLATFORM) \
			STATIC_LIB=1 LINK_PHYINT=0 USE_KCONFIG_DEFINITIONS=1

