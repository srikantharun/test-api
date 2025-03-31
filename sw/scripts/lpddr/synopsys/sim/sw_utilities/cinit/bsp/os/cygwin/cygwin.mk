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


# Utilities
RM    := rm -Rf
CP    := cp
MKDIR := mkdir -p
CHMOD := chmod 755

PERL=perl
PYTHON=python

# Compiler Options
CFLAGS += -m32
CFLAGS += -I$(CINIT_BASE_DIR)/bsp/os/cygwin/include

# Linker Options
LDFLAGS +=


# Output extentions
PROG_EXT = .exe
SHARED_EXT = .dll

# Export all variables
export
