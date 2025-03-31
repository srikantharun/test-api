# TODO: This was automatically generated, adaptions will need to be made
DFT = 1

# Configuration for the IP
IP_NAME            = pcie_p
TOP_LEVEL_MODULES  = pcie_p

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/dft
BENDER_TARGETS_EXT = dft asic sf5a

# Custom compile configuration

# Suppress errors in PCIE CTRL IP (non-fixable but suppresable): 
# Enum type mismatch between operands of '==' expression.
VSIM_VLOG_OPTS += -suppress 2577
# An enum variable 'x' of type 'y' may only be assigned the same enum typed variable or one of its values.
VSIM_VLOG_OPTS += -suppress 8386
# Variable 'x' driven in an combinational block, may not be driven by any other process.
VSIM_VOPT_OPTS += -suppress 7033
# Variable 'x' driven in an always_ff block, may not be driven by any other process.
VSIM_VOPT_OPTS += -suppress 7061
# Suppress errors in PCIE PHY IP (non-fixable but suppresable): 
# Illegal space between ` and compiler directive or macro name.
VSIM_VLOG_OPTS += -suppress 13483

# VSIM_VCOM_OPTS  =
# VSIM_ELAB_OPTS  =

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration

PATTERN_NAME =
DFT_TEST_NAME = 

export PATTERN_NAME
