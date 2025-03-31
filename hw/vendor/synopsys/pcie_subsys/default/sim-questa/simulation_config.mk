# TODO: This was automatically generated, adaptions will need to be made

# Configuration for the IP
IP_NAME            = DWC_pcie_subsystem
TOP_LEVEL_MODULES  = DWC_pcie_subsystem

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

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
DFT_TEST_NAME =
