# Configuration for the IP

IP_NAME             = europa
TOP_LEVEL_MODULES   = europa

BENDER_MANI_LOC     = $(MAKEFILE_DIR)/../rtl
BENDER_TARGETS_EXT += asic
BENDER_TARGETS_EXT += sf5a

VSIM_VOPT_OPTS_EXT += -access=rw+/.
VSIM_VOPT_OPTS_EXT += -suppress 2241 # NOC port mismatch with other modules, need to fix

VSIM_ELAB_OPTS_EXT += -suppress 8760
VSIM_ELAB_OPTS_EXT += -suppress 8386


VSIM_ERROR_ON_DANGEROUS_WARNING = 1
# vlog-2986: The hierarchical reference 'module.something' is not legal in a constant expression context.VSIM_VLOG_OPTS += -suppress 2986
VSIM_VLOG_OPTS += -suppress 2986
VSIM_VLOG_OPTS += -suppress 2241 # NOC port mismatch with other modules, need to fix

# Suppress errors in PCIE CTRL IP (non-fixable but suppresable):
# Enum type mismatch between operands of '==' expression.
VSIM_VLOG_OPTS_EXT += -suppress 2577
# An enum variable 'x' of type 'y' may only be assigned the same enum typed variable or one of its values.
VSIM_VLOG_OPTS_EXT += -suppress 8386
# Variable 'x' driven in an combinational block, may not be driven by any other process.
VSIM_VOPT_OPTS_EXT += -suppress 7033
# Variable 'x' driven in an always_ff block, may not be driven by any other process.
VSIM_VOPT_OPTS_EXT += -suppress 7061
# Suppress errors in PCIE PHY IP (non-fixable but suppresable):
# Illegal space between ` and compiler directive or macro name.
VSIM_VLOG_OPTS_EXT += -suppress 13483

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
