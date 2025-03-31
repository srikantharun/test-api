# TODO: This was automatically generated, adaptions will need to be made
DFT = 1

# Configuration for the IP
IP_NAME            = dcd_p
TOP_LEVEL_MODULES  = dcd_p

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/dft
BENDER_TARGETS_EXT = dft asic sf5a

# Custom compile configuration

# vlog-2986: The hierarchical reference 'module.something' is not legal in a constant expression context.VSIM_VLOG_OPTS += -suppress 2986
VSIM_VLOG_OPTS += -suppress 2986

# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
# VSIM_ELAB_OPTS  =

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration

PATTERN_NAME =
DFT_TEST_NAME = 

export PATTERN_NAME
