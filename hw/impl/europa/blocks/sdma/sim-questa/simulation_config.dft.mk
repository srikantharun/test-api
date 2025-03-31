# TODO: This was automatically generated, adaptions will need to be made
DFT = 1

# Configuration for the IP
IP_NAME            = sdma_p
TOP_LEVEL_MODULES  = sdma_p

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/dft
BENDER_TARGETS_EXT = dft asic sf5a

# Custom compile configuration

# Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
#VSIM_VOPT_OPTS_EXT += -access=rw+/.

# Suppress sformatf error: $sformatf : Argument number (...) has an invalid format width.
VSIM_ELAB_OPTS_EXT += -suppress 8760
# Suppress buggy Illegal assignment to type 'enum warning
VSIM_ELAB_OPTS_EXT += -suppress 8386

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration

PATTERN_NAME =
DFT_TEST_NAME = 

export PATTERN_NAME
