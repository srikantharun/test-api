# TODO: This was automatically generated, adaptions will need to be made
DFT = 0

# Configuration for the IP
IP_NAME            = aic_infra_p
TOP_LEVEL_MODULES  = aic_infra_p

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

# Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
VSIM_VOPT_OPTS_EXT += -access=rw+/.
VSIM_ELAB_OPTS_EXT += -suppress 8760

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
