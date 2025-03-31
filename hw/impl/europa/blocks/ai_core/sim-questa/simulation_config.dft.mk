# Configuration for the IP
IP_NAME            = ai_core_p
TOP_LEVEL_MODULES  = ai_core_p

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/dft
BENDER_TARGETS_EXT = dft asic sf5a

# Custom compile configuration

# VSIM_VLOG_OPTS  =
# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
# VSIM_ELAB_OPTS  =
# Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
VSIM_VOPT_OPTS_EXT += -access=rw+/.
VSIM_ELAB_OPTS_EXT += -suppress 8760

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration

PATTERN_NAME =
DFT_TEST_NAME = 

export PATTERN_NAME
