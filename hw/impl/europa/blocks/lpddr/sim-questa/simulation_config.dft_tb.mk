# Configuration for the IP
IP_NAME            = lpddr
TOP_LEVEL_MODULES  = TB

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/dft_tb
BENDER_TARGETS_EXT = dft asic sf5a

# Enable DFT testbench mode
DFT         = 1
DFT_TB_ROOT = $(MAKEFILE_DIR)/../dv/dft_tb

# Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
VSIM_VOPT_OPTS += -access=rw+/.
VSIM_ELAB_OPTS += -suppress 8760
