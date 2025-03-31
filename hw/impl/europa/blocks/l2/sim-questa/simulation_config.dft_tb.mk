# Configuration for the IP
IP_NAME            = l2
TOP_LEVEL_MODULES  = TB

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/dft_tb
BENDER_TARGETS_EXT = dft asic sf5a

# Enable DFT testbench mode
DFT         = 1
DFT_TB_ROOT = $(MAKEFILE_DIR)/../dv/dft_tb

