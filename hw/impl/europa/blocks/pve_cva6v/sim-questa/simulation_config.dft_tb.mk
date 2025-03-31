# TODO: This was automatically generated, adaptions will need to be made
DFT = 1

# Configuration for the IP
IP_NAME            = pve_cva6v
TOP_LEVEL_MODULES  = TB

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/dft_tb
BENDER_TARGETS_EXT = dft asic sf5a

# Enable DFT testbench mode
DFT         = 1
DFT_TB_ROOT = $(MAKEFILE_DIR)/../dv/dft_tb
VSIM_ELAB_OPTS_EXT += -suppress 8760

