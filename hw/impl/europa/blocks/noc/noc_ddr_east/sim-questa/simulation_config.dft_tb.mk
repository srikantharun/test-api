# Configuration for the IP
IP_NAME            = noc_ddr_east
TOP_LEVEL_MODULES  = TB

#TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/dft_tb
BENDER_TARGETS_EXT = dft asic sf5a

# Enable dft testbench mode
DFT=1
DFT_TB_ROOT=$(MAKEFILE_DIR)/../dv/dft_tb

