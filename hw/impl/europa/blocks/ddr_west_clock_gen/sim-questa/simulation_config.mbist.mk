# TODO: This was automatically generated, adaptions will need to be made
DFT = 1

# Configuration for the IP
IP_NAME            = ddr_west_clock_gen_p
TOP_LEVEL_MODULES  = TB

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/dft_tb
BENDER_TARGETS_EXT = dft asic sf5a

DFT_TEST_NAME = _$(PATTERN_NAME)

