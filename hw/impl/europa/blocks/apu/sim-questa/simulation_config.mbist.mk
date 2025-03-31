# TODO: This was automatically generated, adaptions will need to be made
DFT = 1

# Configuration for the IP
IP_NAME            = apu
TOP_LEVEL_MODULES  = TB

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/dft_tb
BENDER_TARGETS_EXT = dft asic sf5a

# Custom compile configuration

# VSIM_VLOG_OPTS  =
# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
# VSIM_ELAB_OPTS  =

# VSIM run configuration

VSIM_RUN_OPTS += +NEWPATH=$(realpath $(dir $(MAKEFILE_DIR)/../dv/dft_tb))

# VSIM usage configuration

DFT_TEST_NAME = _$(PATTERN_NAME)

