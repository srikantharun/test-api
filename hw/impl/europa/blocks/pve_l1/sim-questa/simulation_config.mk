# TODO: This was automatically generated, adaptions will need to be made
DFT = 0

# Configuration for the IP
IP_NAME            = pve_l1_p
TOP_LEVEL_MODULES  = pve_l1_p

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

# Custom compile configuration
# VSIM_VLOG_OPTS  =
# VSIM_VCOM_OPTS  =
# VSIM_ELAB_OPTS  =

# Suppress warning: Missing connection for port xx_o'. Default value(if given) will not be used due to explicit empty named port connection.
VSIM_VOPT_OPTS_EXT += -suppress 2871

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration
DFT_TEST_NAME =

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
