# TODO: This was automatically generated, adaptions will need to be made
DFT = 0

# Configuration for the IP
IP_NAME            = dcd_p
TOP_LEVEL_MODULES  = dcd_p
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

# Custom compile configuration

# vlog-2986: The hierarchical reference 'module.something' is not legal in a constant expression context.VSIM_VLOG_OPTS += -suppress 2986
VSIM_VLOG_OPTS += -suppress 2986

# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
# VSIM_ELAB_OPTS  =

# VSIM run configuration

# VSIM_RUN_OPTS  =

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
