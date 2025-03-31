# TODO: This was automatically generated, adaptions will need to be made

# Configuration for the IP
IP_NAME            = ifd_odr
TOP_LEVEL_MODULES  = ifd odr vtrsp_tb ifd_odr_tb

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/design_tb

# Custom compile configuration

# VSIM_VLOG_OPTS  =
VSIM_VLOG_OPTS_EXT += -suppress 13262,3838,2897
# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
VSIM_ELAB_OPTS  += -suppress 3838

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration
