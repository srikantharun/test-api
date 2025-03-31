# Configuration for the IP
IP_NAME            = timestamp_logger
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/design_tb

TOP_LEVEL_MODULES  = timestamp_logger_tb

# VSIM_VLOG_OPTS  =
VSIM_VLOG_OPTS_EXT += -suppress 13262,3838,2897
# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
VSIM_ELAB_OPTS  += -suppress 3838

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration
