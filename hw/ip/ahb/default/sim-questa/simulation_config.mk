# Configuration for the IP
IP_NAME            = axe_ahb_sanity_compile
TOP_LEVEL_MODULES  = axe_ahb_mux
TOP_LEVEL_MODULES += axe_ahb_demux
TOP_LEVEL_MODULES += axe_ahb_manager
TOP_LEVEL_MODULES += axe_ahb_stall

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

# Custom compile configuration

# VSIM_VLOG_OPTS  =
# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
# VSIM_ELAB_OPTS  =

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration
