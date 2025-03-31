# Configuration for the IP
IP_NAME            = axe_apb_sanity_compile
TOP_LEVEL_MODULES  = axe_apb_demux
TOP_LEVEL_MODULES += axe_apb_manager
TOP_LEVEL_MODULES += axe_apb_mux
TOP_LEVEL_MODULES += axe_apb_8to32
TOP_LEVEL_MODULES += axe_apb_cut

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

# Custom compile configuration

override GLOBAL_DEFINES += +define+ASSERTIONS_ON

# VSIM_VLOG_OPTS  =
# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
# VSIM_ELAB_OPTS  =

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration
