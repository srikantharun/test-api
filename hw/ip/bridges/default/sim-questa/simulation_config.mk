# Configuration for the IP
IP_NAME            = bridges
TOP_LEVEL_MODULES  = axe_jtag_to_apb
TOP_LEVEL_MODULES += axe_ahb_to_apb

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

VSIM_ERROR_ON_DANGEROUS_WARNING = 1

# Custom compile configuration

# VSIM_VLOG_OPTS  =
# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
# VSIM_ELAB_OPTS  =

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration
