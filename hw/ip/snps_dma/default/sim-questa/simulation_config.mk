# TODO: This was automatically generated, adaptions will need to be made

# Configuration for the IP
IP_NAME            = snps_dma
TOP_LEVEL_MODULES  = snps_dma
TOP_LEVEL_MODULES += snps_dma_axe_axi
TOP_LEVEL_MODULES += ht_dma_tb

# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/design_tb

# Custom compile configuration

VSIM_VLOG_OPTS_EXT += -suppress 13262,3838
# VSIM_VCOM_OPTS  =
# VSIM_VOPT_OPTS  =
VSIM_ELAB_OPTS  += -suppress 3838

# VSIM run configuration

# VSIM_RUN_OPTS  =

# VSIM usage configuration
