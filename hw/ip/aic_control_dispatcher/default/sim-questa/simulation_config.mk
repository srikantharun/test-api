# TODO: This was automatically generated, adaptions will need to be made

# Configuration for the IP
IP_NAME             = aic_cd
TOP_LEVEL_MODULES   = aic_cd
BENDER_MANI_LOC     = $(MAKEFILE_DIR)/../rtl
BENDER_TARGETS_EXT  += asic
BENDER_TARGETS_EXT  += sf5a

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
# (vsim-3999): enum to logig assignment, used as the default axi types have enums, the simple axi demux deos not
# VSIM_ELAB_OPTS += -suppress 3999
