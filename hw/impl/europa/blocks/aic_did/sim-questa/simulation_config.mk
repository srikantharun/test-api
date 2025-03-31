DFT = 0

# Configuration for the IP
IP_NAME            = aic_did_p
TOP_LEVEL_MODULES  = aic_did_p
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
