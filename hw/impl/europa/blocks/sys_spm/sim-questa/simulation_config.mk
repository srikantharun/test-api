DFT = 0

# Configuration for the IP
IP_NAME            = sys_spm_p
TOP_LEVEL_MODULES  = sys_spm_p

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/
DFT_TEST_NAME =

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
