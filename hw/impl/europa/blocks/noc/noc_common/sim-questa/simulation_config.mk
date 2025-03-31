# ==============================================================================
DFT = 0
DFT_TEST_NAME =

# ==============================================================================
IP_NAME            = noc_common_sanity_compile

TOP_LEVEL_MODULES  = noc_common_clk_gater
TOP_LEVEL_MODULES += noc_common_sync_2_stage

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/
BENDER_TARGETS_EXR = "asic sf5a"
