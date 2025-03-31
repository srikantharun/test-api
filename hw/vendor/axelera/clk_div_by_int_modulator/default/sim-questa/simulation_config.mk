
# Configuration for the IP
IP_NAME            = clk_div_by_int_modulator
TOP_LEVEL_MODULES  = clk_div_by_int_modulator

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl
# Custom compile configuration

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += simulation
BENDER_TARGETS_EXT += sf5a
