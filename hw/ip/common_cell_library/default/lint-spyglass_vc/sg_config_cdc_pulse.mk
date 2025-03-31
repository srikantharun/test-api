# Configuration
export IP_NAME     ?= axe_ccl_cdc_pulse
BENDER_MANI_LOC_RTL?= $(MAKEFILE_DIR)/../rtl
BENDER_TARGETS 	   += -t rtl -t asic -t sf5a -t synthesis -D SYNTHESIS
