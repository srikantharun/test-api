DFT = 0
DESIGN_TB ?= 0

# Configuration for the IP
IP_NAME            = soc_mgmt_p

ifeq ("$(DESIGN_TB)", "0")
TOP_LEVEL_MODULES  = soc_mgmt_p
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a
else
TOP_LEVEL_MODULES  = soc_mgmt_tb
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/design_tb
endif

VSIM_VLOG_OPTS += +nospecify

VSIM_ERROR_ON_DANGEROUS_WARNING = 1

override GLOBAL_DEFINES += +define+SOTP_SET_PWR_ON=3

#override GLOBAL_DEFINES += +define+POWER_PINS
