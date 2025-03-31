[10:01] Leonidas Katselas
# TODO: This was automatically generated, adaptions will need to be made

DFT = 0
 
# Configuration for the IP

IP_NAME            = ddr_west_clock_gen_p

TOP_LEVEL_MODULES  = ddr_west_clock_gen_p
 
# TODO: Set the correct directory which contains the Bender.yml with the TOP_LEVEL_MODULES

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/design_tb
 
BENDER_TARGETS_EXT  = asic

BENDER_TARGETS_EXT += sf5a
 
# Custom compile configuration

UVM          ?= 1
 
# VSIM run configuration

override GLOBAL_DEFINES += +define+UVM_NO_DPI

override GLOBAL_DEFINES += +define+UVM_NO_DEPRECATED

override GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY

override GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
 
# SVT configuration defines

override GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE

override GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER

override GLOBAL_DEFINES += +define+UVM

override GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY

#override GLOBAL_DEFINES += +define+POWER_PINS
 
# VSIM_RUN_OPTS  =
 
# VSIM usage configuration

DFT_TEST_NAME =
 
VSIM_ERROR_ON_DANGEROUS_WARNING = 1





























