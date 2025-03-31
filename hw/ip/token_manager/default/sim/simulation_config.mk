# Configuration
IP_NAME            = tkn_mng
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/tb
BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

TESTNAME     ?= tkn_mng_base_test
SEED         ?= 1
UVM          ?= 1
# UVM options
override GLOBAL_DEFINES += +define+UVM_NO_DPI
override GLOBAL_DEFINES += +define+UVM_NO_DEPRECATED
override GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING


override GLOBAL_DEFINES += +define+UVM

override REGRESS_VERIFSDK_PLATFORM = uvm.HW_IP_TKN_MNG_DEFAULT_DV_SIM
