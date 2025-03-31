
# Configuration
IP_NAME            = common_seq_lib
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../tb

TESTNAME     ?= common_seq_lib_smoke_test
SEED         ?= 1
UVM          ?= 1

override GLOBAL_DEFINES += +define+UVM_NO_DPI
override GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
override GLOBAL_DEFINES += +define+AXI_VIP
override GLOBAL_DEFINES += +define+SYNOPSYS_SV
override GLOBAL_DEFINES += +define+ASSERTIONS_ON
override GLOBAL_DEFINES += +define+UVM

# New for bender, as svt.uvm.pkg includes uvm pkg definition
override GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
override GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=64
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=512
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_BURST_LENGTH_WIDTH=8
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_CACHE_WIDTH=4
override GLOBAL_DEFINES += +define+SVT_AXI_CACHE_WIDTH=4
override GLOBAL_DEFINES += +define+SVT_AXI_LOCK_WIDTH=1
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_PROT_WIDTH=3
override GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_WRITE_RESP_REORDERING_DEPTH=8
override GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_NUM_OUTSTANDING_XACT=512
override GLOBAL_DEFINES += +define+SVT_ACE5_ENABLE

