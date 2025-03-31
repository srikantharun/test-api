

#############################################
# Add VCS analyse options for ai_core
#############################################
# Provide the location for the bender manifest
IP_NAME            = aic_ls
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC = $(MAKEFILE_DIR)/../rtl

TESTNAME     ?= aic_ls_base_test
SEED         ?= 1
UVM          ?= 1

## Setting compilation time-out
SIM_COMPILE_TIME_MINUTES ?= 20

GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
GLOBAL_DEFINES += +define+UVM_DEPRECATED_STARTING_PHASE
GLOBAL_DEFINES += +define+AXI_VIP
GLOBAL_DEFINES += +define+SYNOPSYS_SV
GLOBAL_DEFINES += +define+ASSERTIONS_ON
GLOBAL_DEFINES += +define+UVM
# GLOBAL_DEFINES += +define+UVM_HDL_NO_DPI

# Address defines
GLOBAL_DEFINES += +define+M_IFD0_BASE_ADDR=33554432 #'h200_0000
GLOBAL_DEFINES += +define+M_IFD1_BASE_ADDR=33619968 #'h201_0000
GLOBAL_DEFINES += +define+M_IFD2_BASE_ADDR=33685504 #'h202_0000
GLOBAL_DEFINES += +define+M_IFDW_BASE_ADDR=33751040 #'h203_0000
GLOBAL_DEFINES += +define+M_ODR_BASE_ADDR=33816576 #'h204_0000
GLOBAL_DEFINES += +define+D_IFD0_BASE_ADDR=33882112 #'h205_0000
GLOBAL_DEFINES += +define+D_IFD1_BASE_ADDR=33947648 #'h206_0000
GLOBAL_DEFINES += +define+D_ODR_BASE_ADDR=34013184 #'h207_0000
GLOBAL_DEFINES += +define+TOKEN_BASE_ADDR=34078720 #'h208_0000
GLOBAL_DEFINES += +define+TRACE_UNIT_BASE_ADDR=34111488  #'h208_8000

GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=40
GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=512
GLOBAL_DEFINES += +define+SVT_AXI_MAX_TDATA_WIDTH=512
GLOBAL_DEFINES += +define+SVT_AXI_MAX_BURST_LENGTH_WIDTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2
GLOBAL_DEFINES += +define+SVT_AXI_MAX_WRITE_RESP_REORDERING_DEPTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_STREAM_BURST_LENGTH=262144
GLOBAL_DEFINES += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_MESSAGING
GLOBAL_DEFINES += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_DATA_MESSAGING
GLOBAL_DEFINES += +define+SVT_MEM_ENABLE_INTERNAL_MESSAGING
GLOBAL_DEFINES += +define+SVT_AXI_ACE_SNPS_INTERNAL_SYSTEM_MONITOR_USE_MASTER_SLAVE_AGENT_CONNECTION
#GLOBAL_DEFINES += +define+SVT_MEM_LOGIC_DATA # so that axi txn data is of type logic and not bit

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

