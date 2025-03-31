# Configuration
IP_NAME            = aic_cd
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

ifdef UVM_TESTNAME
	TESTNAME?=$(UVM_TESTNAME)
else
	TESTNAME?= ai_core_cd_ral_test
endif

SEED         ?= 1
UVM          ?= 1

# Design Specific
#GLOBAL_DEFINES += +define+AIC_DP_CMD_GEN_COMMAND_DEPTH=1024

# UVM configuration
GLOBAL_DEFINES += +define+UVM_NO_DEPRECATED
GLOBAL_DEFINES += +define+UVM_NO_DPI
GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
GLOBAL_DEFINES += +define+UVM_DEPRECATED_STARTING_PHASE
# AXI VIP configuration defines
GLOBAL_DEFINES += +define+AXI_VIP
GLOBAL_DEFINES += +define+SYNOPSYS_SV

# New for bender, as svt.uvm.pkg includes uvm pkg definition
# ToDO: Review these define Params
GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER
GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY  
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=40
GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=64
GLOBAL_DEFINES += +define+SVT_AXI_MAX_TDATA_WIDTH=1664
GLOBAL_DEFINES += +define+SVT_AXI_MAX_BURST_LENGTH_WIDTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2
GLOBAL_DEFINES += +define+SVT_AXI_MAX_WRITE_RESP_REORDERING_DEPTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_STREAM_BURST_LENGTH=262144 # 2**18

## override commons sequence lib defines
GLOBAL_DEFINES += +define+ACD_M_AXI_ID_WIDTH=6 #7
GLOBAL_DEFINES += +define+ACD_M_AXI_ADDR_WIDTH=40
GLOBAL_DEFINES += +define+ACD_M_AXI_DATA_WIDTH=64
GLOBAL_DEFINES += +define+ACD_S_AXI_ID_WIDTH=7 #1
GLOBAL_DEFINES += +define+ACD_S_AXI_ADDR_WIDTH=40
GLOBAL_DEFINES += +define+ACD_S_AXI_DATA_WIDTH=64
### override commons sequence lib defines
#GLOBAL_DEFINES += +define+ID_M_W=`ACD_M_AXI_ID_WIDTH
#GLOBAL_DEFINES += +define+ADDR_M_W=`ACD_M_AXI_ADDR_WIDTH
#GLOBAL_DEFINES += +define+DATA_M_W=`ACD_M_AXI_DATA_WIDTH
#GLOBAL_DEFINES += +define+ID_S_W=`ACD_S_AXI_ID_WIDTH
#GLOBAL_DEFINES += +define+ADDR_S_W=`ACD_S_AXI_ADDR_WIDTH
#GLOBAL_DEFINES += +define+DATA_S_W=`ACD_S_AXI_DATA_WIDTH
### overriden as seen in common_seq_lib_tb_define
#GLOBAL_DEFINES += +define+AXI_DATA_WIDTH=`ACD_M_AXI_DATA_WIDTH 
#GLOBAL_DEFINES += +define+AXI_ID_WIDTH=`ACD_M_AXI_ID_WIDTH
#GLOBAL_DEFINES += +define+AXI_HP_ADDR_WIDTH=`ACD_M_AXI_ADDR_WIDTH

## override commons sequence lib defines
GLOBAL_DEFINES += +define+ID_M_W=7
GLOBAL_DEFINES += +define+ADDR_M_W=40
GLOBAL_DEFINES += +define+DATA_M_W=64
GLOBAL_DEFINES += +define+ID_S_W=1
GLOBAL_DEFINES += +define+ADDR_S_W=40
GLOBAL_DEFINES += +define+DATA_S_W=64
## overriden as seen in common_seq_lib_tb_define
GLOBAL_DEFINES += +define+AXI_ID_WIDTH=7
GLOBAL_DEFINES += +define+AXI_HP_ADDR_WIDTH=40
GLOBAL_DEFINES += +define+AXI_DATA_WIDTH=64

#Enabling assertions
GLOBAL_DEFINES += +define+ASSERTIONS_ON

