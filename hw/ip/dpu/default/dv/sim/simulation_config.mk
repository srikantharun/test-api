# Configuration
IP_NAME            = dpu
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

TESTNAME     ?= dpu_register_test
SEED         ?= 1
UVM          ?= 1

SIM_COMPILE_TIME_MINUTES ?= 20

# Design Specific
GLOBAL_DEFINES += +define+AIC_DP_CMD_GEN_COMMAND_DEPTH=1024

GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
GLOBAL_DEFINES += +define+AXI_VIP
GLOBAL_DEFINES += +define+SYNOPSYS_SV
GLOBAL_DEFINES += +define+ASSERTIONS_ON
GLOBAL_DEFINES += +define+UVM
GLOBAL_DEFINES += +define+UVM_HDL_MAX_WIDTH=2048

# New for bender, as svt.uvm.pkg includes uvm pkg definition
GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=36
GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=512
GLOBAL_DEFINES += +define+SVT_AXI_MAX_TDATA_WIDTH=2048
GLOBAL_DEFINES += +define+SVT_AXI_MAX_BURST_LENGTH_WIDTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2
GLOBAL_DEFINES += +define+SVT_AXI_MAX_WRITE_RESP_REORDERING_DEPTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_STREAM_BURST_LENGTH=262144
GLOBAL_DEFINES += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_MESSAGING
GLOBAL_DEFINES += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_DATA_MESSAGING
GLOBAL_DEFINES += +define+SVT_MEM_ENABLE_INTERNAL_MESSAGING
GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY

GLOBAL_DEFINES += +define+DPU_CSR_RAL

VCS_VLOGAN_OPTS_EXT += -xlrm floating_pnt_constraint
VCS_VLOGAN_OPTS_EXT += -ntb_opts uvm-1.2

VCS_ELAB_OPTS_EXT += -ntb_opts uvm-1.2
VCS_ELAB_OPTS_EXT += -xlrm floating_pnt_constraint
VCS_ELAB_OPTS_EXT += -debug_access+all 

##ifeq ($(TESTNAME), $(filter $(TESTNAME),  dpu_mv_bypass_test \
##																				  dpu_register_test \
##																					dpu_sanity_test \
##																					dpu_init_cmd_all_inst_directed_test \
##																					dpu_invalid_access_test \
##																					dpu_axi_b2b_test \
##																					dpu_all_instr_exhaustive_test ))
##  
##  GLOBAL_DEFINES += +define+UVM_NO_DPI
##endif

#Waiting more cycles because in the parameter it only waits for 16 cycles
#GLOBAL_DEFINES += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.AWREADY_MAXWAITS=1000
#GLOBAL_DEFINES += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.ARREADY_MAXWAITS=1000
#GLOBAL_DEFINES += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.WREADY_MAXWAITS=1000
#GLOBAL_DEFINES += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.BREADY_MAXWAITS=1000
#GLOBAL_DEFINES += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.RREADY_MAXWAITS=1000

