#############################################
# Add VCS analyse options for sys_ctrl
#############################################
# Configuration
IP_NAME            = sys_spm_p
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/uvm_env/tb


TESTNAME     ?= sys_spm_multi_seq_test
SEED         ?= 1
UVM          ?= 1
# UVM options
override GLOBAL_DEFINES += +define+UVM_NO_DPI
override GLOBAL_DEFINES += +define+UVM_NO_DEPRECATED
override GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY
override GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING

# Include the AXI_VIP defines
override GLOBAL_DEFINES += +define+AXI_VIP
override GLOBAL_DEFINES += +define+SYNOPSYS_SV
# SVT configuration defines
override GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
override GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER
override GLOBAL_DEFINES += +define+UVM
override GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY


