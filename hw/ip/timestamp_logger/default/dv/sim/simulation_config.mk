# Configuration for the IP
IP_NAME            = timestamp_logger
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = .
UVM                = 1
TESTNAME           = timestamp_logger_internal_sanity_test
SEED               = 1

REGRESS_VERIFSDK_PLATFORM = uvm.HW_IP_TIMESTAMP_LOGGER_DEFAULT_DV_SIM
REGRESS_VERIFSDK_LABEL   ?= HW_IP_TIMESTAMP_LOGGER_TEST

# Design Specific
override GLOBAL_DEFINES += +define+DUT=timestamp_logger
override GLOBAL_DEFINES += +define+NUM_GROUPS=timestamp_logger_aic_pkg::TimeLogNumGroups
override GLOBAL_DEFINES += +define+DW=aic_common_pkg::AIC_LT_AXI_DATA_WIDTH
override GLOBAL_DEFINES += +define+AW=aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH
override GLOBAL_DEFINES += +define+SIDW=aic_infra_pkg::AIC_INFRA_CONFIG_AXI_S_IDW
override GLOBAL_DEFINES += +define+MIDW=aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH
override GLOBAL_DEFINES += +define+GROUP_MSG_WIDTH=timestamp_logger_aic_pkg::TimeLogGroupMsgWidth
override GLOBAL_DEFINES += +define+GROUP_FIFO_DEPTH=timestamp_logger_aic_pkg::TimeLogGroupFifoDepth
override GLOBAL_DEFINES += +define+TIMESTAMP_FIFO_DEPTH=timestamp_logger_aic_pkg::TimeLogTimestampFifoDepth
override GLOBAL_DEFINES += +define+MEM_DEPTH=timestamp_logger_aic_pkg::TimeLogMemDepth
override GLOBAL_DEFINES += +define+USE_MACRO=timestamp_logger_aic_pkg::TimeLogUseMacro
override GLOBAL_DEFINES += +define+CSR_ST_ADDR=aipu_addr_map_pkg::AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR_ST_ADDR
override GLOBAL_DEFINES += +define+MEM_ST_ADDR=aipu_addr_map_pkg::AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM_ST_ADDR
override GLOBAL_DEFINES += +define+CSR_END_ADDR=aipu_addr_map_pkg::AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_CSR_END_ADDR
override GLOBAL_DEFINES += +define+MEM_END_ADDR=aipu_addr_map_pkg::AICORE_0_CONFIGURATION_PERIPHERALS_TIMESTAMP_UNIT_MEM_END_ADDR

# SVT
override GLOBAL_DEFINES += +define+UVM_NO_DPI

override GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
override GLOBAL_DEFINES += +define+SYNOPSYS_SV
override GLOBAL_DEFINES += +define+ASSERTIONS_ON
override GLOBAL_DEFINES += +define+UVM
