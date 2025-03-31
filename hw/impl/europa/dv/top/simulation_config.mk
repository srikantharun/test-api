###################################################################
# TB config
###################################################################
BENDER_MANI_LOC := .
IP_NAME := europa_top
TOP_LEVEL_MODULES := sim_top
SEED := 1

UVM ?= 1
TESTNAME ?= fw_base_test

TOP_PLATFORM_NAME := top

# uart_xactor uses DPI interactively communicate with the UART in a terminal,
# not needed in simulation
GLOBAL_DEFINES += +define+UART_XACTOR_NO_DPI
GLOBAL_DEFINES += +define+VERIFICATION_ENABLE_CVA6V_PROBES
GLOBAL_DEFINES += +define+TU_PLL0519A01_LN05LPE_4007002_FAST_MODEL
GLOBAL_DEFINES += +define+DV_AXI_RAM_UNBOUNDED

# EMMC softmodel config
GLOBAL_DEFINES += +define+sim
GLOBAL_DEFINES += +define+emmc_flexmem
# Enable debug messages
GLOBAL_DEFINES += +define+emmc_cmd_message_enable
GLOBAL_DEFINES += +define+emmc_state_message_enable

# SPI softmodel
SPI_FLASH_MODEL := s25fs512s
GLOBAL_DEFINES += +define+sim
GLOBAL_DEFINES += +define+$(SPI_FLASH_MODEL)
ENABLE_SOFTMODELS ?= 1
ifeq ("$(ENABLE_SOFTMODELS)", "1")
BENDER_TARGETS_EXT += spinor_$(SPI_FLASH_MODEL) emmc_softmodel
endif
PLUSARGS += +SPINOR_REGFILE=$(REPO_ROOT)/hw/dv/spinor_softmodel/sfdp_$(SPI_FLASH_MODEL).hex
PLUSARGS += +s25fs_cmd_message_enable

GLOBAL_DEFINES += +define+LPDDR_P_GRAPH_0_STUB
GLOBAL_DEFINES += +define+LPDDR_P_GRAPH_1_STUB
GLOBAL_DEFINES += +define+LPDDR_P_GRAPH_2_STUB
GLOBAL_DEFINES += +define+LPDDR_P_GRAPH_3_STUB
GLOBAL_DEFINES += +define+LPDDR_P_PPP_0_STUB
GLOBAL_DEFINES += +define+LPDDR_P_PPP_1_STUB
GLOBAL_DEFINES += +define+LPDDR_P_PPP_2_STUB
GLOBAL_DEFINES += +define+LPDDR_P_PPP_3_STUB

#give some time for OTP model to power up
GLOBAL_DEFINES += +define+SOTP_SET_PWR_ON=3

#allow the tests to take more that one hour
SIM_RUN_TIME_MINUTES=480


REGRESS_VERIFSDK_PLATFORM=SIM_TOP
