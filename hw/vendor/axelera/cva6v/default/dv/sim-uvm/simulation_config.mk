# Configuration for the IP
IP_NAME            = ai_core_cva6v
TOP_LEVEL_MODULES  = hdl_top

BENDER_MANI_LOC    = $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/uvm
UVM                = 1
UVM_TESTNAME       = cva6v_base_test
TESTNAME          ?= cva6v_oss_riscv_arch_rv64i_m-add-01
ELF               ?= ${REPO_ROOT}/hw/vendor/axelera/cva6v/default/dv/deps/tests/build/riscv-arch-test/riscv-test-suite/rv64i_m/I/src/add-01
SEED              ?= 1

DPI_C_SRC    += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c/dpi_memory.cc
DPI_C_SRC    += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c/dummy.cc
DPI_C_INCDIR += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c

SV_LIBS      += -sv_lib $(SPIKE_HOME)/lib/libriscv

#GLOBAL_DEFINES += +define+SVT_ACE5_ENABLE #TODO: enable for AXI5
GLOBAL_DEFINES += +define+UVM_NO_DPI
GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=36
GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=512
GLOBAL_DEFINES += +define+SVT_AXI_MAX_BURST_LENGTH_WIDTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2
GLOBAL_DEFINES += +define+SVT_AXI_MAX_WRITE_RESP_REORDERING_DEPTH=8
GLOBAL_DEFINES += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_MESSAGING
GLOBAL_DEFINES += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_DATA_MESSAGING
GLOBAL_DEFINES += +define+SVT_MEM_ENABLE_INTERNAL_MESSAGING
GLOBAL_DEFINES += +define+SVT_AXI_ACE_SNPS_INTERNAL_SYSTEM_MONITOR_USE_MASTER_SLAVE_AGENT_CONNECTION
GLOBAL_DEFINES += +define+SVT_MEM_LOGIC_DATA # so that axi txn data is of type logic and not bit
GLOBAL_DEFINES += +define+TARGET_VERIF
GLOBAL_DEFINES += +define+VERIFICATION_ENABLE_CVA6V_PROBES

ifeq ("$(DEBUG)", "1")
  GLOBAL_DEFINES += +define+ADD_DUMP_IF
endif

# SIM RUN
PLUSARGS_COMMON  += +elf_file=$(ELF)
PLUSARGS_COMMON  += +tohost_addr=2000001000
SIM_RUN_TIME_MINUTES = 120

REGRESS_VERIFSDK_PLATFORM=cva6v.UVM

# Rules to compile and clean Open Souce Testsuites
include $(MAKEFILE_DIR)/../cva6v_oss_config.mk

# Rules to Run spike
RUN_VSIM_POSTREQUISITES += compare_trace_vsim
RUN_VCS_POSTREQUISITES  += compare_trace_vcs
include $(MAKEFILE_DIR)/../cva6v_spike_config.mk

