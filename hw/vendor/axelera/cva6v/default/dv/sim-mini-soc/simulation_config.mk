# Configuration for the IP
IP_NAME            = ai_core_cva6v
TOP_LEVEL_MODULES  = hdl_top

BENDER_MANI_LOC := $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/mini_soc
TESTNAME ?= cva6v_oss_riscv_arch_rv64i_m-add-01
ELF      ?= ${REPO_ROOT}/hw/vendor/axelera/cva6v/default/dv/deps/tests/build/riscv-arch-test/riscv-test-suite/rv64i_m/I/src/add-01
SEED     ?= 1

# Enable or disable stripping disassembly logs (default: 1)
STRIP_DISASSEMBLY ?= 0  # Set to 0 to disable stripping

# SIM COMPILE
DPI_C_SRC    += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c/dpi_memory.cc
DPI_C_SRC    += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c/dummy.cc
DPI_C_INCDIR += $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/c

SV_LIBS      += -sv_lib $(SPIKE_HOME)/lib/libriscv

GLOBAL_DEFINES += +define+TARGET_VERIF
GLOBAL_DEFINES += +define+VERIFICATION_ENABLE_CVA6V_PROBES

ifeq ("$(DEBUG)", "1")
  GLOBAL_DEFINES += +define+ADD_DUMP_IF
endif
ifeq ("$(GUI)", "1")
  GLOBAL_DEFINES += +define+ADD_DUMP_IF
endif

# SIM RUN
PLUSARGS_COMMON  += +elf_file=$(ELF)
PLUSARGS_COMMON  += +tohost_addr=2000001000
SIM_RUN_TIME_MINUTES = 240

########################################
# RAG (Random Assembly Generator)
########################################
RAG_DIR := $(GIT_REPO)/hw/vendor/axelera/cva6v/default/dv/deps/rag
RAG_BUILD ?= 0
RAG_GENERATE ?= 0
RAG_LIST ?= 0

include $(RAG_DIR)/rag.mk

ifeq ($(RAG_BUILD), 1)
RUN_VSIM_PREREQUISITES += rag_build
endif
ifeq ($(RAG_GENERATE), 1)
RUN_VSIM_PREREQUISITES += rag_generate
endif
CLEAN_PREREQUISITES += rag_clean # Makefile format mandates clean_*
CLEAN_PREREQUISITES += rag_clean_outdir

REGRESS_VERIFSDK_PLATFORM=cva6v.MINI_SOC

# Rules to compile and clean Open Souce Testsuites & directed assemblies
include $(MAKEFILE_DIR)/../cva6v_ax_asm_config.mk
include $(MAKEFILE_DIR)/../cva6v_oss_config.mk

# Rules to Run spike
RUN_VSIM_POSTREQUISITES += compare_trace_vsim
RUN_VCS_POSTREQUISITES  += compare_trace_vcs
include $(MAKEFILE_DIR)/../cva6v_spike_config.mk
