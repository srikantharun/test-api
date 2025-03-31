# Configuration for the IP
IP_NAME = spike
TOP_LEVEL_MODULES = cva6v_riscv_isacov_module

BENDER_MANI_LOC := .
TESTNAME ?= cva6v_oss_riscv_arch_rv64i_m-add-01
ELF      ?= ${REPO_ROOT}/hw/vendor/axelera/cva6v/default/dv/deps/tests/build/riscv-arch-test/riscv-test-suite/rv64i_m/I/src/add-01
SEED     ?= 2
COVERAGE ?= 1

# Allow optional disassembly stripping (default enabled)
STRIP_DISASSEMBLY ?= 1  # Set to 0 in simulation_config.mk to disable

GLOBAL_DEFINES += +define+VERIFICATION_ENABLE_CVA6V_PROBES

PLUSARGS_COMMON += +CSV_FILENAME=$(SPIKE_RUN_DIR)/inst_cov_dis.log

REGRESS_VERIFSDK_PLATFORM = cva6v.SPIKE_COVERAGE

VSIM_ELAB_OPTS_EXT += -sv_lib $(IMPERAS_HOME)/lib/Linux64/ImperasLib/imperas.com/verification/riscv/1.0/model

ifeq ("$(COVERAGE)", "1")
# do not generate code coverage by default, but only function coverage. Spike is not RTL sim and makes no use of code cov
	VSIM_VOPT_OPTS_COVERAGE =
endif

# Rules to compile and clean Open Souce Testsuites
include $(MAKEFILE_DIR)/../cva6v_oss_config.mk

# Rules to Run spike
include $(MAKEFILE_DIR)/../cva6v_spike_config.mk
