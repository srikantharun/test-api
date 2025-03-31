GIT_REPO := $(shell git rev-parse --show-toplevel)
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre.mk

########################################
########################################
##@ Simulation setup:
########################################

##% SIM_FLOW_CONFIG @@ ="simulation_config.mk" @@ Specify configuration options
SIM_FLOW_CONFIG ?= simulation_config.mk
-include $(SIM_FLOW_CONFIG)

########################################
##@ Validate the configuration:
########################################
$(call check_defined, BENDER_MANI_LOC, add to your configuration file)
$(call check_defined, IP_NAME, specify the name of the IP in SIM_FLOW_CONFIG)
$(call check_defined, TOP_LEVEL_MODULES, specify all top-level modules SIM_FLOW_CONFIG)

########################################
##@ Common Simulator variables (keep short to make commandline simple):
########################################

##% TIMESCALE @@ 1ns/1ps @@ Default timescale
TIMESCALE ?= 1ns/1ps

##% GLOBAL_DEFINES @@  @@ Additional defines applied to all compilations
override GLOBAL_DEFINES +=

##% PLUSARGS @@  @@ Additional +plusargs to simulation
override PLUSARGS +=

##% SV_LIBS @@  @@ Additional sv_libs to simulation (DPI code libraries)
SV_LIBS +=

##% UVM @@ {(0), 1 } @@ Automatically build for UVM
UVM       ?= 0
ifneq ("$(UVM)", "0")
override GLOBAL_DEFINES += +define+UVM_NO_DEPRECATED
endif

##% DFT @@ {(0), 1 } @@ Enable DFT testbench mode
DFT       ?= 0

##% GUI @@ {(0), 1 } @@ Enable GUI
GUI       ?= 0

##% COVERAGE @@ {(0), 1 } @@ Enable coverage
COVERAGE ?= 0

##% XPROP @@ {(0), 1 } @@ Enable x-propagation
XPROP      ?= 0
XPROP_PATH ?=

##% COVERAGE_ARCHIVE_LOC @@  @@ Archive coverage to fixed location at end of regression
COVERAGE_ARCHIVE_LOC ?=

##% PROFILE @@ {(0), 1 } @@ Enable profiling
PROFILE ?= 0

##% DEBUG @@ {(0), 1 } @@ Enable debug (including waves)
ifeq ("$(GUI)", "0")
DEBUG     ?= 0
else
DEBUG     ?= 1
GRID_CMD  += --x11
endif

##% NODEPS @@ {(0), 1 } @@ No dependencies - rerun last compile
NODEPS    ?= 0

##% SIM_COMPILE_TIME_MINUTES @@ {(30), N} @@ Simulation compile time in minutes
SIM_COMPILE_TIME_MINUTES ?= 30

##% SIM_RUN_TIME_MINUTES @@ {(60(batch), 720(gui)), N} @@ Simulation run time in minutes
ifeq ("$(GUI)", "0")
SIM_RUN_TIME_MINUTES ?= 60
else
SIM_RUN_TIME_MINUTES ?= 720
endif

##% SIM_COVERAGE_TIME_MINUTES @@ {(60), N} @@ Coverage collection time in minutes
SIM_COVERAGE_TIME_MINUTES ?= 60

##% DPI_C_SRC @@ @@ Source files to include into compilation of the shared library dpi.so
DPI_C_SRC ?= $(GIT_REPO)/hw/dv/common/c/axe_csv.cc

##% DPI_C_OPTS @@ @@ Additional switches to pass to g++ during the compilation of dpi.so
DPI_C_OPTS ?=

##% DPI_C_INCDIR @@ @@ Include directories to pass to g++ during the compilation of dpi.so
DPI_C_INCDIR ?=

##% DPI_C_SRC @@ @@ Source files to include into compilation of the shared library dpi.so
DPI_C_SRC ?=

##% DPI_C_OPTS @@ @@ Additional switches to pass to g++ during the compilation of dpi.so
DPI_C_OPTS ?=

##% DPI_C_INCDIR @@ @@ Include directories to pass to g++ during the compilation of dpi.so
DPI_C_INCDIR ?=

##% VHDL_STD_NOWARNINGS @@ {(0), 1 } @@ Enable/Disable StdArithNoWarnings and NumericStdNoWarnings
VHDL_STD_NOWARNINGS ?= 0

########################################
##@ Simulation run variables:
########################################

##% TESTNAME @@ $(IP_NAME) @@ Name of the test to run
TESTNAME     ?= $(IP_NAME)
UVM_TESTNAME ?= $(TESTNAME)

##% UVM_VERBOSITY @@ {UVM_LOW} @@ UVM verbosity level
UVM_VERBOSITY ?= UVM_LOW

##% SEED @@ $(RANDOM_SEED) @@ Seed for the simulation, if not specified a random seed is used
SEED ?= $(RANDOM_SEED)

##% REGRESS_SW_BUILD_DIR @@  @@ Build directory used by verifsdk to build the SW tests during the regression
REGRESS_SW_BUILD_DIR ?= $(MAKEFILE_DIR)/build_sw

.PHONY: $(REGRESS_SW_BUILD_DIR)
$(REGRESS_SW_BUILD_DIR): ## Create the software build directory
	@# Create the build directory
	mkdir -p $@

##% REGRESS_VERIFSDK_PLATFORM @@  @@ Platform used by verifsdk during the regression
REGRESS_VERIFSDK_PLATFORM ?=

##% REGRESS_VERIFSDK_LABEL @@  @@ Label used by verifsdk during the regression
REGRESS_VERIFSDK_LABEL ?=

##% REGRESS_VERIFSDK_TEST @@  @@ Test used by verifsdk when running a single test
REGRESS_VERIFSDK_TEST ?=

##% REGRESS_VERIFSDK_ARGS @@  @@ Additional arguments passed to verifsdk during the regression
REGRESS_VERIFSDK_ARGS ?=

##% REGRESS_VERIFSDK_CTEST_ARGS @@  @@ Additional arguments passed to CTest during the regression
REGRESS_VERIFSDK_CTEST_ARGS ?=

##% REGRESS_VERIFSDK_GRID_NUM_CPUS @@  @@ Amount of CPU used for SW compilation
REGRESS_VERIFSDK_GRID_NUM_CPUS ?= 8

##% PRE_SIM_TARGETS @@  @@ User defined pre-simulation targets
PRE_SIM_TARGETS ?=

##% POST_SIM_TARGETS @@  @@ User defined post-simulation targets
POST_SIM_TARGETS ?=

##% PRESERVE_SIMS @@  @@ Preserve old simulations runs
PRESERVE_SIMS ?= 0

########################################
## Bender setup:
########################################
$(call check_undefined, BENDER_TARGETS, Internal BENDER_TARGETS should not be externally defined)
BENDER_TARGETS += rtl
BENDER_TARGETS += simulation

########################################
## DFT prerequisites
########################################
ifeq ("$(DFT)","1")
include $(GIT_REPO)/hw/scripts/flow_makefiles/dft_tb.mk
endif

########################################
## Questasim specific
########################################
include $(GIT_REPO)/hw/scripts/flow_makefiles/questasim.mk

########################################
## VCS specific
########################################
include $(GIT_REPO)/hw/scripts/flow_makefiles/vcs.mk

########################################
## Clean targets:
########################################
include $(GIT_REPO)/hw/scripts/flow_makefiles/_post.mk
