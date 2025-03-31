GIT_REPO := $(shell git rev-parse --show-toplevel)
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre.mk

########################################
##@ RTL Architect setup:
########################################

RTLA_FLOW ?= elaboration

##% DFT @@ {(0), 1 } @@ Run on DFT-inserted RTL
DFT ?= 0

##% GUI @@ {(0), 1 } @@ Enable GUI
GUI ?= 0

########################################
## Validate the configuration:
########################################


########################################
## Create the build and run directories:
########################################
BUILD_DIR := build_rtl_architect

# Define the directory name using the timestamp
RTLA_RUN_DIR := run_$(TIMESTAMP)
RTLA_EXEC_DIR := $(BUILD_DIR)/$(RTLA_RUN_DIR)

.PHONY: create_run_dir
create_run_dir:
	mkdir -p $(BUILD_DIR)
	# Create the directory
	mkdir -p $(BUILD_DIR)/$(RTLA_RUN_DIR)
	# Print the created directory name
	@echo "Created run directory: $(RTLA_EXEC_DIR)"

########################################
##@ RTL Architect flow (command):
########################################
RTLA_OPTS = ""

ifeq ("$(GUI)", "0")
RTLA_OPTS += -batch
else
GRID_OPTS += --x11
RTLA_OPTS += -gui
endif

GRID_NUM_CPUS = 4
RTLA_CMD ?= $(GRID_CMD) rtl_shell $(RTLA_OPTS)

.PHONY: run_rtla_analyze
run_rtla_analyze: RTLA_FLOW=analyze
run_rtla_analyze: run_rtla ## Run RTL-Architect till the Analyze step

.PHONY: run_rtla_elab
run_rtla_elab: RTLA_FLOW=elaboration
run_rtla_elab: run_rtla ## Run RTL-Architect till the Elaboration step

.PHONY: run_rtla_cond
run_rtla_cond: RTLA_FLOW=conditioning
run_rtla_cond: run_rtla ## Run RTL-Architect till the Conditioning step

.PHONY: run_rtla_est
run_rtla_est: RTLA_FLOW=estimation
run_rtla_est: run_rtla ## Run RTL-Architect till the Estimation step

.PHONY: run_rtla
run_rtla: create_run_dir $(FLOW_PREREQUISITES) ## Run RTL-Architect till the chosen step (default: Elaboration)
	@echo "Running $(RTLA_CMD) on design till $(RTLA_FLOW) step"
	cd $(BUILD_DIR)/$(RTLA_RUN_DIR)
	RTLA_FLOW=$(RTLA_FLOW) DFT=$(DFT) MAKEFILE_DIR=$(MAKEFILE_DIR) RTLA_EXEC_DIR=$(RTLA_EXEC_DIR) GRID_NUM_CPUS=$(GRID_NUM_CPUS)\
		$(RTLA_CMD) \
		-file ../../rtla_setup.tcl

.PHONY: check_bronze
check_bronze: create_run_dir $(FLOW_PREREQUISITES) ## Run check bronze
	@echo "Get macro's and interfaces..."
	cd $(BUILD_DIR)/$(RTLA_RUN_DIR)
	DFT=$(DFT) MAKEFILE_DIR=$(MAKEFILE_DIR) RTLA_EXEC_DIR=$(RTLA_EXEC_DIR) GRID_NUM_CPUS=$(GRID_NUM_CPUS) BUILD_DIR=$(BUILD_DIR)\
		$(RTLA_CMD) \
		-file ${REPO_ROOT}/hw/scripts/rtla/check_bronze.tcl

.PHONY: all
all: run_rtla_est ## Run to Estimation.

include $(GIT_REPO)/hw/scripts/flow_makefiles/_post.mk
