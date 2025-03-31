GIT_REPO := $(shell git rev-parse --show-toplevel)
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre.mk

########################################
##@ DFT:
########################################

##% GUI @@ {(0), 1 } @@ Enable GUI
GUI ?= 0
##% DEBUG @@ {(0), 1 } @@ Enable interactive shell (do not exit on error)
DEBUG ?= $(GUI)

##% PROJECT @@ europa @@ Project name
PROJECT ?= europa
##% RTL_INSERTION_DIRS @@ memory_test logic_test @@ List of directories with RTL insertion dofiles
RTL_INSERTION_DIRS ?= memory_test logic_test
##% ATPG_DIRS @@ stuckat atspeed @ List of directories with ATPG dofiles
ATPG_DIRS ?= stuckat atspeed
##% TSDB_NAME @@ tsdb_outdir @@ Name of TSDB for release
TSDB_NAME ?= tsdb_outdir

IP_NAME = $(notdir $(abspath $(MAKEFILE_DIR)../../..))
BLOCK_NAME = $(notdir $(abspath $(MAKEFILE_DIR)../..))

# The source TSDB is located under the last RTL_INSERTION_DIR
RELEASE_TSDB := $(MAKEFILE_DIR)/insertion/$(lastword $(RTL_INSERTION_DIRS))/$(TSDB_NAME)
# The release destination name is the block name
RELEASE_DIR := $(DFT_HOME)/$(BLOCK_NAME)

# The source SDC
RELEASE_SDC     := $(dir $(MAKEFILE_DIR))synth-rtla/constraints/dft
RELEASE_SDC_DIR := /data/europa/pd/europa/dft_scripts/dev/$(BLOCK_NAME)_p

.PHONY: rtl_insertion
rtl_insertion: $(RTL_INSERTION_DIRS) ## Perform full RTL insertion

ifeq ("$(GRID_ENABLE)", "1")
GRID_NUM_CPUS := 4
GRID_CMD += --mem=16G
ifeq ("$(GUI)", "1")
GRID_CMD += --x11
endif
ifeq ("$(DEBUG)", "1")
GRID_CMD += --pty
endif
endif

.PHONY: find_dft_release_of_netlist
find_dft_release_of_netlist:
	@$(call check_defined, NETLIST, define a path to the netlist to search)
	grep -Eom1 '\/data\/releases\/europa\/dft\/.*?\/$(BLOCK_NAME)\/[0-9]+\/' $(abspath $(dir $(NETLIST))../../init_design/log/init_design.log)

.PHONY: create_subblock_atpg_dir
create_subblock_atpg_dir: ## Create atpg directory for subblock design
	cookiecutter $(REPO_ROOT)/hw/scripts/cookiecutter/subblock_atpg_directory

.PHONY: $(RTL_INSERTION_DIRS)
$(RTL_INSERTION_DIRS): % : $(FLOW_PREREQUISITES) ## Perform $@ RTL insertion
	@if [ -d "insertion/$@" ]; then \
		cd insertion/$@ ; $(GRID_CMD) ./run.sh ; \
	else \
		echo "WARNING: Skipping $@ - insertion/$@ does not exist" ; \
	fi

.PHONY: rtl_release
rtl_release: ## Copy RTL from TSDB to release area
ifndef DFT_HOME
	$(error Can\'t release without a DFT_HOME. Please load a dft module: module avail dft -l)
endif
	@if [ -d "$(RELEASE_TSDB)" ]; then \
		echo "Release RTL FROM: $(RELEASE_TSDB)" ; \
		echo "Release RTL TO: $(RELEASE_DIR)" ; \
		$(MAKEFILE_DIR)/release.sh $(RELEASE_TSDB) $(RELEASE_DIR) ../rtl/Bender.yml ; \
	else \
		echo "ERROR: $(RELEASE_TSDB) does not exist" ; exit 1 ; \
	fi

.PHONY: atpg
atpg:
	cd atpg ; $(GRID_CMD) ./run.sh ;

.PHONY: $(ATPG_DIRS)
$(ATPG_DIRS): % : ## Perform $@ ATPG
	@if [ -d "atpg/$@" ]; then \
		cd atpg/$@ ; $(GRID_CMD) ./run.sh ; \
	else \
		echo "WARNING: Skipping $@ - atpg/$@ does not exist" ; \
	fi

.PHONY: sdc_release
sdc_release: ## Copy SDC from constraints to PD area
	@echo "Release SDC FROM: $(RELEASE_SDC)" ; \
	echo "Release SDC TO: $(RELEASE_SDC_DIR)" ; \
	$(REPO_ROOT)/hw/impl/$(PROJECT)/dft/scripts/sdc_release.sh $(RELEASE_SDC) $(RELEASE_SDC_DIR)

.PHONY: imc_bist_signature_update
imc_bist_signature_update: ## Update IMC BIST signature data
ifneq ($(IP_NAME),mvm)
	$(error This command must be run from hw/ip/mvm)
endif
	cd $(MAKEFILE_DIR)/../dv/sim/build_vsim_mvm/run_vsim_ai_core_mvm_bist_no_error_test_1_MBIST
	find . -name "*.txt" -type f -exec md5sum {} \; | sort > $(MAKEFILE_DIR)/../data/imc_bist_signatures/mbist.md5
	cd $(MAKEFILE_DIR)/../dv/sim/build_vsim_mvm/run_vsim_ai_core_mvm_bist_no_error_test_1_CBIST
	find . -name "*.txt" -type f -exec md5sum {} \; | sort > $(MAKEFILE_DIR)/../data/imc_bist_signatures/cbist.md5

.PHONY: imc_bist_signature_check
imc_bist_signature_check: ## Check if IMC BIST vector data matches expected signature
ifneq ($(IP_NAME),mvm)
	$(error This command must be run from hw/ip/mvm)
endif
	cd $(MAKEFILE_DIR)/../dv/sim/build_vsim_mvm/run_vsim_ai_core_mvm_bist_no_error_test_1_MBIST
	md5sum -c $(MAKEFILE_DIR)/../data/imc_bist_signatures/mbist.md5
	cd $(MAKEFILE_DIR)/../dv/sim/build_vsim_mvm/run_vsim_ai_core_mvm_bist_no_error_test_1_CBIST
	md5sum -c $(MAKEFILE_DIR)/../data/imc_bist_signatures/cbist.md5

########################################
## Clean targets:
########################################

CLEAN_PREREQUISITES += clean_insertion
.PHONY: clean_insertion
clean_insertion:
	find $(MAKEFILE_DIR)/insertion -name dft_inserted_designs -type d -exec rm -vr '{}' +
	find $(MAKEFILE_DIR)/insertion -name tsdb_outdir -type d -exec rm -vr '{}' +
	find $(MAKEFILE_DIR)/insertion -name rpt -type d -exec rm -vr '{}' +
	find $(MAKEFILE_DIR)/insertion -name 'build_*' -type d -exec rm -vr '{}' +
	find $(MAKEFILE_DIR)/insertion -name '*.log' -type f -exec rm -v '{}' +
	find $(MAKEFILE_DIR)/insertion -name '*bisr_segment_order*.bak' -type f -exec rm -v '{}' +

include $(GIT_REPO)/hw/scripts/flow_makefiles/_post.mk
