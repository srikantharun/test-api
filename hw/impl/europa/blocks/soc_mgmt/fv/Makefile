GIT_REPO := $(shell git rev-parse --show-toplevel)
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre.mk

########################################
##@ VC Formal setup:
########################################

VCF_FLOW = fpv

##% GUI @@ {(0), 1 } @@ Enable GUI
GUI       ?= 0

##% WAIT_LICENSE @@ {60} @@ Waiting for licenses available (in minutes)
WAIT_LICENSE ?= 60

ifeq ("$(GUI)", "1")
VCF_MODE = -gui
GRID_CMD += --x11
else
VCF_MODE = -batch
endif

ifeq ("$(CI)", "")
    VCF_LICENSE_MODE = _interactive
else
    VCF_LICENSE_MODE = _batch
endif

VCF_LICENSE = vcf

BENDER_MANI_LOC = $(MAKEFILE_DIR)/src

BENDER_SCRIPT = template --template ${GIT_REPO}/hw/scripts/bender_templates/synopsys_tcl.tera

BENDER_TARGETS = -t rtl

BENDER_TARGETS_EXT ?=

##% FV_TOP @@ @@ Override VC Formal toplevel

########################################
## Validate the configuration:
########################################


########################################
## Create the build and run directories:
########################################
VCF_BUILD_DIR = $(VCF_FLOW)/build_vcf

.PHONY: create_run_dir
create_run_dir:
	# Create the directory
	mkdir -p $(VCF_BUILD_DIR)
	# Print the created directory name
	@echo "Created run directory: $(VCF_BUILD_DIR)"

########################################
##@ VC Formal flow (command):
########################################
GRID_NUM_CPUS = 4
GRID_OPTS += --mem=8G --license $(VCF_LICENSE)$(VCF_LICENSE_MODE)
VCF_CMD ?= $(GRID_CMD) vcf -f ../run.tcl $(VCF_MODE) -lic_wait $(WAIT_LICENSE)

.PHONY: run_fpv
run_fpv: VCF_FLOW=fpv
run_fpv: BENDER_TARGETS += -t fpv
run_fpv: run_vcf ## Runs FPV

.PHONY: run_cc
run_cc: VCF_FLOW=cc
run_cc: run_vcf ## Runs CC

.PHONY: run_dpv
run_dpv: VCF_FLOW=dpv
run_dpv: BENDER_SCRIPT = template --template ${GIT_REPO}/hw/scripts/bender_templates/vcf.tera
run_dpv: BENDER_TARGETS += -t dpv
run_dpv: VCF_MODE += -fmode DPV -fml_elite
run_dpv: VCF_LICENSE = vcf_dpv
run_dpv: run_vcf ## Runs DPV

.PHONY: run_frv
run_frv: VCF_FLOW=frv
run_frv: BENDER_TARGETS += -t frv
run_frv: run_vcf ## Runs FRV

.PHONY: run_seq
run_seq: VCF_FLOW=seq
run_seq: BENDER_TARGETS += -t seq
run_seq: run_vcf ## Runs SEQ

.PHONY: run_vcf
run_vcf: $(FLOW_PREREQUISITES) set_formal_top create_run_dir bender_update ## Run VC Formal APP (default: FPV)
	@echo "Running $(VCF_MODE) with $(VCF_LICENSE)$(VCF_LICENSE_MODE) license"
	cd $(VCF_BUILD_DIR)
	@echo "Generating bender file with $(BENDER_TARGETS) $(addprefix -t ,$(BENDER_TARGETS_EXT))"
	bender -d $(BENDER_MANI_LOC) script $(BENDER_SCRIPT) $(BENDER_TARGETS) $(addprefix -t ,$(BENDER_TARGETS_EXT)) > rtl.analyze.tcl
ifdef FV_SPEC
	sed -Ei 's/analyze \-format sv/analyze \-format sv \-library impl/g' rtl.analyze.tcl
	bender -d $(FV_SPEC) script $(BENDER_SCRIPT) $(BENDER_TARGETS) $(addprefix -t ,$(BENDER_TARGETS_EXT)) > spec.analyze.tcl
	sed -Ei 's/analyze \-format sv/analyze \-format sv \-library spec/g' spec.analyze.tcl
endif
	@echo "Running $(VCF_FLOW) on $(VCF_MODE) mode"
	$(VCF_CMD)

.PHONY: set_formal_top
set_formal_top: ## Changes toplevel of formal runs
ifdef FV_TOP
	sed -Ei 's/set design \S+$$/set design $(FV_TOP)/g' $(VCF_FLOW)/settings.tcl
endif

########################################
##@ Questasim clean targets:
########################################

CLEAN_PREREQUISITES += clean_vcf_runs
.PHONY: clean_vcf_runs
clean_vcf_runs: ## Remove VCF build directories
	rm -rf */build_vcf

include $(GIT_REPO)/hw/scripts/flow_makefiles/_post.mk
