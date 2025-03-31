########################################
## This file provides common setup
########################################

.DEFAULT_GOAL := help

# Tell make to use bash instead of sh and make use of oneshell
SHELL := /usr/bin/bash
.SHELLFLAGS := -eu -o pipefail -c
.ONESHELL:

# Check that given variables are set and all have non-empty values,
# die with an error otherwise.
#
# Params:
#   1. Variable name(s) to test.
#   2. (optional) Error message to print.
check_defined = \
    $(strip $(foreach 1,$1, \
        $(call __check_defined,$1,$(strip $(value 2)))))
__check_defined = \
    $(if $(value $1),, \
      $(error Undefined: $1$(if $2, ($2))))

# Check that given variables are not set
# die with an error otherwise.
#
# Params:
#   1. Variable name(s) to test.
#   2. (optional) Error message to print.
check_undefined = \
    $(strip $(foreach 1,$1, \
        $(call __check_undefined,$1,$(strip $(value 2)))))
__check_undefined = \
    $(if $(value $1), \
      $(error Already defined: $1$(if $2, ($2))), \
      $(eval $1 := ))

########################################
##@ Global Variables:
########################################

##% GIT_REPO @@ @@ This always points to the root of the repository
$(call check_defined, GIT_REPO, add 'GIT_REPO := $(shell git rev-parse --show-toplevel)' before including _pre.mk)

##% MAKEFILE_DIR @@ @@ This points to the location the makefile link is located
MAKEFILE_DIR := $(realpath $(dir $(firstword $(MAKEFILE_LIST))))

##% RANDOM_SEED @@ /dev/urandom @@ This always gives a different random number
RANDOM_SEED := $(strip $(shell od -vAn -N4 -tu4 < /dev/urandom))

# Get the current timestamp
TIMESTAMP := $(shell date +"%Y%m%d_%H%M%S")

##% FLOW_PREREQUISITES @@ @@ These targets are called every time when executing something
$(call check_undefined, FLOW_PREREQUISITES, This variable is reserved for global prerequisites)

########################################
##@ Global computing grid setup (SLURM):
########################################

##% GRID_ENABLE @@ { 0 ,(1)} @@ Run heavy jobs on the computing grid
GRID_ENABLE ?= 1

##% GRID_NUM_CPUS @@ {1} @@ The amount of cpu cores to allocate
GRID_NUM_CPUS ?= 2

##% GRID_TIME_MINUTES @@ {1440} @@ The number of minutes until timeout
GRID_TIME_MINUTES ?= 1440

##% GRID_OPTS_EXT @@ ="<extra_options>" @@ Arguments passed to compute grid commands
GRID_OPTS_EXT ?=
$(call check_undefined, GRID_OPTS, do not add to this variable)

$(call check_undefined, GRID_CMD, do not add to this variable)
GRID_CMD ?=

GRID_OPTS  = --verbose
GRID_OPTS += --cpus-per-task=$(GRID_NUM_CPUS)
GRID_OPTS += --time=$(GRID_TIME_MINUTES)

ifeq ("$(GRID_ENABLE)", "1")
GRID_CMD  = srun $(GRID_OPTS) $(GRID_OPTS_EXT)
endif


########################################
##@ IP Generators
########################################

####################
# Token Generation #
####################
TOKEN_TOP_PROD_CNTR_W:=4
TOKEN_TOP_CONS_CNTR_W:=8
TOKEN_AIC_CNTR_W:=8
TOKEN_APU_CNTR_W:=8
TOKEN_SCRIPT_SOURCES := $(GIT_REPO)/bin/token_manager_mapping $(shell find $(GIT_REPO)/hw/ip/token_manager/default/scripts -type f ! -name "*.pyc")
TOKEN_MAPPING_AIC_CSV := $(GIT_REPO)/hw/ip/aic_common/default/data/aic_token_mapping.csv
TOKEN_MAPPING_TOP_CSV := $(GIT_REPO)/hw/impl/europa/data/top_token_network/top_token_network.csv
TOKEN_CSR_HJSON_DIR  := $(GIT_REPO)/hw/ip/token_manager/default/data/build_token

TOKEN_MAPPING_BUILD := $(GIT_REPO)/hw/ip/token_manager/default/rtl/pkg/build_token

TOP_UID_MAPPING := $(GIT_REPO)/hw/impl/europa/data/top_token_network/top_token_network_uid.lst

$(TOKEN_MAPPING_BUILD):
	mkdir -p $@
	touch $@
$(TOKEN_CSR_HJSON_DIR):
	mkdir -p $@
	touch $@

TOKEN_AIC_CSR_HJSON     := $(TOKEN_CSR_HJSON_DIR)/token_manager_aic_csr.hjson
TOKEN_APU_CSR_HJSON     := $(TOKEN_CSR_HJSON_DIR)/token_manager_apu_csr.hjson
TOKEN_SDMA_CSR_HJSON    := $(TOKEN_CSR_HJSON_DIR)/token_manager_sdma_csr.hjson
TOKEN_AIC_MAPPING_PKG   := $(TOKEN_MAPPING_BUILD)/token_mgr_mapping_aic_pkg.sv
TOKEN_APU_MAPPING_PKG   := $(TOKEN_MAPPING_BUILD)/token_mgr_mapping_apu_pkg.sv
TOKEN_SDMA_MAPPING_PKG  := $(TOKEN_MAPPING_BUILD)/token_mgr_mapping_sdma_pkg.sv

TOKEN_TARGETS = $(TOKEN_AIC_CSR_HJSON) $(TOKEN_APU_CSR_HJSON) $(TOKEN_SDMA_CSR_HJSON) \
                  $(TOKEN_AIC_MAPPING_PKG) $(TOKEN_APU_MAPPING_PKG) $(TOKEN_SDMA_MAPPING_PKG)
FLOW_PREREQUISITES += $(TOKEN_TARGETS)

$(TOKEN_TARGETS): $(TOKEN_MAPPING_AIC_CSV) $(TOKEN_MAPPING_TOP_CSV) $(TOKEN_MAPPING_BUILD) $(TOKEN_CSR_HJSON_DIR) $(TOKEN_SCRIPT_SOURCES) $(TOP_UID_MAPPING)
	token_manager_mapping -t $(TOKEN_MAPPING_TOP_CSV) -ip AIC0  -tpw $(TOKEN_TOP_PROD_CNTR_W) -tcw $(TOKEN_TOP_CONS_CNTR_W) -po $(TOKEN_AIC_MAPPING_PKG)  -ho $(TOKEN_AIC_CSR_HJSON) \
	                        -l $(TOKEN_MAPPING_AIC_CSV) -w $(TOKEN_AIC_CNTR_W)
	token_manager_mapping -t $(TOKEN_MAPPING_TOP_CSV) -ip APU   -tpw $(TOKEN_APU_CNTR_W)      -tcw $(TOKEN_APU_CNTR_W)      -po $(TOKEN_APU_MAPPING_PKG)  -ho $(TOKEN_APU_CSR_HJSON) --sw_endpoint_only
	token_manager_mapping -t $(TOKEN_MAPPING_TOP_CSV) -ip SDMA0 -tpw $(TOKEN_TOP_PROD_CNTR_W) -tcw $(TOKEN_TOP_CONS_CNTR_W) -po $(TOKEN_SDMA_MAPPING_PKG) -ho $(TOKEN_SDMA_CSR_HJSON)

.PHONY: gen_token_mapping
gen_token_mapping: $(TOKEN_TARGETS) ## Generate the token mapping intermediate files


.PHONY: clean_gen_token
CLEAN_PREREQUISITES += clean_gen_token
clean_gen_token: ## Remove intermediate token generation files
	rm -rf $(TOKEN_MAPPING_BUILD)
	rm -rf $(TOKEN_CSR_HJSON_DIR)

##################
# CSR Generation #
##################

# Include data file listings
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre_csr.mk

# this will pre-process hjson_pre to be able to include parts:
%.hjson : %.hjson_pre
	simple_preprocess $< -o $@

# Generate the expected list of generated output file names
_GEN_REGS = $(addprefix $(GIT_REPO)/,$(subst .hjson,_reg_top.sv,$(subst data,rtl/build_reg,$(CSR_IP_LIST))))

# This will make sure that only the CSR hjson for which a partiular rule triggered will be part of the prerequisites
.SECONDEXPANSION: $(_GEN_REGS)
$(_GEN_REGS): $$(subst rtl/build_reg,data,$$(subst _reg_top.sv,.hjson,$$@)) $(TOKEN_CSR_HJSON) $(TIMESTAMP_LOGGER_CSR_HJSON)
	@echo "regtool: Generating RTL : $@"
	@mkdir -p $(dir $@)
	@regtool \
		-r $< \
		-t $(dir $@)

# Capture all registers to be generated
FLOW_PREREQUISITES += gen_reg
gen_reg: $(_GEN_REGS) ## Generate all regtool registers

CLEAN_PREREQUISITES += clean_reg
.PHONY: clean_reg
clean_reg: ## Remove all generated registers and virtualenv
	rm -rf $(dir $(_GEN_REGS))

# Generate the expected list of generated output file names
_GEN_REG_DOCS = $(addprefix $(GIT_REPO)/,$(subst .hjson,_regs.md,$(subst data,docs/build_reg,$(CSR_IP_LIST))))

# This will make sure that only the CSR hjson for which a partiular rule triggered will be part of the prerequisites
.SECONDEXPANSION: $(_GEN_REG_DOCS)
$(_GEN_REG_DOCS): $$(subst docs/build_reg,data,$$(subst _regs.md,.hjson,$$@)) $(TOKEN_CSR_HJSON)
	@echo "regtool: Generating DOC : $@"
	@mkdir -p $(dir $@)
	@regtool \
		-d $< \
		-o $@

# Capture all registers to be generated
FLOW_PREREQUISITES += gen_reg_doc
gen_reg_doc: $(_GEN_REG_DOCS) ## Generate all regtool register docs

CLEAN_PREREQUISITES += clean_reg_doc
.PHONY: clean_reg_doc
clean_reg_doc: ## Remove all generated registers and virtualenv
	rm -rf $(dir $(_GEN_REG_DOCS))

# Generate the expected list of generated output file names
_GEN_RALS = $(addprefix $(GIT_REPO)/,$(subst .hjson,_ral_pkg.sv,$(subst data,dv/build_ral,$(CSR_IP_LIST))))

# This will make sure that only the CSR hjson for which a partiular rule triggered will be part of the prerequisites
.SECONDEXPANSION: $(_GEN_RALS)
$(_GEN_RALS): $$(subst dv/build_ral,data,$$(subst _ral_pkg.sv,.hjson,$$@)) $(TOKEN_CSR_HJSON)
	@echo "regtool: Generating RAL : $@"
	@mkdir -p $(dir $@)
	@regtool \
		-s $< \
		-t $(dir $@)

# Capture all registers to be generated
FLOW_PREREQUISITES += gen_ral
gen_ral: $(_GEN_RALS) ## Generate all regtool registers

CLEAN_PREREQUISITES += clean_ral
.PHONY: clean_ral
clean_ral: ## Remove all generated registers and virtualenv
	rm -rf $(dir $(_GEN_RALS))

#################
# Lowrisc IPGen #
#################

# Include data file listings
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre_ipgen.mk

# Generate the expected list of generated output file names
_GEN_IPGEN = $(addprefix $(GIT_REPO)/,$(subst .hjson,,$(subst data,rtl/build_ipgen,$(IPGEN_LIST))))

# This will make sure that only the CSR hjson for which a partiular rule triggered will be part of the prerequisites
.SECONDEXPANSION: $(_GEN_IPGEN)
$(_GEN_IPGEN): $$(subst rtl/build_ipgen,data,$$(addsuffix .hjson,$$@))
	rm -rf $@
	ipgen generate \
		-C ${GIT_REPO}/hw/vendor/lowrisc/ip_templates/$(notdir $(basename $<)) \
		--config-file $< \
		--force \
		-o $@
	touch $@

# Capture all registers to be generated
FLOW_PREREQUISITES += gen_ipgen
gen_ipgen: $(_GEN_IPGEN) ## Generate all regtool registers

CLEAN_PREREQUISITES += clean_ipgen
.PHONY: clean_ipgen
clean_ipgen: ## Remove all generated registers and virtualenv
	rm -rf $(_GEN_IPGEN)

#############################
# Pad generation for Europa #
#############################

PAD_GENERATOR_FILES = $(GIT_REPO)/bin/pad_solder $(shell find $(GIT_REPO)/hw/scripts/pad_solder -type f ! -name "*.pyc")
EUROPA_PAD_CONFIG = $(GIT_REPO)/hw/impl/europa/asic/data/europa_io.csv
EUROPA_PAD_MODULE = $(subst asic/data,asic/rtl/build_pad,$(EUROPA_PAD_CONFIG:%.csv=%.sv))

$(dir $(EUROPA_PAD_MODULE)):
	mkdir -p $@
	touch $@

FLOW_PREREQUISITES += $(EUROPA_PAD_MODULE)
$(EUROPA_PAD_MODULE): $(EUROPA_PAD_CONFIG) $(PAD_GENERATOR_FILES) $(dir $(EUROPA_PAD_MODULE))
	pad_solder render \
		-t $(GIT_REPO)/hw/scripts/pad_solder/templates \
		-c $< \
		> $@
	$(REPO_ROOT)/hw/scripts/flow_makefiles/copy_if_diff.sh $@ $(subst build_pad,generated,$@)

.PHONY: gen_europa_pads
gen_europa_pads: $(EUROPA_PAD_MODULE) ## Generate the IO pad module for europa

CLEAN_PREREQUISITES += clean_europa_pads
.PHONY: clean_europa_pads ## Remove the generated pads
clean_europa_pads:
	rm -rf $(dir $(EUROPA_PAD_MODULE))

###################################
##@ p wrapper generation for Europa
###################################

##% P_WRAPPER_BLOCK_NAMES @@ ai_core @@ list of supported blocks for p wrapper
P_WRAPPER_BLOCK_NAMES 		?= aic_infra dcd pve soc_periph aic_did #lpddr pcie l2 aic_mid sys_spm

##% P_WRAPPER_CONFIG_FILES @@ all _p.hjson for given blocks @@ list of _p.hjson files
P_WRAPPER_CONFIG_FILES 		?= $(foreach block,$(P_WRAPPER_BLOCK_NAMES),$(REPO_ROOT)/hw/impl/europa/blocks/$(block)/data/$(block)_p.hjson)

##% P_WRAPPER_GENERATED_FILES @@ all _p.sv for given blocks @@ list of _p.sv files
P_WRAPPER_GENERATED_FILES 	?= $(foreach block,$(P_WRAPPER_BLOCK_NAMES),$(REPO_ROOT)/hw/impl/europa/blocks/$(block)/rtl/generated/$(block)_p.sv)

#TODO add wrappers as part of pre-requisites
#FLOW_PREREQUISITES += $(P_WRAPPER_GENERATED_FILES)

# Generate rules to generate p wrapper for each block based on the working pattern
define P_WRAPPER_BLOCK_RULE
$(REPO_ROOT)/hw/impl/europa/blocks/$(1)/rtl/generated/%_p.sv: $(REPO_ROOT)/hw/impl/europa/blocks/$(1)/data/%_p.hjson
	@echo "Generating $$@ from $$<"
	p_wrapper $(basename $(notdir $$*))
	$(eval SOURCE_DIR := $(REPO_ROOT)/hw/impl/europa/blocks/$(1)/rtl/build_wrapper/)
	$(REPO_ROOT)/hw/scripts/flow_makefiles/copy_if_diff.sh $(SOURCE_DIR)$(notdir $$*)_p.sv $$@
endef

# Apply rules for each block
$(foreach block,$(P_WRAPPER_BLOCK_NAMES),$(eval $(call P_WRAPPER_BLOCK_RULE,$(block))))

.PHONY: gen_p_wrappers
gen_p_wrappers: $(TOKEN_CSR_HJSON) $(TOKEN_MAPPING_PKG) $(P_WRAPPER_GENERATED_FILES) ## Generate listed p wrappers

#TODO add wrappers as part of pre-requisites
#CLEAN_PREREQUISITES += clean_p_wrappers
.PHONY: clean_p_wrappers ## Remove the generated p wrappers
clean_p_wrappers:
	rm -f $(P_WRAPPER_GENERATED_FILES)

########################################
##@ Tech Lib Generators
########################################

##% AXE_TCL_CONFIG_DIR @@ $(GIT_REPO)/hw/ip/tech_cell_library/default/data @@ The base directory for tech lib config files
AXE_TCL_CONFIG_DIR   	?= $(GIT_REPO)/hw/ip/tech_cell_library/default/data

##% AXE_TCL_CONFIG_YML @@ $(AXE_TCL_CONFIG_DIR)/axe_tcl_config.yml @@ The YAML config file for generator
AXE_TCL_CONFIG_YML   	?= $(AXE_TCL_CONFIG_DIR)/axe_tcl_config.yml

##% AXE_TCL_BENDER_FILE @@ $(GIT_REPO)/hw/ip/tech_cell_library/default/rtl/Bender.yml @@ The generated tech lib Bender file
AXE_TCL_BENDER_FILE  	?= $(GIT_REPO)/hw/ip/tech_cell_library/default/rtl/Bender.yml

##% AXE_TCL_TECHLIB @@ $(GIT_REPO)/hw/ip/tech_cell_library/default/rtl/sf5a/tc_techlib.tcl @@ The generated tech lib tcl file
AXE_TCL_TECHLIB      	?= $(GIT_REPO)/hw/ip/tech_cell_library/default/rtl/sf5a/tc_techlib.tcl

##% AXE_TCL_MBIST_TECHLIB @@ $(GIT_REPO)/hw/ip/tech_cell_library/default/rtl/sf5a/tc_mbist_techlib.tcl @@ The generated mbist tcl file
AXE_TCL_MBIST_TECHLIB	?= $(GIT_REPO)/hw/ip/tech_cell_library/default/rtl/sf5a/tc_mbist_techlib.tcl

AXE_TCL_YAML_DEP  := $(AXE_TCL_CONFIG_YML) $(AXE_TCL_CONFIG_DIR)/ips.yml
AXE_TCL_SCRIPT    ?= gen_axe_tcl_config
AXE_TCL_LOG_FILE  ?= gen_axe_tcl.log
AXE_TCL_OUTPUTS   ?= $(AXE_TCL_BENDER_FILE) $(AXE_TCL_TECHLIB) $(AXE_TCL_MBIST_TECHLIB) $(AXE_TCL_LOG_FILE)

FLOW_PREREQUISITES += gen_axe_tcl

.NOTPARALLEL: gen_axe_tcl
gen_axe_tcl: $(AXE_TCL_BENDER_FILE) $(AXE_TCL_TECHLIB) $(AXE_TCL_MBIST_TECHLIB)## Generate tech lib files

$(AXE_TCL_BENDER_FILE): $(AXE_TCL_YAML_DEP) ## Build target that depends on YAML files
	$(AXE_TCL_SCRIPT) -y $(AXE_TCL_CONFIG_YML) -t $(AXE_TCL_TECHLIB) -m $(AXE_TCL_MBIST_TECHLIB) -b $(AXE_TCL_BENDER_FILE) -d "info"

$(AXE_TCL_TECHLIB): $(AXE_TCL_YAML_DEP) ## Build target that depends on YAML files
	$(AXE_TCL_SCRIPT) -y $(AXE_TCL_CONFIG_YML) -t $(AXE_TCL_TECHLIB) -m $(AXE_TCL_MBIST_TECHLIB) -b $(AXE_TCL_BENDER_FILE) -d "info"

CLEAN_PREREQUISITES += clean_axe_tcl
.PHONY: clean_axe_tcl
clean_axe_tcl: ## Clean target to remove generated tech lib files
	rm -f $(AXE_TCL_OUTPUTS)


########################################
##@ Bender Variables:
########################################
BENDER ?= bender

##% BENDER_MANI_LOC @@ @@ Point to the direcotry where bender hooks in, set in config
# Add this in any makefile that uses bender !!!
# $(call check_defined, BENDER_MANI_LOC, add to your configuration file)

##% BENDER_TARGETS_EXT @@ @@ add extra targets to the bender invocation
BENDER_TARGETS_EXT ?=
$(call check_undefined, BENDER_TARGETS, do not add to this variable)

##% BENDER_ARGS_EXT @@ @@ add extra bender global arguments
BENDER_ARGS_EXT ?=
$(call check_undefined, BENDER_ARGS, do not add to this variable)

##% BENDER_ARGS_EXT @@ @@ add extra bender subcommand arguments
BENDER_SUBCMD_ARGS_EXT ?=
$(call check_undefined, BENDER_SUBCMD_ARGS, do not add to this variable)

CLEAN_PREREQUISITES += clean_bender
.PHONY: clean_bender
clean_bender: ## Remove all Bender.lock files in the repo
	@# Keep the Bender.lock files clean
	rm -f $(shell find $(GIT_REPO) -name Bender.lock)

.PHONY: bender_update
bender_update: clean_bender $(FLOW_PREREQUISITES) ## Run bender dependency resolution
	$(BENDER) -d $(BENDER_MANI_LOC) update
