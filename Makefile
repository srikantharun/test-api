#!/usr/bin/env make -f
GIT_REPO := $(shell git rev-parse --show-toplevel)
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre.mk

########################
##@ Release Variables
########################

##% REL_PROC @@ europa @@
REL_PROC ?= europa

##% REL_TYPE @@ top @@
REL_TYPE ?= block

##% REL_BLOCK @@ "" @@ Block to Release
REL_BLOCK ?= ""

##% REL_DIR @@ "" @@ Release directory
REL_DIR ?= ""

##% REL_PROC @@ "/data/releases/europa/" @@ Flat Release Directory
REL_DIR_FLAT ?= "/data/releases/europa/"

##% REL_KEEP_DURATION @@ 12 @@ Keep releases as old as these many weeks
REL_KEEP_DURATION ?= 12

##% REL_KEEP_FILE @@ hw/scripts/pd_release/pd_release.keep @@ PD Release keep file path
REL_KEEP_FILE ?= $(GIT_REPO)/hw/scripts/pd_release/pd_release.keep

##% REL_CLEANUP_LOG @@ /cleanup_logs/ @@ PD Release cleanup log file
REL_CLEANUP_LOG ?= $(REL_DIR_FLAT)/cleanup_logs/

##% REL_DFT_ENABLE @@ true @@ PD Release DFT flag
REL_DFT_ENABLE ?= true

##% REL_COPY_ALL @@ false @@ PD Release - copy all source files to release directory
REL_COPY_ALL   ?= false

####################################
##@ Generate the Top-Level Source
####################################
.PHONY: gen-europa-aipu
gen-europa-aipu: ## Generate aipu.sv in Europa project
	cd $(GIT_REPO)/hw/impl/europa/asic/ && \
	$(GIT_REPO)/bin/gen_top \
	-i data/aipu.hjson \
	-s true \
  -p ${REPO_ROOT}/hw/scripts/gen_files/protocol | tee gen_aipu.log

.PHONY: gen-europa
gen-europa: ## Generate europa.sv in Europa project
	cd $(GIT_REPO)/hw/impl/europa/asic/ && \
	$(GIT_REPO)/bin/gen_top \
	-i data/europa.hjson \
  -p ${REPO_ROOT}/hw/scripts/gen_files/protocol | tee gen_europa.log

.PHONY: gen-europa-ai_core
gen-europa-ai_core: ## Generate ai_core.sv in Europa project
	cd $(GIT_REPO)/hw/impl/europa/blocks/ai_core && \
	$(GIT_REPO)/bin/gen_top \
	        -i data/ai_core.hjson | tee gen-ai_core.log

################################
##@ Release for Physical Design
################################
.PHONY:
pd_release: ## Release for Physical Design
	$(GIT_REPO)/bin/pd_release \
		-p $(REL_PROC) \
		-t $(REL_TYPE) \
		-b $(REL_BLOCK) \
		-r $(REL_DIR) \
		$(if $(filter $(REL_DFT_ENABLE),true),-d,) \
		-rf "hier"

.PHONY:
pd_release_flat: gen_flow_prerequisites ## Flat Release for Physical Design
	$(GIT_REPO)/bin/pd_release \
		-generate \
		-p $(REL_PROC) \
		-t $(REL_TYPE) \
		-b $(REL_BLOCK) \
		-r $(REL_DIR_FLAT) \
		$(if $(filter $(REL_DFT_ENABLE),true),-d,) \
		$(if $(filter $(REL_COPY_ALL),true),-ca,) \
		-rf "flat"

.PHONY:
pd_release_clean:  ## Flat Release cleanup for Physical Design
	$(GIT_REPO)/bin/pd_release \
		-clean \
		-d $(REL_DIR_FLAT) \
		-k $(REL_KEEP_FILE) \
		-w $(REL_KEEP_DURATION) \
		-l $(REL_CLEANUP_LOG) \
		-f

include $(GIT_REPO)/hw/scripts/flow_makefiles/_post.mk
