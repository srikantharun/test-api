########################################
##@ Setup the repo base paths
########################################

REPO_ROOT := $(shell git rev-parse --show-toplevel)

GIT_REPO ?= $(REPO_ROOT)
include $(REPO_ROOT)/hw/scripts/flow_makefiles/_pre.mk

########################################
##@ setup for Formality
########################################

##% FM_LOG_DIR            @@ logs               @@ Formality run log directory
FM_LOG_DIR                ?= logs
##% FM_TCL_SCRIPT         @@ fm.tcl             @@ Formality tcl script
FM_TCL_SCRIPT             ?= fm.tcl
NETLIST_TYPE              ?= rtla
FM_RUN_DIR				  ?= build_$(NETLIST_TYPE)

.PHONY: formality
formality: $(FLOW_PREREQUISITES)
	fm_shell -f $(FM_TCL_SCRIPT) -work_path ${FM_RUN_DIR} |& tee $(FM_LOG_DIR)/fm_shell.log

CLEAN_PREREQUISITES += clean_formality
.PHONY: clean_formality
clean_formality: ## Clean all formality generated files
	rm -rf build_*

include $(REPO_ROOT)/hw/scripts/flow_makefiles/_post.mk
