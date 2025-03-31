GIT_REPO := $(shell git rev-parse --show-toplevel)
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre.mk

########################################
##@ Linting setup:
########################################

##% LINT_FLOW_CONFIG @@ ="lint_config.mk" @@ Specify configuration options
LINT_FLOW_CONFIG ?= lint_config.mk
include $(LINT_FLOW_CONFIG)

########################################
## Validate the configuration:
########################################

BENDER_MANI_LOCATIONS := $(dir $(realpath $(shell find $(MAKEFILE_DIR)/.. -name Bender.yml)))
LINT_TARGETS := $(BENDER_MANI_LOCATIONS:=.lint_check)

WAIVE_BENDER_MANI_LOCATIONS ?=
WAIVE_BENDER_MANI_LOCATIONS_COMMON ?= ../rtl/dft ../dv/dft_tb
WAIVER_LOCATIONS := $(dir $(realpath $(shell find $(WAIVE_BENDER_MANI_LOCATIONS) $(WAIVE_BENDER_MANI_LOCATIONS_COMMON) -name Bender.yml 2>/dev/null )))

##@ Lint flow (Verible):
VERIBLE_LINT ?= verible-verilog-lint

##% VERIBLE_LINT_RULES @@ .rules.verible_lint@@ The verilog linting rules to apply
VERIBLE_LINT_RULES ?= $(GIT_REPO)/.rules.verible_lint

BENDER_TARGETS = -t rtl

.PHONY: verible_lint
verible_lint: $(FLOW_PREREQUISITES) $(LINT_TARGETS)

%.lint_check:	## Run the lint rules for this SUB_IP, it searches for all Bender.yml files from the parent directory
	@echo "Running $(VERIBLE_LINT) on $*..."
	@if [ "$(filter $*, $(WAIVER_LOCATIONS))" = "" ]; then \
		$(VERIBLE_LINT) \
			--rules_config $(VERIBLE_LINT_RULES) \
			--show_diagnostic_context \
			$$($(BENDER) -d $* script flist $(BENDER_TARGETS) $(EXT_BENDER_TARGETS) --no-deps); \
	else \
	  echo "WARNING! Skipping $* because of waiver!";
	fi

.PHONY: all
all: verible_lint ## Run all lightweight linting checks

include $(GIT_REPO)/hw/scripts/flow_makefiles/_post.mk
