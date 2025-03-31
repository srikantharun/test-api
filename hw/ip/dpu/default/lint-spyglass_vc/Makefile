########################################
##@ Setup the repo base paths
########################################
GIT_REPO ?= $(REPO_ROOT)
include $(REPO_ROOT)/hw/scripts/flow_makefiles/_pre.mk

########################################
##@ setup for Spyglass
########################################

##% SG_FLOW_CONFIG @@ ="sg_config.mk" @@ Specify configuration options, create if required
ifeq (${DFT},1)
SG_FLOW_CONFIG ?= sg_config.dft.mk
else
SG_FLOW_CONFIG ?= sg_config.mk
endif
-include $(SG_FLOW_CONFIG)

##% GUI @@ {(0), 1 } @@ Enable GUI
GUI ?= 0
##% SG_PROJECT @@ ./sg_proj.prj @@ Spyglass project file
SG_PROJECT  ?= $(MAKEFILE_DIR)/sg_proj.prj
##% SG_GOALS @@ lint/lint_rtl @@ Goals to run spyglass for
##% SG_GOALS @@  @@ (lint/<lint_rtl,lint_abstract>)
##% SG_GOALS @@  @@ (cdc/<cdc_setup,cdc_setup_check,clock_reset_integrity,cdc_verify_struct,cdc_verify,cdc_abstract>)
##% SG_GOALS @@  @@ (rdc/rdc_verify_struct)
SG_GOALS 	?= lint/lint_rtl
##% SG_DIR @@ build_spyglass @@ Spyglass working directory
SG_DIR 		?= $(MAKEFILE_DIR)/build_spyglass
##% SG_BATCH @@ -batch @@ Spyglass batchmode
ifeq ("$(GUI)", "0")
SG_BATCH	?= -batch
else
GRID_OPTS	+= --x11
SG_BATCH	?= -gui
endif
##% SG_VERSION @@ U-2023.03 @@ Spyglass version for module load
SG_VERSION	?= U-2023.03
##% SPYGLASS_TERA_TEMPATE @@ /hw/scripts/bender_templates/spyglass_tcl.tera @@ Spyglass tera template for bender
SPYGLASS_TERA_TEMPATE ?=hw/scripts/bender_templates/spyglass_tcl.tera
##% BENDER_SPYGLASS_TARGETS @@ -t spyglass -t synopsy -t synthesis @@ Additional targets for spyglass
BENDER_SPYGLASS_TARGETS ?=-t spyglass -t synopsys -t synthesis

.PHONY: $(SG_DIR)
$(SG_DIR): ## Create the spyglass build directory
	@mkdir -p $@
	find $(MAKEFILE_DIR) -name '*.awl'  -exec cp -f {} $@ ';'
	find $(MAKEFILE_DIR) -name '*.sdc'  -exec cp -f {} $@ ';'
	find $(MAKEFILE_DIR) -name '*.sgdc' -exec cp -f {} $@ ';'
	@touch $@


.PHONY: $(SG_DIR)/$(IP_NAME).add_sources.tcl
SPYGLASS_PREREQUISITES += $(SG_DIR)/$(IP_NAME).add_sources.tcl
$(SG_DIR)/$(IP_NAME).add_sources.tcl: $(SG_DIR) $(FLOW_PREREQUISITES) ## Generate the spyglass add_sources script with bender
	$(BENDER) -d $(BENDER_MANI_LOC_RTL) script template \
		--template $(REPO_ROOT)/$(SPYGLASS_TERA_TEMPATE) \
		$(BENDER_TARGETS) \
		$(BENDER_TARGETS_EXT) \
		$(BENDER_SPYGLASS_TARGETS) \
		> $@
	@chmod +x $@


.PHONY: spyglass
spyglass: $(SPYGLASS_PREREQUISITES) ## Runs spyglass flow
	@module switch vcspyglass/$(SG_VERSION)
	@cd $(SG_DIR)
	$(GRID_CMD) spyglass \
		-project $(SG_PROJECT) \
		$(SG_BATCH) \
		-goals $(SG_GOALS)


.PHONY: spyglass_vc
spyglass_vc: $(SPYGLASS_PREREQUISITES) ## Runs spyglass_vc flow
	@module switch vc/$(SG_VERSION)
	@cd $(SG_DIR)
	$(GRID_CMD) spyglass_vc \
		-project $(SG_PROJECT) \
		$(SG_BATCH) \
		-goals $(SG_GOALS)


CLEAN_PREREQUISITES += clean_spyglass
.PHONY: clean_spyglass
clean_spyglass: ## Clean all spyglass generated files
	rm -rf $(SG_DIR)
	rm -f *.tcl*


include $(REPO_ROOT)/hw/scripts/flow_makefiles/_post.mk
