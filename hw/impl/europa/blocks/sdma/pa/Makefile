GIT_REPO := $(shell git rev-parse --show-toplevel)
include $(GIT_REPO)/hw/scripts/flow_makefiles/_pre.mk

########################################
##@ PowerArtist setup:
########################################

##% DFT @@ {(0), 1 } @@ Run on DFT-inserted RTL
DFT ?= 0

########################################
## Validate the configuration:
########################################


########################################
## Create the build and run directories:
########################################
BUILD_DIR := build_power_artist

# Define the directory name using the timestamp
PA_RUN_DIR ?= run_$(TIMESTAMP)
PA_EXEC_DIR := $(BUILD_DIR)
PA_PARSED_RPT_DIR := $(BUILD_DIR)/parsed_reports

PA_PARSE_UNGATED_THRESHOLD ?= 5 ## set threshold on what to report, below will not end up in parsed report

PA_SCRIPTS_DIR := $(GIT_REPO)/hw/scripts/pa

PA_PDB_DIR := ${PA_EXEC_DIR}/pdb/
PA_ELAB_PDB := ${PA_PDB_DIR}/${DESIGN_NAME}_elab.pdb
PA_ELAB_GATE_PDB := ${PA_PDB_DIR}/${DESIGN_NAME}_elab.gate.pdb
PA_DESIGN_STAGE:=rtl

PA_COMMON_CMD_SETTINGS:=DFT=$(DFT) MAKEFILE_DIR=$(MAKEFILE_DIR) PA_EXEC_DIR=$(PA_EXEC_DIR)

$(PA_EXEC_DIR):
	mkdir -p $(PA_EXEC_DIR)
	@echo "Created run directory: $(PA_EXEC_DIR)"

$(PA_PARSED_RPT_DIR):
	mkdir -p $(PA_PARSED_RPT_DIR)

########################################
##@ PowerArtist flows:
########################################
PA_WAIT_FOR_LIC:=-wait -wait_for_license_timeout 36000
PA_CMD ?= $(GRID_CMD) pa_shell $(PA_WAIT_FOR_LIC)

${PA_ELAB_PDB}: pa_elab
# gatelevel elaboration is only requierd for PACE generation:
${PA_ELAB_GATE_PDB}: PA_DESIGN_STAGE=gate
${PA_ELAB_GATE_PDB}: pa_elab

pa_elab: $(PA_EXEC_DIR) $(FLOW_PREREQUISITES) ## Run PowerArtist elaboration
	cd $(PA_EXEC_DIR)
	$(PA_COMMON_CMD_SETTINGS) PA_DESIGN_STAGE=$(PA_DESIGN_STAGE)\
		$(PA_CMD) \
		-tcl ${PA_SCRIPTS_DIR}/run_elab.tcl

pa_ase: ${PA_ELAB_PDB} $(PA_EXEC_DIR) $(FLOW_PREREQUISITES) ## Run Analyse Static Efficiency on the design
	cd $(PA_EXEC_DIR)
	$(PA_COMMON_CMD_SETTINGS)\
		$(PA_CMD) \
		-tcl ${PA_SCRIPTS_DIR}/run_ase.tcl

pa_red: ${PA_ELAB_PDB} $(PA_EXEC_DIR) $(FLOW_PREREQUISITES) ## Run PA reduction on the design
	cd $(PA_EXEC_DIR)
	$(PA_COMMON_CMD_SETTINGS)\
		$(PA_CMD) \
		-tcl ${PA_SCRIPTS_DIR}/run_red.tcl

.PHONY: pa_ase_parse
pa_ase_parse: $(PA_PARSED_RPT_DIR) $(PA_EXEC_DIR)/report/*_static_efficiency_detailed.rpt ## Parse the report of the ASE run
	python3.8 ${PA_SCRIPTS_DIR}/parsing/ase_parse.py -t $(PA_PARSE_UNGATED_THRESHOLD) -b $(BUILD_DIR) -o $(PA_PARSED_RPT_DIR)

pa_avg: ${PA_ELAB_PDB} $(PA_EXEC_DIR) $(FLOW_PREREQUISITES) ## Run average power analysis on the design
	cd $(PA_EXEC_DIR)
	$(PA_COMMON_CMD_SETTINGS)\
		$(PA_CMD) \
		-tcl ${PA_SCRIPTS_DIR}/run_avg.tcl

pa_pace_gen: ${PA_ELAB_GATE_PDB} $(PA_EXEC_DIR) $(FLOW_PREREQUISITES) ## Generate PACE tech file, used for power estimations
	cd $(PA_EXEC_DIR)
	$(PA_COMMON_CMD_SETTINGS)\
		$(PA_CMD) \
		-tcl ${PA_SCRIPTS_DIR}/run_pace_gen.tcl


include $(GIT_REPO)/hw/scripts/flow_makefiles/_post.mk
