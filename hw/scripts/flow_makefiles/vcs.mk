########################################
##@ VCS setup:
########################################

##% VCS_FLOW_CONFIG @@ ="vcs_config.mk" @@ Specify configuration options
VCS_FLOW_CONFIG ?= vcs_config.mk
-include $(VCS_FLOW_CONFIG)

########################################
##@ VCS build variables:
########################################
ifeq ("$(DEBUG)", "0")
    VCS_LICENSE_TYPE = vcs_batch
else
    VCS_LICENSE_TYPE = vcs_interactive
endif

VLOGAN := $(subst time=$(GRID_TIME_MINUTES),time=$(SIM_COMPILE_TIME_MINUTES)  --license $(VCS_LICENSE_TYPE),  $(GRID_CMD)) vlogan

VCS    := $(subst time=$(GRID_TIME_MINUTES),time=$(SIM_COMPILE_TIME_MINUTES)  --license $(VCS_LICENSE_TYPE),  $(GRID_CMD)) vcs

URG    := $(subst time=$(GRID_TIME_MINUTES),time=$(SIM_COVERAGE_TIME_MINUTES) --license $(VCS_LICENSE_TYPE),  $(GRID_CMD)) urg

VERDI ?= verdi

##% VCS_GUI_TYPE @@ verdi @@ VCS gui to use
VCS_GUI_TYPE ?= verdi

##% VCS_DUMP_TYPE @@ fsdb @@ Dump database datatype
VCS_DUMP_TYPE ?= fsdb

##% VCS_BUILD_DIR @@ build_vcs_<ip> @@ dedicated build direcotry for vcs
VCS_BUILD_DIR ?= $(MAKEFILE_DIR)/build_vcs_$(IP_NAME)$(DFT_TEST_NAME)

$(call check_undefined, _VCS_COMPILE_DIR, _VCS_COMPILE_DIR should not be externally defined)
_VCS_COMPILE_DIR = $(VCS_BUILD_DIR)/compile_vcs

##% VCS_RUN_DIR @@ build_vcs_<ip>/run_<> @@ dedicated run directory for VCS
VCS_RUN_DIR = $(VCS_BUILD_DIR)/run_vcs_$(TESTNAME)_$(SEED)$(subst /,_,$(subst +,_,$(subst $(subst ,, ),_,$(PLUSARGS))))

##% VCS_COVERAGE_DIR @@ build_vcs_<ip> @@ dedicated coverage directory for VCS
VCS_COVERAGE_DIR ?= $(VCS_BUILD_DIR)/coverage_vcs

##% VCS_VLOGAN_OPTS_EXT @@ ="<extra_options>" @@ Arguments passed to all VLOG statements
VCS_VLOGAN_OPTS_EXT ?=
VCS_VHDLAN_OPTS_EXT ?=
VCS_ELAB_OPTS_EXT ?=

VCS_VLOGAN_OPTS ?=
VCS_VHDLAN_OPTS ?=
VCS_ELAB_OPTS_EXT ?=

# Common arguments for all vcs builds
# Specify the different Common compile options for configuring from the Makefile

$(call check_undefined, VCS_VLOGAN_OPTS_COMMON, Common build variable should not be externally defined)
$(call check_undefined, VCS_VHDLAN_OPTS_COMMON, Common build variable should not be externally defined)

# Global defines
VCS_VLOGAN_OPTS_COMMON += $(GLOBAL_DEFINES)
VCS_VHDLAN_OPTS_COMMON += $(GLOBAL_DEFINES)

# Supress copyright banner
VCS_VLOGAN_OPTS_COMMON += -nc
VCS_VHDLAN_OPTS_COMMON += -nc

# Use full 64-bit mode
VCS_VLOGAN_OPTS_COMMON += -full64
VCS_VHDLAN_OPTS_COMMON += -full64
VCS_ELAB_OPTS_COMMON   += -full64

# Set the timescale
VCS_VLOGAN_OPTS_COMMON += -timescale=$(TIMESCALE)

# Enable Verdi debug by default
VCS_VLOGAN_OPTS_COMMON += -kdb
VCS_VHDLAN_OPTS_COMMON += -kdb
VCS_ELAB_OPTS_COMMON   += -kdb

# Linting
VCS_VLOGAN_OPTS_COMMON += +lint=TFIPC-L
VCS_ELAB_OPTS_COMMON   += +lint=TFIPC-L

# Incremental analysis
VCS_VLOGAN_OPTS_COMMON += -incr_vlogan

# Enable sva assertions
VCS_VLOGAN_OPTS_COMMON += -assert svaext # Incremental analysis

# Verilog 2k
VCS_VLOGAN_OPTS_COMMON += +v2k

# Debug / waves
VCS_ELAB_OPTS_DEBUG += -debug_access+all +vcs+fsdbon

ifeq ("$(DEBUG)", "1")
VCS_RUN_OPTS_DEBUG += +fsdb+all=on
endif

# Licence
VCS_ELAB_OPTS += +vcs+lic+wait
VCS_RUN_OPTS  += -licqueue

# Stop on assertion
VCS_ELAB_OPTS_EXT += -assert enable_hier
VCS_RUN_OPTS      += -assert global_finish_maxfail=1 -assert errmsg

# Coverage
ifneq ("$(COVERAGE)", "0")
VCS_ELAB_OPTS_COMMON += -cm line+cond+tgl+fsm+branch+assert -cm_report svpackages -cm_dir  $(VCS_COVERAGE_DIR)/simv.vdb
VCS_RUN_OPTS         += -cm line+cond+tgl+fsm+branch+assert -cm_report svpackages -cm_dir  $(VCS_COVERAGE_DIR)/simv.vdb -cm_name $(TESTNAME).$(SEED)
endif

ifneq ("$(XPROP)", "0")
VCS_ELAB_OPTS_COMMON += -xprop=tmerge
endif

ifneq ("$(UVM)", "0")
VCS_VLOGAN_OPTS_COMMON += -ntb_opts uvm-1.2
endif

# UVM Runtime Options
VCS_RUN_OPTS += +UVM_VERBOSITY=$(UVM_VERBOSITY)

########################################
##@ vcs compile targets:
########################################

# Variables for storing the prerequisites / postrequisites for each vcs stage
COMPILE_VCS_PREREQUISITES += $(_VCS_COMPILE_DIR)
ifneq ("$(UVM)", "0")
COMPILE_VCS_PREREQUISITES  += analyze_vcs_uvm
endif

ifneq ("$(DPI_C_SRC)", "")
VCS_SV_LIBS               += -sv_lib $(_VCS_COMPILE_DIR)/dpi
COMPILE_VCS_PREREQUISITES += compile_vcs_dpi
endif

COMPILE_VCS_POSTREQUISITES ?=

.PHONY: $(_VCS_COMPILE_DIR) $(VCS_RUN_DIR)
$(_VCS_COMPILE_DIR) $(VCS_RUN_DIR): ## Create the vcs build directory
	@mkdir -p $@

.PHONY: $(_VCS_COMPILE_DIR)/$(IP_NAME).vcs.compile.sh
$(_VCS_COMPILE_DIR)/$(IP_NAME).vcs.compile.sh: bender_update $(FLOW_PREREQUISITES) $(_VCS_COMPILE_DIR) ## Generate the compile script for vcs
	@# Generate the compile script
	$(BENDER) -d $(BENDER_MANI_LOC) \
		$(BENDER_ARGS_EXT) \
		script vcs \
		$(addprefix --target=,$(BENDER_TARGETS)) \
		$(addprefix --target=,$(BENDER_TARGETS_EXT)) \
		--vlog-arg="$(VCS_VLOGAN_OPTS_COMMON) $(VCS_VLOGAN_OPTS) $(VCS_VLOGAN_OPTS_EXT)" \
		--vcom-arg="$(VCS_VHDLAN_OPTS_COMMON) $(VCS_VHDLAN_OPTS) $(VCS_VHDLAN_OPTS_EXT)" \
		$(EXT_BENDER_SUBCMD_ARGS) \
		> $@
	chmod +x $@

# The grep is to extract the top-level package name directly from the top-level Bender.yml
VCS_UVM_BENDER = $(GIT_REPO)/hw/dv/uvm/vcs
.PHONY: $(_VCS_COMPILE_DIR)/$(IP_NAME).vcs.uvm.compile.sh
$(_VCS_COMPILE_DIR)/$(IP_NAME).vcs.uvm.compile.sh:  $(_VCS_COMPILE_DIR)/$(IP_NAME).vcs.compile.sh
	@# Generate the compile script
	$(BENDER) -d $(VCS_UVM_BENDER) \
		$(BENDER_ARGS_EXT) \
		script template \
		--template=$(GIT_REPO)/hw/scripts/bender_templates/vcs_sh.tera \
		--target=vcs \
		--target=simulation \
		$(addprefix --target=,$(BENDER_TARGETS)) \
		$(addprefix --target=,$(BENDER_TARGETS_EXT)) \
		--vlog-arg="$(VCS_VLOGAN_OPTS_COMMON) $(VCS_VLOGAN_OPTS) $(VCS_VLOGAN_OPTS_EXT)" \
		$(EXT_BENDER_SUBCMD_ARGS) \
		> $@
	chmod +x $@

.PHONY: analyze_vcs_uvm
analyze_vcs_uvm: $(_VCS_COMPILE_DIR)/$(IP_NAME).vcs.uvm.compile.sh
	@# Compile in UVM
	cd $(_VCS_COMPILE_DIR)
	$(VLOGAN) $(VCS_VLOGAN_OPTS_COMMON) $(VCS_VLOGAN_OPTS) $(VCS_VLOGAN_OPTS_EXT)
	TECH_CORNER=$(TECH_CORNER)
	$(subst time=$(GRID_TIME_MINUTES),time=$(SIM_COMPILE_TIME_MINUTES) --license $(VCS_LICENSE_TYPE),  $(GRID_CMD)) $< \
	|& tee $(_VCS_COMPILE_DIR)/$(IP_NAME).$@.log

.PHONY: analyze_vcs
analyze_vcs: $(_VCS_COMPILE_DIR)/$(IP_NAME).vcs.compile.sh $(COMPILE_VCS_PREREQUISITES) ## Run the VCS analysis step
	@# Compile
	cd $(_VCS_COMPILE_DIR)
	TECH_CORNER=$(TECH_CORNER)
	$(subst time=$(GRID_TIME_MINUTES),time=$(SIM_COMPILE_TIME_MINUTES) --license $(VCS_LICENSE_TYPE),  $(GRID_CMD)) $< \
	|& tee $(_VCS_COMPILE_DIR)/$(IP_NAME).$@.log

.PHONY: compile_vcs_dpi
compile_vcs_dpi: $(_VCS_COMPILE_DIR) $(DPI_C_SRC)
	g++ -fPIC -shared -Bsymbolic -std=c++17 $(DPI_C_OPTS)\
 	   -I$(VCS_HOME)/include \
		$(DPI_C_SRC) \
		$(addprefix -I, $(DPI_C_INCDIR)) \
		-o $(_VCS_COMPILE_DIR)/dpi.so

.PHONY: %_vcs_elab
%_vcs_elab: analyze_vcs ## Run the VCS elaboration step for a top-level module
	@cd $(_VCS_COMPILE_DIR) && \
	$(VCS) \
		$(VCS_ELAB_OPTS_COMMON) \
		$(VCS_ELAB_OPTS) \
		$(VCS_ELAB_OPTS_EXT) \
		-l $(_VCS_COMPILE_DIR)/$(patsubst %_vcs_elab,%,$@).elab.log \
		$(patsubst %_vcs_elab,%,$@) \
		-o $(IP_NAME)_elab

.PHONY: %_vcs_elab_debug
%_vcs_elab_debug: %_vcs_elab  ## Run the VCS elaboration step for a top-level module (debug)
	@cd $(_VCS_COMPILE_DIR) && \
	$(VCS) \
		$(VCS_ELAB_OPTS_COMMON) \
		$(VCS_ELAB_OPTS) \
		$(VCS_ELAB_OPTS_EXT) \
		$(VCS_ELAB_OPTS_DEBUG) \
		-l $(_VCS_COMPILE_DIR)/$(patsubst %_vcs_elab_debug,%,$@).elab_debug.log \
		$(patsubst %_vcs_elab_debug,%,$@) \
		-o $(IP_NAME)_elab_debug

.PHONY: compile_vcs
compile_vcs: $(addsuffix _vcs_elab,$(TOP_LEVEL_MODULES)) $(addsuffix _vcs_elab_debug,$(TOP_LEVEL_MODULES)) .WAIT $(COMPILE_VCS_POSTREQUISITES) ## Compile a simulation for a top-level module

########################################
##@ VCS run targets:
########################################

# Variables for storing the prerequisites for each VCS stage
ifeq ("$(NODEPS)", "0")
RUN_VCS_PREREQUISITES += compile_vcs
endif
RUN_VCS_PREREQUISITES += $(VCS_RUN_DIR) $(PRE_SIM_TARGETS)

# Variables for storing the postrequisites for each VCS stage
RUN_VCS_POSTREQUISITES += $(POST_SIM_TARGETS)

ifeq ("$(DEBUG)", "0")
RUN_VCS_ELAB = $(subst time=$(GRID_TIME_MINUTES),time=$(SIM_RUN_TIME_MINUTES) --license $(VCS_LICENSE_TYPE),      $(GRID_CMD)) $(_VCS_COMPILE_DIR)/$(IP_NAME)_elab
else
RUN_VCS_ELAB = $(subst time=$(GRID_TIME_MINUTES),time=$(SIM_RUN_TIME_MINUTES) --license $(VCS_LICENSE_TYPE),      $(GRID_CMD)) $(_VCS_COMPILE_DIR)/$(IP_NAME)_elab_debug
endif

ifneq ("$(GUI)", "0")
RUN_VCS_ELAB += -gui=$(VCS_GUI_TYPE)
endif

VCS_RUN_OPTS_TCL ?=

.PHONY: _run_vcs_
_run_vcs_:
	@# Run in single shell
	# Clear Status
	rm -f $(VCS_RUN_DIR)/PASSED $(VCS_RUN_DIR)/FAILED
	mkdir -p $(VCS_RUN_DIR)
	# Mark as failed - in case of error
	touch $(VCS_RUN_DIR)/FAILED
	# Run the simulation
	cd $(VCS_RUN_DIR)
	sim_sts=0
	$(RUN_VCS_ELAB) \
		$(VCS_RUN_OPTS_COMMON) \
		$(VCS_RUN_OPTS) \
		$(VCS_RUN_OPTS_DEBUG) \
		$(VCS_RUN_OPTS_EXT) \
		$(VCS_RUN_OPTS_TCL) \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		$(PLUSARGS) \
		$(PLUSARGS_COMMON) \
		$(SV_LIBS) \
		$(VCS_SV_LIBS) \
		+ntb_random_seed=$(SEED) \
		-l sim.log || sim_sts=$$?
	# Check the log for errors
	chk_sts=0
	$(GIT_REPO)/hw/scripts/flow_makefiles/check_sim_log_status.sh --simulator vcs --uvm $(UVM) --dft_tb $(DFT) sim.log || chk_sts=1
	if [ $$sim_sts -eq 0 ] && [ $$chk_sts -eq 0 ]; then \
		mv FAILED PASSED; \
	fi

.PHONY:    run_vcs
run_vcs: $(RUN_VCS_PREREQUISITES) .WAIT _run_vcs_ ## Run all tests with vcs
	@# Check for PASSED / FAILED and set correct exit status
	if [ -f $(VCS_RUN_DIR)/PASSED ]; then \
		echo " _____         _____ _____ ______ _____  "; \
		echo "|  __ \ /\    / ____/ ____|  ____|  __ \ "; \
		echo "| |__) /  \  | (___| (___ | |__  | |  | |"; \
		echo "|  ___/ /\ \  \___ \\\___ \|  __| | |  | |"; \
		echo "| |  / ____ \ ____) |___) | |____| |__| |"; \
		echo "|_| /_/    \_\_____/_____/|______|_____/ "; \
	else \
		echo " ______      _____ _      ______ _____  "; \
		echo "|  ____/\   |_   _| |    |  ____|  __ \ "; \
		echo "| |__ /  \    | | | |    | |__  | |  | |"; \
		echo "|  __/ /\ \   | | | |    |  __| | |  | |"; \
		echo "| | / ____ \ _| |_| |____| |____| |__| |"; \
		echo "|_|/_/    \_\_____|______|______|_____/ "; \
		false; \ #Exit status
	fi

########################################
##@ VCS regression targets:
########################################
VCS_VERIFSDK_REGRESS_CMD = \
verifsdk -P $(REGRESS_VERIFSDK_PLATFORM) \
 		 -L $(REGRESS_VERIFSDK_LABEL) \
		 -F sim.VCS \
		 $(REGRESS_VERIFSDK_ARGS)

REGRESS_VCS_PREREQUISITES ?=
ifeq ("$(NODEPS)", "0")
REGRESS_VCS_PREREQUISITES += compile_vcs
endif

.PHONY: regress_vcs
regress_vcs: $(REGRESS_VCS_PREREQUISITES)
	@# Run a regression
	! [ -z "$(REGRESS_SW_BUILD_DIR)" ] && mkdir -p $(REGRESS_SW_BUILD_DIR) && cd $(REGRESS_SW_BUILD_DIR)

	# Compile all the tests (run on grid)
	$(subst cpus-per-task=$(GRID_NUM_CPUS),cpus-per-task=$(REGRESS_VERIFSDK_GRID_NUM_CPUS), $(GRID_CMD)) $(VCS_VERIFSDK_REGRESS_CMD)

	# Run all the tests (run locally - jobs submited to grid)
	verifsdk_exit_value=0
	$(VCS_VERIFSDK_REGRESS_CMD) --ctest $(REGRESS_VERIFSDK_CTEST_ARGS) COVERAGE=$(COVERAGE) || verifsdk_exit_value=$$?

	# Analyse Coverage
	if [[ $(COVERAGE) != 0 ]]; then
		make -C $(MAKEFILE_DIR) report_vcs_coverage > report_vcs_coverage.log || (cat report_vcs_coverage.log && exit 1)

		if [[ -n "$(COVERAGE_ARCHIVE_LOC)" ]]; then
			mkdir -p $(COVERAGE_ARCHIVE_LOC);
			cp -r $(VCS_COVERAGE_DIR)/html $(COVERAGE_ARCHIVE_LOC);
			cp -r $(VCS_COVERAGE_DIR)/simv.vdb $(COVERAGE_ARCHIVE_LOC);
		fi
	fi

	# exit depending on verisdk success
	exit $$verifsdk_exit_value

########################################
##@ VCS single sim targets:
########################################
VCS_VERIFSDK_SIM_CMD = verifsdk -P $(REGRESS_VERIFSDK_PLATFORM) -F sim.VCS --only $(REGRESS_VERIFSDK_TEST)

VSDK_VCS_PREREQUISITES ?= $(REGRESS_SW_BUILD_DIR)
ifeq ("$(NODEPS)", "0")
VSDK_VCS_PREREQUISITES += compile_vcs
endif

.PHONY:    vsdk_vcs
vsdk_vcs: $(VSDK_VCS_PREREQUISITES)
	@# Run in sw build directory
	cd $(REGRESS_SW_BUILD_DIR)

	# Compile the targeted test (run on grid)
	$(GRID_CMD) $(VCS_VERIFSDK_SIM_CMD)

	# Run the targeted test (run locally - jobs submited to grid)
	cd $(REGRESS_VERIFSDK_TEST) && ./run.sh

########################################
##@ VCS coverage targets:
########################################

.PHONY: report_vcs_coverage
report_vcs_coverage: ## Generate coverage html report
	@# Generate coverage report
	echo Generating Coverage Report
	$(URG) -dir $(VCS_COVERAGE_DIR)/simv.vdb -report $(VCS_COVERAGE_DIR)/html

.PHONY: view_vcs_coverage
view_vcs_coverage: ## Launch the coverage gui
	@# Coverage Gui
	echo Viewing Coverage
	-$(VERDI) -cov -covdir $(VCS_COVERAGE_DIR)/simv.vdb

########################################
##@ VCS clean targets:
########################################

CLEAN_PREREQUISITES += clean_vcs_runs
.PHONY: clean_vcs_runs
clean_vcs_runs: ## Remove the run directories inside the build directory
	rm -rf $(VCS_BUILD_DIR)/run_*

CLEAN_PREREQUISITES += clean_vcs
.PHONY: clean_vcs
clean_vcs: ## Clean the WHOLE vcs build directory
	rm -rf $(VCS_BUILD_DIR) $(VSIM_BUILD_DIR)/../../gen_rtl
