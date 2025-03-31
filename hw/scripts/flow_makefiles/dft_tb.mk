########################################
##@ DFT TB mode, supports VCS and VSIM
########################################

########################################
##@ Validate the configuration:
########################################
$(call check_defined, PATTERN_NAME, specify which pattern to run)
$(call check_defined, DFT_TB_ROOT, specify a DFT TB root. This will contain your pattern files.)

########################################
##@ Common VCS/VSIM Configuration
########################################

.PHONY: link_dft_tb
link_dft_tb:
	@# If a dft pattern simulation is executed, link the pattern files
	if [ ! -z "$(PATTERN_NAME)" ]; then \
		ln -sf $(DFT_HOME)/$(IP_NAME)/Latest/patterns/${PATTERN_NAME}.sv09 $(DFT_TB_ROOT)/${PATTERN_NAME}.sv
		ln -sf $(DFT_HOME)/$(IP_NAME)/Latest/patterns/${PATTERN_NAME}.sv09.* $(DFT_TB_ROOT)
		if [ ! -e $(DFT_TB_ROOT)/ddr_ate_firmware ] && [ -e "$(DFT_HOME)/$(IP_NAME)/Latest/tsdb/logic_test/tsdb_outdir/ddr_ate_firmware" ] ; then \
			ln -sf $(DFT_HOME)/$(IP_NAME)/Latest/tsdb/logic_test/tsdb_outdir/ddr_ate_firmware $(DFT_TB_ROOT)
		fi
	fi

COMPILE_VCS_PREREQUISITES  += link_dft_tb
COMPILE_VSIM_PREREQUISITES += link_dft_tb

# Questa specific custom compile configuration
VSIM_VOPT_OPTS += +nospecify

# VCS specific custom compile configuration
VCS_ELAB_OPTS_DEBUG += -debug_region+cell -debug_region+lib
VCS_ELAB_OPTS += +nospecify +notimingchecks -assert disable

# Run configuration
VSIM_RUN_OPTS += +NEWPATH=$(realpath $(DFT_TB_ROOT))
VCS_RUN_OPTS  += +NEWPATH=$(realpath $(DFT_TB_ROOT))

# Extend rundir name
DFT_TEST_NAME = _$(PATTERN_NAME)

########################################
## Clean targets:
########################################
CLEAN_PREREQUISITES += clean_dft_tb
.PHONY: clean_dft_tb
clean_dft_tb:
	@if [ -e $(DFT_TB_ROOT)/${PATTERN_NAME}.sv* ]; then \
	  find $(DFT_TB_ROOT)/${PATTERN_NAME}.sv -type l -exec rm -v '{}' +
	  find $(DFT_TB_ROOT)/${PATTERN_NAME}.sv09* -type l -exec rm -v '{}' +
	fi
