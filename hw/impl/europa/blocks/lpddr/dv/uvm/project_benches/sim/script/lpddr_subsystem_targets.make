all: work_setup compile_design compile_tb opt sim

compile_tb:
	vlog $(VLOG_OPTIONS) $(COMPILE_DEFINES) $(BASE_DEPENDENTS) $(INCDIRS) $(HVL_SV_SOURCE) $(HDL_SV_SOURCE)  | tee $(LOG_FILE_DIR)/compile_tb_output

work_setup:
	@echo 
	@echo --------------------------------------------------
	@if test -d $(WORK_DIR); then \
		echo Going with current work dir : $(WORK_DIR); \
	else\
		echo Creating work dir : $(WORK_DIR); \
		vlib $(WORK_DIR); \
	fi
	vmap work $(WORK_DIR);
	vmap mtiUVm $(METH_HOME);
	@if test -d $(LOG_FILE_DIR); then \
		echo Outputing to current log dir : $(LOG_FILE_DIR); \
	else\
		echo Creating log dir : $(LOG_FILE_DIR); \
		mkdir $(LOG_FILE_DIR); \
	fi
	@echo --------------------------------------------------

compile_design:
	@echo 
	@echo --------------------------------------------------
	@echo "               Compiling the Design"
	@echo --------------------------------------------------
	@echo 
	@if test -d $(realpath $(WORK_DIR))/lpddr_subsystem_dut; then \
		echo --------------------------------------------------; \
		echo Precompiled lpddr_subsystem_dut is already present in;\
	 	echo $(realpath $(WORK_DIR)),;\
	 	echo so skipping the compilation of DUT. Perform make;\
	 	echo clean if DUT is changed, to recompile it.;\
		echo --------------------------------------------------; \
	else\
		echo Compiling DUT file at $(realpath $(WORK_DIR))/lpddr_subsystem_dut; \
		vlib $(realpath $(WORK_DIR))/lpddr_subsystem_dut; \
		sh script/lpddr_subsystem_rtl_compile.sh  | tee $(LOG_FILE_DIR)/compile_des_output;\
	fi
	@echo ------------Done compiling the Design-------------
	@echo

opt:
	@echo 
	@echo --------------------------------------------------
	@echo "              Optimizing the Design"
	@echo --------------------------------------------------
	@echo 
	vopt $(VOPT_ARGS) $(VOPT_OPTIONS) hdl_top hvl_top -o top_opt | tee $(LOG_FILE_DIR)/vopt_output
	@echo ------------Done optimizing the Design------------
	@echo

sim:
	vsim $(VSIM_OPTIONS) top_opt $(UVM_OPTIONS) $(VSIM_PLUS_ARGS) +UVM_VERBOSITY=$(VERBOSITY) $(VSIM_DO_CMD) $(VSIM_LOG_CMD) $(VSIM_WAVE_CMD)

create_phy_init_details:
	sh script/create_phy_init_details.sh $(PI_OUTPUT_PATH) $(PI_DETAILS_PATH)

help: 
	more script/make_help.txt
####################
# Cleanup.

clean:
	rm -rf work transcript vsim.wlf

.PHONY: all compile_design compile_tb opt sim
