##% SPIKE_BUILD_DIR @@ build_vsim_<ip> @@ dedicated build directory for spike
SPIKE_BUILD_DIR ?= $(MAKEFILE_DIR)/build_spike_$(IP_NAME)$(DFT_TEST_NAME)

##% SPIKE_RUN_DIR @@ run_spike_<UVM>_<seed> @@ dedicated run directory for spike in the build directory
SPIKE_RUN_DIR ?= $(SPIKE_BUILD_DIR)/run_spike_$(TESTNAME)_$(SEED)$(subst /,_,$(subst +,_,$(subst $(subst ,, ),_,$(PLUSARGS))))

SPIKE_STEPS := 200000000
VERIFSDK_CI_CLEANUP ?= 0

# Allow optional disassembly stripping (default enabled)
STRIP_DISASSEMBLY ?= 0  # Set to 0 in simulation_config.mk to disable

.PHONY: $(SPIKE_RUN_DIR)
$(SPIKE_RUN_DIR):
	@# Create the build directory
	mkdir -p $@

PRE_SIM_TARGETS += run_spike
.PHONY: run_spike
run_spike: $(SPIKE_RUN_DIR)
	@# Run Spike on given elf
	if [ ! -e ${ELF} ]; then echo "ERROR: Failed to locate ${ELF}"; false; fi

	cd $(SPIKE_RUN_DIR)
	cp $(ELF) default

	# Create objdump
	riscv64-unknown-elf-objdump -d default > default.S

	# Run Spike
	$(GRID_CMD)	bash -c "(
		$(SPIKE_HOME)/bin/spike --steps=${SPIKE_STEPS} --log-commits -m0x2000000000:0x800000000,0x18000000:0x400000 --isa=rv64imafcv_zfh_zvfh_zicntr_zihpm_zicsr_zifencei_zicbom --varch=vlen:4096,elen:32 --priv=msu --pmpregions=0 -l --log=instruction_dump_spike_id0.log default |& tee spike.stdout
		if grep -Eq "FAILED" spike.stdout; then
		  exit 1
		fi
		if grep -q "Maximum" spike.stdout; then
		  exit 1
		fi
		# Convert Log to csv
		cva6_spike_log_to_trace_csv --log instruction_dump_spike_id0.log --csv raw_spike_rvvi.csv --vector --full_hex
		# Post Process csv
		cva6v_post_process_csv --input raw_spike_rvvi.csv --output spike_rvvi.csv
		# Conditionally strip disassembly
		if [ \"$(STRIP_DISASSEMBLY)\" -eq \"1\" ]; then
		  cva6v_strip_disassembly
		  cp inst_cov_dis.log  $(VSIM_RUN_DIR)
		fi
	)"
	echo "Spike run completed. Run directory: $(realpath $(SPIKE_RUN_DIR))"
	echo "Using Spike binary: $(SPIKE_HOME)/bin/spike"

.PHONY: compare_trace_vsim
compare_trace_vsim:
	@# Copy Spike logs locally
	cd $(VSIM_RUN_DIR)
	cp $(SPIKE_RUN_DIR)/* .
	rm -rf "$(SPIKE_RUN_DIR)"/*

	# Generate hdl logs
	sts=0

	$(GRID_CMD)	bash -c "(
		spike-dasm --isa=rv64imafcv_zfh_zvfh_zicntr_zihpm < trace_rvvi_hart_00.dasm > sim_rvvi.log || sts=1
		cva6v_sim_log_to_csv --log  sim_rvvi.log --csv raw_sim_rvvi.csv --vector --full_hex || sts=1
		cva6v_post_process_csv --input raw_sim_rvvi.csv --output sim_rvvi.csv || sts=1 )"

	# Compare
	diff --unified=0 spike_rvvi.csv sim_rvvi.csv > sim_rvvi.diff || sts=1

	# generate files for fw_trace_utils
	mkdir -p fw_trace_utils_sim_files
	ln -sf  $(VSIM_RUN_DIR)/default  $(VSIM_RUN_DIR)/fw_trace_utils_sim_files/default
	ln -sf  $(VSIM_RUN_DIR)/default.S  $(VSIM_RUN_DIR)/fw_trace_utils_sim_files/default.S
	ln -sf  $(VSIM_RUN_DIR)/trace_rvvi_hart_00.dasm   $(VSIM_RUN_DIR)/fw_trace_utils_sim_files/instruction_dump_rvvi_id0.log

	if [ $$sts -ne 0 ] ; then \
		echo "compare_trace_vsim : FAILED"
		if [ -e PASSED ]; then \
			mv PASSED FAILED; \
		fi; \
	fi

	if [ "$(VERIFSDK_CI_CLEANUP)" -ne 0 ]; then \
	    if [ -e PASSED ]; then \
	        rm -rf *; \
	        touch PASSED; \
	    fi; \
	fi
	echo "VSIM run completed. Run directory: $(realpath $(VSIM_RUN_DIR))"

.PHONY: compare_trace_vsim
compare_trace_vcs:
	@# Copy Spike logs locally
	cd $(VCS_RUN_DIR)
	cp $(SPIKE_RUN_DIR)/* .

	# Generate hdl logs
	sts=0
	spike-dasm --isa=rv64imafcv_zfh_zvfh_zicntr_zihpm < trace_rvfi_hart_00.dasm > simulator.log || sts=1
	cva6v_sim_log_to_csv --log  simulator.log --csv simulator.csv || sts=1

	# Compare
	diff spike.csv simulator.csv > simulator.diff || sts=1

	if [ $$sts -ne 0 ] ; then \
		echo "compare_trace_vcs : FAILED"
		if [ -e PASSED ]; then \
			mv PASSED FAILED; \
		fi \
	fi
