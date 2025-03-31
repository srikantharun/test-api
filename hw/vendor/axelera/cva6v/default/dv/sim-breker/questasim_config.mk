#############################################
# Add VSIM Run and Elab options for cva6v
#############################################

include ../sim-mini-soc/questasim_config.mk

# Copy test specific files locally
BREKER_TEST_DIR ?= $(MAKEFILE_DIR)/../tests/breker
TBX             := $(shell find $(BREKER_TEST_DIR)/$(notdir $(ELF)) -type f -name *.tbx)
TCV             := $(shell find $(BREKER_TEST_DIR)/$(notdir $(ELF)) -type f -name *.tcv)

PLUSARGS_COMMON += +TREK_TBX_FILE=default.tbx

RUN_VSIM_PREREQUISITES += run_presim_breaker
.PHONY: run_presim_breaker
run_presim_breaker:
	@# Run Breker Presim
	mkdir -p $(VSIM_RUN_DIR)
	echo "Copying $(ELF) to rundir $(VSIM_RUN_DIR)/default)"
	cp $(ELF) $(VSIM_RUN_DIR)/default

	echo "Copying $(TBX) to rundir $(VSIM_RUN_DIR)/default)"
	cp $(TBX) $(VSIM_RUN_DIR)/default.tbx

	echo "Copying $(TCV) to rundir $(VSIM_RUN_DIR)/default)"
	cp $(TCV) $(VSIM_RUN_DIR)/default.tcv
