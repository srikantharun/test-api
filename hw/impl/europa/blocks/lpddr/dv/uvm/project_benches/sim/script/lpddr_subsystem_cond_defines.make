ifeq ($(VISUALIZER),1)
  VOPT_OPTIONS += -debug -designfile $(LOG_FILE_DIR)/lpddr_subsystem_design.bin
  VSIM_DUMP_CMD =
  VSIM_WAVE_CMD = -qwavedb=+nologtimezero+signal+transaction+class+cells+memory+wavefile=$(LOG_FILE_DIR)/$(LOG_NAME).db
  ifeq ($(SIM_MODE),"gui")
    VSIM_OPTIONS += -visualizer=$(LOG_FILE_DIR)/lpddr_subsystem_design.bin
    VSIM_DO_CMD = -do '$(VSIM_COV_CMD) $(VSIM_DUMP_CMD)'
  endif
endif

ifeq ($(NO_WAVE),1)
  VSIM_DUMP_CMD =
  VSIM_WAVE_CMD =
endif
