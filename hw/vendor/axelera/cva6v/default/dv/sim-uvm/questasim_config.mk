#############################################
# Add VSIM Run and Elab options for cva6v
#############################################

VSIM_VOPT_OPTS_EXT += -access=rw+/. # Short term - avoids internal segfault with vsim
VSIM_VLOG_OPTS_EXT += -suppress 2121,2244,2696,2697
VSIM_VLOG_OPTS_EXT += -suppress 2147,2577,3838,7034,7060,13262 # SVT VIP related
VSIM_ELAB_OPTS_EXT += -suppress 7034,8754,8760
VSIM_ELAB_OPTS_EXT += -suppress 3838,8451 # SVT VIP related

VSIM_COVER_ALL ?= 0

ifeq ("$(COVERAGE)", "1")
ifeq ("$(VSIM_COVER_ALL)", "0")
# do not generate code coverage by default, but only function coverage
	VSIM_VOPT_OPTS_COVERAGE =
endif
endif

ifeq ("$(DEBUG)", "1")
VSIM_RUN_OPTS       =-qwavedb=+maxbits=320000  # note that both +maxbits and +memory do not work if both are set!
#VSIM_RUN_OPTS       =-qwavedb=+memory=64,2   # uncomment this if memory dump is desired

endif
