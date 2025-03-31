# TODO: This was automatically generated, adaptions will need to be made

# Configuration for the IP
IP_NAME            = l1
TOP_LEVEL_MODULES  = l1_tb

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/design_tb

# Custom compile configuration

# VSIM_VLOG_OPTS  =
# VSIM_VCOM_OPTS  =
## workaround for vsim for failing xbar on spill:
 # VSIM_VOPT_OPTS  = -access=r+/.
# VSIM_ELAB_OPTS  =

# VSIM run configuration
ifeq ("$(DEBUG)", "1")
VSIM_RUN_OPTS  =-qwavedb=+maxbits=320000
endif

# VSIM usage configuration
VSIM_DEBUG_EN = 0
