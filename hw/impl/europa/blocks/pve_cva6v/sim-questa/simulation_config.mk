# TODO: This was automatically generated, adaptions will need to be made
DFT = 0

# Configuration for the IP
IP_NAME            = pve_cva6v_p
TOP_LEVEL_MODULES  = pve_cva6v_p

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl/

BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

# Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
VSIM_VOPT_OPTS_EXT += -access=rw+/.

# Suppress warning: Missing connection for port xx_o'. Default value(if given) will not be used due to explicit empty named port connection.
VSIM_VOPT_OPTS_EXT += -suppress 2871

# Suppress sformatf error: $sformatf : Argument number (...) has an invalid format width.
VSIM_ELAB_OPTS_EXT += -suppress 8760
DFT_TEST_NAME =

VSIM_ERROR_ON_DANGEROUS_WARNING = 1
