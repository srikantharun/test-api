# TODO: This was automatically generated, adaptions will need to be made

# Configuration for the IP
IP_NAME            = cva6v
TOP_LEVEL_MODULES  = cva6v

# Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
VSIM_VOPT_OPTS_EXT += -access=rw+/.

# Suppress sformatf error: $sformatf : Argument number (...) has an invalid format width.
VSIM_ELAB_OPTS_EXT += -suppress 8760
