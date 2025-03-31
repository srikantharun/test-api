#############################################
# Add VCS Run and Elab options for cva6v
#############################################

VCS_RUN_OPTS         += -reportstats

ifeq ("$(VCS_DUMP_TYPE)", "vpd")
ifeq ("$(VCS_GUI_TYPE)", "dve")
ifeq ("$(DEBUG)", "1")
# RG: DVE + VPD
VCS_RUN_OPTS_TCL = -ucli -do ../../dump_vpd.tcl
endif
endif
endif

ifeq ("$(VCS_DUMP_TYPE)", "fsdb")
ifeq ("$(VCS_GUI_TYPE)", "verdi")
ifeq ("$(DEBUG)", "1")
# RG: Verdi + FSDB
VCS_RUN_OPTS_TCL = -ucli -do ../../dump_fsdb.tcl
endif
endif
endif
