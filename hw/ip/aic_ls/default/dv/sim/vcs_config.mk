
# Specify the debug access:
#VCS_VLOGAN_OPTS += +define+SVT_ACE5_ENABLE #TODO: enable for AXI5
VCS_VLOGAN_OPTS += +define+SVT_UVM_TECHNOLOGY
VCS_VLOGAN_OPTS += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_MESSAGING
VCS_VLOGAN_OPTS += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_DATA_MESSAGING
VCS_VLOGAN_OPTS += +define+SVT_MEM_ENABLE_INTERNAL_MESSAGING
VCS_VLOGAN_OPTS += +define+SVT_MEM_LOGIC_DATA # so that axi txn data is of type logic and not bit
VCS_VLOGAN_OPTS += -ntb_opts uvm-1.2
VCS_ELAB_OPTS   += -ntb_opts uvm-1.2
#VCS_ELAB_OPTS   += -debug_access+all
VCS_VLOGAN_OPTS += -debug_acc+all+dmptf -debug_region+cell+encrypt
VCS_ELAB_OPTS += -debug_acc+all+dmptf -debug_region+cell+encrypt
#############################################
# Add VCS Run and Elab options for cva6v
#############################################

# Provide the testbench toplevel name
HDL_TOP          ?= 1

ifeq (${RUN_UNR}, 0)
  TOP_LEVEL_MODULES  = hdl_top
  VCS_ELAB_OPTS     += -top hdl_top
  ifeq ($(HVL_TOP),1)
    TOP_LEVEL_MODULES += hvl_top
    VCS_ELAB_OPTS     += -top hvl_top
  endif
endif #RUN_UNR

NO_DUT           ?= 0

ifeq ($(REGRESSION), 1)
  VCS_RUN_OPTS += +REGRESSION=1
endif

# SIM RUN
TEST_PROGRAM_OUT ?= default

#VCS_ELAB_OPTS += -sverilog ../../../c/dpi_memory.cc
#VCS_ELAB_OPTS += -sverilog ../../../c/dummy.cc

VCS_RUN_OPTS         += -reportstats
VCS_RUN_OPTS         += -sv_lib $(SPIKE_HOME)/lib/libriscv
VCS_RUN_OPTS         += ++./$(TEST_PROGRAM_OUT).o
VCS_RUN_OPTS         += +elf_file=./$(TEST_PROGRAM_OUT).o
VCS_RUN_OPTS         += +tohost_addr=0000000080001000
VCS_RUN_OPTS         += +isa="rv64gcv_zfh_zvfh_zicntr_zihpm"
VCS_RUN_OPTS         += +march="rv64gc_zve32f_zfh_zfhmin"
VCS_RUN_OPTS         += +varch="vlen:4096,elen:32"

ifeq ("$(VCS_DUMP_TYPE)", "vpd")
ifeq ("$(VCS_GUI_TYPE)", "dve")
# RG: DVE + VPD
VCS_ELAB_OPTS += -debug_access+all
VCS_RUN_OPTS_TCL = -ucli -do ../../dump_vpd.tcl
endif
endif

ifeq ("$(VCS_DUMP_TYPE)", "fsdb")
ifeq ("$(VCS_GUI_TYPE)", "verdi")
# RG: Verdi + FSDB
VCS_ELAB_OPTS += -debug_access+all
VCS_RUN_OPTS_TCL = -ucli -do ../../dump_fsdb.tcl
endif
endif

