# TCL file invoked from VCS's simv at run-time using this: -ucli -do <this file>

# Syntax: fsdbDumpvars [depth] [instance] [option]*
##############################################################################
# Option                     Description
##############################################################################
# +mda                       Dumps memory and MDA signals in all scopes.
# +packedmda                 Dumps packed signals
# +struct                    Dumps structs
# +skip_cell_instance=mode  Enables or disables cell dumping
# +strength                  Enables strength dumping
# +parameter                 Dumps parameters
# +power                     Dumps power-related signals
# +trace_process             Dumps VHDL processes
# +no_functions              Disables dumping of functions
# +sva                       Dumps assertions
# +Reg_Only                  Dumps only reg type signals
# +IO_Only                   Dumps only IO port signals
# +by_file=<filename>        File to specify objects to add
# +all                       Dumps memories, MDA signals, structs, unions,power, and packed structs

#fsdbDumpfile  "test.fsdb"
# Change the TB file name according to your TB
if {[info exists ::env(UVM_TESTNAME)]} {
  set dumpname $::env(UVM_TESTNAME)
} else {
  set dumpname "test"
}
append dumpname "_seed_"
if {[info exists ::env(SIM_SEED)]} {
  append dumpname $::env(SIM_SEED)
  append dumpname "."
} else {
  append dumpname "1."
}
if {[info exists ::env(DUMP_TYPE)]} {
  set dumptype $::env(DUMP_TYPE)
  append dumpname $::env(DUMP_TYPE)
} else {
  set dumptype "fsdb"
  append dumpname "fsdb"
}
if {$dumptype == "fsdb"} {
  fsdbDumpvars  0 hdl_top  +all +packedmda +fsdbfile+$dumpname
} else {
    dump -file $dumpname -type VPD
    call {$vcdpluson(0, hdl_top)}
}
#dump -file waves.vpd -type VPD
#dump -add / -depth 0 -aggregates
run
quit
