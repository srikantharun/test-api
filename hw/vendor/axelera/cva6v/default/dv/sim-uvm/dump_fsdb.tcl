# TCL file invoked from VCS's simv at run-time using this: -ucli -do <this file>

if {[info exists ::env(TESTNAME)]} {
  set dumpname $::env(TESTNAME)
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
append dumpname "fsdb"
fsdbDumpvars  0 hdl_top  +all +packedmda +fsdbfile+$dumpname


run
quit
