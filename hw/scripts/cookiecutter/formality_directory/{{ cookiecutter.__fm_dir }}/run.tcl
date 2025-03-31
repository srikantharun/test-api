# NETLIST_TYPE should be set from the cmdline using the -x directive
# If NETLIST_TYPE not set, the default is rtla

#source $REPO_ROOT/fm_ip_versions.tcl

if ![info exist NETLIST_TYPE] {
  puts "WARNING: NETLIST_TYPE not set. Defaulting to rtla"
  set NETLIST_TYPE "rtla"
}

if { $NETLIST_TYPE == "rtla" } {
  puts "INFO: using rtla netlist as compare netlist"
} elseif { $NETLIST_TYPE == "pdsyn" } {
  set PD_RELEASE_VERSION  $SYN_SUB_VER_{{ cookiecutter.block_name }}
  puts "INFO: using $NETLIST_TYPE from $PD_RELEASE_DIR/$PD_RELEASE_VERSION"
} elseif { $NETLIST_TYPE == "rtl_dft" } {
  puts "INFO: using DFT inserted RTL as implementation design"
} elseif { $NETLIST_TYPE == "rtl" } {
  puts "INFO: RTL v.s. RTL"
} else {
  puts "ERROR: unkown netlist type $NETLIST_TYPE"
  exit
}
