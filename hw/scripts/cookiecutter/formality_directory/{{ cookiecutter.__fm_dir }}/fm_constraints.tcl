if { $NETLIST_TYPE == "rtla" } {
  puts "INFO: applying formality constraints for rtla netlist"
} elseif { $NETLIST_TYPE == "pdsyn" } {
  puts "INFO: applying formality constraints for pdsyn netlist"
} elseif { $NETLIST_TYPE == "rtl_dft" } {
  puts "INFO: applying formality constraints for DFT inserted RTL"
} elseif { $NETLIST_TYPE == "rtl" } {
  puts "INFO: applying formality constraints for released RTL"
} else {
  puts "ERROR: given netlist type $NETLIST_TYPE not supported."
  exit
}
