# Set up environment variables
set RTL_PATH $::env(REPO_ROOT)
set BLOCK $BLOCK
set CORNER_CONDITION "tt_nominal_0p8500v_0p8500v_125c"
set SPEF_CONDITION "rcworst_125c"
set NETLIST $NETLIST

puts "BLOCK: $BLOCK"
puts "NETLIST: $NETLIST"

# Define design parameters
set DESIGN ${BLOCK}_p
set MEM_IP ${DESIGN}
puts "INFO: Design name is ${DESIGN}"
set eda_tool dc_shell

# Load tech_cell library
source ${RTL_PATH}/hw/ip/tech_cell_library/default/rtl/sf5a/tc_techlib.tcl

# Read in technology libraries
foreach tech_lib "${MEM_LIBS} ${REG_FILES}" {
    puts "Reading: ${tech_lib}"
    read_file -format db [glob ${tech_lib}/*${CORNER_CONDITION}*.db]
}

# List the loaded libraries
list_libraries

# Set synthesis results and PT report directories
set SYN_RESULTS_DIR "${RTL_PATH}/hw/impl/europa/blocks/${BLOCK}/results"
set PT_REPORTS_DIR "${RTL_PATH}/hw/impl/europa/blocks/${BLOCK}/pt_reports"
file mkdir ${PT_REPORTS_DIR}

# Check if synthesized netlist exists, read it if found
if {[file exists ${NETLIST}]} {
    puts "INFO: Reading in qsyn netlist ${NETLIST}"
} else {
    puts "ERROR: Netlist not found!"
    exit
}

# Read the netlist and set the current design
read_verilog ${NETLIST}
current_design ${DESIGN}

# Link the design to resolve references
link

# Get design information (ports, pins, cells)
get_ports *
get_pins *
get_cells *

# Create a 2.0 unit period clock named "fast_clk" on input ports matching "i*clk"
create_clock -add -name fast_clk -period 2.0 -waveform "0 1.0" [get_ports i*clk]

# Check if parasitics exists, read it if found
if { [info exists SPEF_CONDITION] && [file exists ${SYN_RESULTS_DIR}/${DESIGN}.spef.${SPEF_CONDITION}] } {
    puts "INFO: Reading parasitics ${SYN_RESULTS_DIR}/${DESIGN}.spef.${SPEF_CONDITION}"
    read_parasitics ${SYN_RESULTS_DIR}/${DESIGN}.spef.${SPEF_CONDITION}
} else {
    puts "SPEF_CONDITION not found. Continuing."
}

# TODO: Implement clock-gating enablement and configuration via PCTL.
# Set case analysis if the clock gating enable signal exists
#if { [info exists ip_cg_en] } {
#    set_case_analysis 1 [get_ports $ip_cg_en]
#}

# Enable power analysis and generate clock gate savings report
set power_enable_analysis true
report_clock_gate_savings -sequential -by_clock_gate -nosplit > ${PT_REPORTS_DIR}/clock_gate_savings.all.${DESIGN}.rpt
puts "INFO: Clock gate savings report generated at ${PT_REPORTS_DIR}/clock_gate_savings.all.${DESIGN}.rpt"

# Exit the tool
exit
