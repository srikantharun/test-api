# Set up environment variables
set RTL_PATH $::env(REPO_ROOT)
set BLOCK aic_did
set CORNER_CONDITION tt_nominal_0p8500v_0p8500v_125c
set SPEF_CONDITION rcworst_125c

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
if {[file exists ${SYN_RESULTS_DIR}/${DESIGN}.mapped.v]} {
    puts "INFO: Reading in qsyn netlist ${SYN_RESULTS_DIR}/${DESIGN}.mapped.v"
} else {
    puts "ERROR: Netlist not found!"
    exit
}

# Read the netlist and set the current design
read_verilog ${SYN_RESULTS_DIR}/${DESIGN}.mapped.v
current_design ${DESIGN}

# Link the design to resolve references
link

# Get design information (ports, pins, cells)
get_ports *
get_pins *
get_cells *

#set cells [get_cells *aic_did_p*]
#puts "Cells found: $cells"

# Check if parasitics exists, read it if found
if { [info exists SPEF_CONDITION] && [file exists ${SYN_RESULTS_DIR}/${DESIGN}.spef.${SPEF_CONDITION}] } {
    puts "INFO: Reading parasitics ${SYN_RESULTS_DIR}/${DESIGN}.spef.${SPEF_CONDITION}"
    read_parasitics ${SYN_RESULTS_DIR}/${DESIGN}.spef.${SPEF_CONDITION}
} else {
    puts "SPEF_CONDITION not found. Continuing."
}
create_clock -add -name fast_clk -period 2.0 -waveform "0 1.0" [get_ports i*clk]

#source $::env(REPO_ROOT)/hw/impl/europa/blocks/aic_did/synth-rtla/constraints/aic_did_p_constraints.tcl
#read_sdc $::env(REPO_ROOT)/hw/impl/europa/blocks/aic_did/synth-rtla/constraints/dft/aic_did_p.cnsAtspeed.sdc
#read_parasitics $::env(REPO_ROOT)/hw/impl/europa/blocks/aic_did/results/aic_did_p.spef.cbest_125c 

# Set case analysis if the clock gating enable signal exists
#if { [info exists ip_cg_en] } {
#  set_case_analysis 1 [get_ports $ip_cg_en]
#}

# Enable power analysis, perform power analysis and generate reports
set power_enable_analysis true


# Update timing
update_timing
write_sdf -o ${SYN_RESULTS_DIR}/${DESIGN}.sdf

# Calculate power before reporting
update_power                                 
report_power -verbose > power_report.txt
report_timing > timing_report.txt

# Exit tool
exit
