variable script_dir [file dirname  [file normalize [info script]]]

if { [info exists env(PA_DESIGN_STAGE)] } {
  set design_stage $env(PA_DESIGN_STAGE)
}

# Configure "flow_step" and source the common config file for all major flow steps.
set flow_step "Elaborate"
source ${script_dir}/base/config.tcl

# Define list of Blackboxes (if any).
# ####################
# # Need to review
# ####################
#pa_set black_box_modules {}

# Optional: skip certain modules and optionally also its module instances from
# being elaborated. Difference is that 'skip_modules' creates a Blackbox,
# while 'skip_module_insts' also removes the instances.
#pa_set elaborate_skip_modules <module_name1>:<module_name2>
#pa_set elaborate_skip_module_insts <module names, optionally with wildcards>

# Optional: let the tool automatically declare missing modules as black boxes.
#pa_set elaborate_auto_black_box true

# Optional: set the RTL parameters for a specific mode used during Elaborate.
#pa_set parameter_maps <param1Name>=<value1> <param2Name>=<value2>

# ##############################################################################
# ########################### READ THE RTL CODE FILES ##########################
# ##############################################################################
# read in the source code with "CompileFile" commands.
if { $design_stage == "gate" } {
  CompileFile -type verilog -sv true -file $NETLIST_FILE
  pa_set gate_level_netlist true
} else {
  source ${script_dir}/base/compile_rtl.tcl

  # Globally configure parser to be compliant to specific Verilog language standard.
  # ####################
  # # Need to review
  # ####################
  #pa_set verilog_2001 true
  pa_set system_verilog true

  # Optional: include current directory into search path for include files.
  # ####################
  # # Need to review
  # ####################
  #pa_set elaborate_incdir_search_src true

  # All non-instantiated memories with behavioral description are bit-blasted into registers.
  # ####################
  # # Need to review
  # ####################
  pa_set blast_regfile all

  # Optional: enable register slicing (don't merge them inside a common multi-bit register).
  pa_set disable_register_slicing false

  # Optional: map behavioral descriptions of (clock gating etc.) cells to lib files
  # Limitation: currently only works for Verilog, not for VHDL!
  # ####################
  # # Need to review
  # ####################
  #MapBehavioralCell -module <RTL module> -lib_cell <lib cell name> \
  #  -pin_mapping {{<RTL pin 1> <libcell pin 1>} {<RTL pin 2> <libcell pin 2>} ...}
}

# ##############################################################################
# ############################ ELABORATE THE DESIGN ############################
# ##############################################################################
# Optional: write out a power database (PDB) for elaborate step.
# This PDB is needed for SDC file import.
pa_set elaborate_write_power_db true
pa_set power_db_name $PDB_DIR/${filename}_elab${elab_suffix}.pdb

# Check if SDC flow is chosen => need to write a PDB; error out if not correctly set up.
if { $use_sdc_input_for_clocks && ![pa_set elaborate_write_power_db] } {
  puts "Error: Flow is configured to read SDC for clock information, but required Elaborate PDB won't be saved! Exiting ..."
  exit 1
}

# Optional: accept non-LRM compliant VHDL/Verilog/SystemVerilog code.
# ####################
# # Need to review
# ####################
#pa_set elaborate_relax_syntax_check true

pa_set elaborate_report_file $RPT_DIR/${filename}_elab${elab_suffix}.rpt
pa_set elaborate_report_options "optimization module"
pa_set elaborate_log $LOG_DIR/${filename}_elab${elab_suffix}.log

if { [info exists BBOX_MODULES] } {
  pa_set black_box_modules ${BBOX_MODULES}
}

if { [info exists MAP_MODULES] } {
  foreach mod ${MAP_MODULES} {
    set mod_split [mcsplit [lindex $mod 0] " "]
    set mod_from [lindex $mod_split 0]
    set lib_to   [lindex $mod_split 1]
    puts "Map $mod_from onto $lib_to"
    MapBehavioralCell -module $mod_from -lib_cell $lib_to -pin_mapping [lindex $mod 1]
  }
}

Elaborate

exit
