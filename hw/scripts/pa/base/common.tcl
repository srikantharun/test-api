# ##############################################################################
# ######################### ADVANCED FLOW SETUP SCRIPT #########################
# ##############################################################################
#
# This script contains advanced settings for power analysis and reduction.
# The design specific settings are generally performed in 'config.tcl'
# (this script is sourced by 'config.tcl').
#
# This script requires customization when technology and main stdcell libraries
# are changed, or when optimization, Multi-VT or other advanced settings need
# to be adapted to specific flows.
#
# Don't change the structure in this script unless you know what you are doing!
#
# Version History:
# 2019-09-26 (HB): initial version
# 2020-05-07 (HB): added 2020 R1 feature: AnalyzeStaticEfficiency (run_ase.tcl)
# 2020-05-19 (HB): added support for SDC vectorless and SDC Reduction LEC flow
# 2021-04-23 (HB): minor fix for "suffix" and "SetClockGatingStyle (run_ase.tcl)
# 2021-04-24 (HB): add possibility to add further clocks to SDC-based flow
# 2021-05-06 (HB): introduce dummy 'flow_step' in 'config.tcl'
#
# ##############################################################################
# ########################## DIRECTORY STRUCTURE SETUP #########################
# ##############################################################################

# Sanity check if design data directory is present. Comment out if not used.
# ####################
# # Need to review
# ####################
if {![file exists $DESIGN_DATA_DIR]} {
  puts "ERROR: Design data input directory '$DESIGN_DATA_DIR' is not present! Exiting ..."
  exit 1
}
# Create directory structure if not already present.
if {![file exists $LOG_DIR]} { exec mkdir -p $LOG_DIR }
if {![file exists $RPT_DIR]} { exec mkdir -p $RPT_DIR }
if {![file exists $CSV_DIR]} { exec mkdir -p $CSV_DIR }
if {![file exists $PDB_DIR]} { exec mkdir -p $PDB_DIR }
if {![file exists $WORK_DIR]} { exec mkdir -p $WORK_DIR }
if {![file exists $GRAPH_DIR]} { exec mkdir -p $GRAPH_DIR }
if {![file exists $PACE_DIR]} { exec mkdir -p $PACE_DIR }

# Introduce $PACE_DIR only for PACE-based flow.
if { $use_pace_based_flow } {
  if {![file exists $PACE_DIR]} { exec mkdir -p $PACE_DIR }
}

# ##############################################################################
# ############################### GLOBAL SETTINGS ##############################
# ##############################################################################

# Define the top module for Elaborate, ReadSDC, PACE generation.
pa_set top $top_module

# Set up names for output files (PDBs, reports, log files, csv, graph etc.)
# -------------------------------------------------------------------------
# File name settings; per default matching "$top_module" name.
set filename ${top_module}
# Optional: add date and time stamp to the name.
# The setting needs to come from Linux "date" command outside of PA.
# Add the following line to your Linux run script:
#   bash: export PA_run_time_stamp=`date "+%FT%T"`
#   csh:  setenv PA_run_time_stamp `date +"%FT%T"`
#if { [info exists env(PA_run_time_stamp)] } {
#  append filename "_$env(PA_run_time_stamp)"
#}

# Suffix for reporting settings: check and store design stage.
# Also apply "gate_level_netlist" setting.
if { ($design_stage == "gate") || ($design_stage == "post_syn") } {
  set elab_suffix ".gate"
  pa_set gate_level_netlist true
} elseif { $design_stage == "rtl" } {
  set elab_suffix ""
} else {
  puts "ERROR: Setting 'design_stage' has unsupported value: '$design_stage'!"
  exit 1
}

# Read in provided .lib file names and generate LDB if not already present.
# Otherwise directly use LDB if present.
source ${script_dir}/base/read_lib.tcl

# Optional: suppress unnecessary messages throughout the flow.
# ####################
# # Need to review
# ####################
#pa_set suppress_messages { <list of message IDs> }

# Define scenario file name (created during Elaborate, used in other flow steps).
pa_set scenario_file $WORK_DIR/${filename}${elab_suffix}.scn

# Global optimization settings
# ----------------------------
# ####################
# # Need to review
# ####################
# Tell all engines (Elaborate, but also Power Analysis and Reduction) about how
# the design should be optimized: "SetDontTouch":
# SetDontTouch -module <module or *> ...
# Optional: keep unused logic (in case of preliminary RTL code):
#   -delete_unloaded_path false
# Optional: high-effort optimization of enable expressions:
#   -optimize_enable_expression true ; # can increase Elaborate runtime by ~30%
# Optional: perform boolean optimization:
#   -boolean_optimization true ; # should improve logic power

# Optional: don't map logic to compound gates; use 2-input and/or/mux gates.
# Facilitates debugging/tracing through logic; impact on correlation to gate-level.
#pa_set dont_use_compound_gates true
#pa_set dont_use_aoi21_compound_gates true
#pa_set dont_enable_mux21_compound_gates true

# Leave config script for Elaborate step.
if { $flow_step == "Elaborate" } { return }
# Following settings are not used by Elaborate.

# ##############################################################################
# ########################## ACTIVITY RELATED SETTINGS #########################
# ##############################################################################

# Skip activity related settings for PACE generation or AnalyzeStaticEfficiency.
if { $flow_step != "WriteTechnologyFile" && $flow_step != "AnalyzeStaticEfficiency" } {

  # Suffix for reporting: add source of activity if not 'vcd_fsdb'.
  if { $source_of_activity_data == "vcd_fsdb" } {
    set suffix $elab_suffix

    # Optional: add FSDB/VCD filename and/or start and finish time to file names.
    #append filename "_[file tail [pa_set activity_file]]" ; # for file name only
    # or
    #append filename "_[regsub -all {\/} [pa_set activity_file] {_}]" ; # for path
    #append filename "_[pa_set start_time]_[pa_set finish_time]"

    # If sequence numbering is missing for an FSDB (FDB-9), declare that clock
    # transition is the first one recognized to ensure correct sequence of
    # signal changes in a RTL (unit-delay based) simulation file.
    pa_set order_clock_transition_first true

  } elseif { $source_of_activity_data == "saif" } {
    set suffix "_saif${elab_suffix}"

    # Optional: add SAIF filename to file names.
    #append filename "_[file tail [pa_set saif_file]]" ; # for file name only
    # or
    #append filename "_[regsub -all {\/} [pa_set saif_file] {_}]" ; # for path

  } elseif { $source_of_activity_data == "vectorless" } {
    set suffix "_vectorless${elab_suffix}"
    # If no manual VAF file specified, auto-generate VAF from average activity
    # and duty cycle values specified in '${script_dir}/base/generate_vaf_file.tcl'.
    if { [pa_set vectorless_input_file] == "" } {
      pa_set vectorless_input_file $WORK_DIR/${top_module}${suffix}.vaf
    }
  } else {
    puts "ERROR: Setting 'source_of_activity_data' has unsupported value: '$source_of_activity_data'!"
    exit 1
  }
  if { $source_of_activity_data != "vectorless" } {
    # Enables activity propagation when simulation dump is not complete.
    pa_set mixed_sim_prob_estimation true
  }
} else {
  set suffix $elab_suffix
}

# Leave config script for GenerateActivityWaveforms step.
if { $flow_step == "GenerateActivityWaveforms" } { return }
# Following settings are not used by GenerateActivityWaveforms.

# ##############################################################################
# ########################### CLOCK RELATED SETTINGS ###########################
# ##############################################################################

# Optional: trace full clock domains instead of only clock tree.
# This allows to report clock domain specific power, but also reports clock
# tracing conflicts in data paths, as clocks are traced through the registers
# to the end of the related data paths, which can increase tracing 'conflicts'.
# ####################
# # Need to review
# ####################
set clock_tree_trace_domain false ; # valid values: "true" or "false"

if { $use_sdc_input_for_clocks } {

  # Clock names are imported through SDC
  # ------------------------------------
  # Elaborate PDB as input to map the SDC commands.
  pa_set power_db_name ${PDB_DIR}/${filename}_elab${elab_suffix}.pdb
  # Optional: only limit SDC import to clock definitions.
  # This also prohibits recognition of clock transitions(!).
  #pa_set sdc_only_clock_commands true

  # clock mode: 'infer' to infer clock gates and repeater in RTL,
  #             'trace' don't infer clock gates/repeater in gate-level,
  #             'ideal' don't infer clock gates, treat (HFN) clock net as ideal.
  if { $design_stage == "gate" } {
    pa_set sdc_clocks_mode trace
    pa_set sdc_clocks_gated false
    pa_set sdc_clocks_ecg false
  } elseif { $design_stage == "post_syn" } {
    pa_set sdc_clocks_mode ideal
    pa_set sdc_clocks_gated false
    pa_set sdc_clocks_ecg false
  } else {
    pa_set sdc_clocks_mode infer
    # Exception for Reduction LEC step: deactivate inferred clock gating.
    if { $flow_step == "Reduction_LEC" } {
      pa_set sdc_clocks_gated false
      pa_set sdc_clocks_ecg false
    } else {
      pa_set sdc_clocks_gated true
      pa_set sdc_clocks_ecg true
    }
  }
  # Activate tracing clock domains if specified above.
  if { $clock_tree_trace_domain } {
    pa_set sdc_trace_domain true
  }
  # Output file for clock commands.
  pa_set sdc_out_file ${WORK_DIR}/${filename}_ReadSDC${elab_suffix}.scr
  # Output file for vectorless information on clocks (not used).
  # For a vectorless approach original vectorless file name needs to be saved.
  if { $source_of_activity_data == "vectorless" } {
    set save_vectorless_file [pa_set vectorless_input_file]
  }
  pa_set vectorless_input_file ${WORK_DIR}/${filename}_ReadSDC${elab_suffix}.vaf
  # Additional files for (primary input) transition time, (primary output) loads.
  pa_set transition_time_file ${WORK_DIR}/${filename}_ReadSDC${elab_suffix}.tt
  pa_set load_file ${WORK_DIR}/${filename}_ReadSDC${elab_suffix}.loads
  pa_set sdc_append_in_side_files true
  # Set to "false" when additional data (input slew, case analysis etc.) should
  # be imported from SDC into PowerArtist as well.
  # ####################
  # # Need to review
  # ####################
  pa_set sdc_comment_side_files true
  # Log file for ReadSDC command.
  pa_set sdc_log ${LOG_DIR}/${filename}_ReadSDC${elab_suffix}.log

  # Skip ReadSDC if results are already present; risky with preliminary SDC data?
  # Otherwise, need to remove ${WORK_DIR}/${filename}_ReadSDC${elab_suffix} data.
  # The SDC file has to be re-generated for Reduction LEC step.
  # ####################
  # # Need to review
  # ####################
  if { ![file exists [pa_set sdc_out_file]] || $flow_step == "Reduction_LEC" } {
    if { [file exists [pa_set vectorless_input_file]] } {
      exec rm [pa_set vectorless_input_file] }
    if { [file exists [pa_set transition_time_file]] } {
      exec rm [pa_set transition_time_file] }
    if { [file exists [pa_set load_file]] } {
      exec rm [pa_set load_file] }
    ReadSDC
  }
  # Reset "sdc_files" and (potentially present) additional SDC input to default,
  # otherwise problems with PACE generation or missing files occur.
  pa_reset sdc_files
  pa_reset transition_time_file
  pa_reset load_file

  # Important: check content of "*_ReadSDC.scr" file before automatically sourcing!
  source [pa_set sdc_out_file]
  # Optional: manually add further clock definitions via separate file.
  if { [file exists "${script_dir}/addtl_clocks.tcl"] } {
    source "${script_dir}/addtl_clocks.tcl"
  }

  # Cleanup of files.
  if { [file exists "ReadSDC.tt"] } { exec rm "ReadSDC.tt" }

  # Vectorless input file from ReadSDC should not be used (only contains
  # SetStimulus for clock nets).
  # Need to restore original vectorless input file name for vectorless approach.
  # Also need to re-set the vectorless input file for AnalyzeStaticEfficiency.
  if { $source_of_activity_data != "vectorless" || \
    $flow_step == "AnalyzeStaticEfficiency" } {
    pa_reset vectorless_input_file
  } else {
    pa_set vectorless_input_file $save_vectorless_file
  }

} else {

  # Clock names are specified manually through "SetClockNet" commands
  # -----------------------------------------------------------------
  # Declaration of clocks for PowerArtist:
  # '-mode infer' for RTL designs (clock tree buffering will be estimated).
  # '-mode trace' for gate-level designs (clock tree will only be traced).
  # '-mode ideal' for post-synthesis correlation studies (clock nets are ideal).
  if { $design_stage == "gate" } {
    set clock_mode trace
    set clock_gating false
    set clock_gating_ecg false
    set clock_gating_ecg_effort low
  } elseif { $design_stage == "post_syn" } {
    set clock_mode ideal
    set clock_gating false
    set clock_gating_ecg false
    set clock_gating_ecg_effort low
  } else {
    set clock_mode infer
    # Exception for Reduction LEC step: deactivate inferred clock gating.
    if { $flow_step == "Reduction_LEC" } {
      set clock_gating false
      set clock_gating_ecg false
      set clock_gating_ecg_effort low
    } else {
      set clock_gating true
      set clock_gating_ecg true
      set clock_gating_ecg_effort high
    }
  }
  foreach clock $CLOCK_LIST {
    # Check if clock frequency is specified (required for PACE generation):
    if { [lindex $clock 1] == "-1" } {
      if { $flow_step == "WriteTechnologyFile" } {
        puts "Error: PACE generation specified, but required clock frequency for clock '[lindex $clock 0]' is not specified! Exiting ..."
        exit 1
      } else {
        if { [lindex $clock 2] == "-1" } {
          SetClockNet -name [lindex $clock 0] -mode $clock_mode -gate_clock $clock_gating \
            -enhanced_cg $clock_gating_ecg -cg_effort $clock_gating_ecg_effort \
            -trace_domain $clock_tree_trace_domain
        } else {
          SetClockNet -name [lindex $clock 0] -mode $clock_mode -gate_clock $clock_gating \
            -enhanced_cg $clock_gating_ecg -cg_effort $clock_gating_ecg_effort \
            -trace_domain $clock_tree_trace_domain \
            -transition_time [lindex $clock 2]
        }
      }
    } else {
      if { [lindex $clock 2] == "-1" } {
        SetClockNet -name [lindex $clock 0] -mode $clock_mode -gate_clock $clock_gating \
          -enhanced_cg $clock_gating_ecg -cg_effort $clock_gating_ecg_effort \
          -trace_domain $clock_tree_trace_domain \
          -frequency [lindex $clock 1]
      } else {
        SetClockNet -name [lindex $clock 0] -mode $clock_mode -gate_clock $clock_gating \
          -enhanced_cg $clock_gating_ecg -cg_effort $clock_gating_ecg_effort \
          -trace_domain $clock_tree_trace_domain \
          -frequency [lindex $clock 1] -transition_time [lindex $clock 2]
      }
    }
  }
}

# ##############################################################################
# ##################### ACTIVITY RELATED SETTINGS CONTINUED ####################
# ##############################################################################

# Finish vectorless setup; might need clock definitions from above.
# Needs to be skipped for AnalyzeStaticEfficiency.
if { $source_of_activity_data == "vectorless" && \
  $flow_step != "AnalyzeStaticEfficiency" } {
  # Create Vectorless activity file (VAF) from average activity and duty cycle
  # It can use clock definitions from above.
  source ${script_dir}/generate_idle_vaf_file.tcl
}

# ##############################################################################
# ##################### POWER ANALYSIS & REDUCTION SETTINGS ####################
# ##############################################################################

# Specify default output load on primary outputs.
# ####################
# # Need to review
# ####################
pa_set default_output_load 2.5e-14

# Specify default input transition time and default clock transition time.
# Recommendation for initial runs if transition times unknown:
# - default_transition:        7% of fastest clock
# - default_clock_transition: 10% of fastest clock
# ####################
# # Need to change
# ####################
pa_set default_transition_time 90ps
pa_set default_clock_transition_time 50ps

# Use scan flops as target for synthesis.
# ####################
# # Need to review
# ####################
pa_set use_non_scan_flops false
# Model load/fanout effect of scan chain insertion.
# ####################
# # Need to review
# ####################
pa_set infer_scan_fanouts true

# Apply power normalization for nets without annotated (i.e. propagated) activity.
pa_set enable_power_normalization true

# Report power related to specific supplies.
pa_set enable_power_per_supply_annotation true

# Optional: re-set negative library arc/cell negative power to 0.
#pa_set reset_library_negative_power true
#pa_set reset_negative_power true

# Clock related tracing options
# -----------------------------
# Check mux select activity which clock from mux input to propagate.
# Only applicable for average power and reduction, not for time-based power.
# !!  This usually makes the clock tracing simulation dependent !!
pa_set mux_select_activity_based_clock_tracing true
# Switch to old order-based clock priority (first one receives priority).
# Per default clock with higher frequency receives priority.
#pa_set frequency_independent_clock_tracing true

# Optional: activate event propagation for inferred buffers, clock gate and memory enables.
# Improves accuracy of CG/memory efficiency and power analysis at the cost of run time.
#pa_set event_based_analysis_signal_type "cg_enable mem_enable inferred_buffer"
pa_set event_based_analysis_signal_type "cg_enable mem_enable"

# Enhanced CG settings (enable term sharing for different registers)
# ------------------------------------------------------------------
# Activate new ECG algorithm. Former algorithms are "sns2", "sns", "gcf".
pa_set ecg_clique_creation sns3

# Optional 2020 settings for ECG, not supported for release 2019:
if { [lindex [split $wwVersion "."] 0] >= "2020" } {
  # Improves run time, but can lead to weaker clock enables.
  #pa_set ecg_containment_type disable
  # Identifies shared parts between enable expressions, can lead to higher run time.
  #pa_set ecg_bucketization_type disable
}

# Optional: treat regfiles as memories
# ####################
# # Need to review
# ####################
#pa_set categorize_regfile_as_memory true

# Memory definitions (mostly) for ReducePower and AnalyzeStaticEfficiency
# -----------------------------------------------------------------------
# Define Memories and their interface pins, so that the memory related power
# reduction PowerBots can fully recognize them (and their read/write/sleep modes).
# These settings are required for generating the GAF (for power reduction) already.
# Wildcards are supported for library name, cell names and pin names.
# ####################
# # Need to review
# ####################
#DefineMemory -library <libName> -cell <cell_name> \
#             -read_address {} -write_address {} -data {} \
#             -access_enable {read/write_access_en_pin_name(s)} -memory_enable {en_pin}
# (and optional: -sleep {} -power_down {} )

# Define debug messages.
# Here: add debug information for memory recognition (present in gaf_red.log).
pa_set activity_debug_flags H

# ##############################################################################
# ################## CELL USAGE AND WIRE CAP RELATED SETTINGS ##################
# ##############################################################################

if { [pa_set gate_level_netlist] } {
  # For gate-level: need to import corresponding SPEF file (which matches netlist).
  ReadParasitics -path ${top_module} -file $spef_file

  # Optional for post-layout gate-level analysis:
  # Don't estimate net capacitances if these are not present in SPEF file above.
  # ####################
  # # Need to review
  # ####################
  if {0} {
    if { $design_state == "gate" } {
      pa_set no_module_net_capacitances true

      # Leave script for non-pace run or PACE run except PACE generation:
      if { !use_pace_based_flow  || $flow_step != "WriteTechnologyFile" } {
        return
      }
    }
  }
}

if { !$use_pace_based_flow } {

  # non-PACE related settings
  # -------------------------
  # Following settings are only used for RTL (or mixed RTL/gate-level) designs.

  # Wire cap estimation required for all nets (RTL).
  # Wireload model selection to estimate wire caps (if no PACE cap model is used).
  # SetCapEstimation uses built-in wireload models (down to 28nm).
  # ####################
  # # Need to change
  # ####################
  pa_set wireload_library <wireload_library_name>
  SetWireLoadModel -name <model_name> -library <lib_name> -instance $top_module
  #SetCapEstimation -technology 28 -scale 0.5 -area_scale 0.5

  # Manually define cell usage with PowerArtist commands and settings (non-PACE mode)
  # ---------------------------------------------------------------------------------
  # Set up the clock gate information for power estimation. Default min_bit_width is 3.
  # Either 'clock_cell_attribute' or actual 'gating_cell' should be used (not both).
  # ####################
  # # Need to review
  # ####################
  SetClockGatingStyle -clock_cell_attribute latch_posedge_precontrol -min_bit_width 3 -min_bit_width_ecg 6
  #SetClockGatingStyle -gating_cells <lib name:cell name> -min_bit_width 3 -max_bit_width 20

  # Define the clock cells and clock tree architecture.
  # Specify clock buffers, optionally with their fanout for root, branch and leaf.
  # ####################
  # # Need to change
  # ####################
  SetClockBuffer -type root   -name <root_clk_buffer>   -library <library_name> [-fanout <max fanout>]
  SetClockBuffer -type branch -name <branch_clk_buffer> -library <library_name> [-fanout <max fanout>]
  SetClockBuffer -type leaf   -name <leaf_clk_buffer>   -library <library_name> [-fanout <max fanout>]

  # Define the high fanout net count and related buffer topology.
  # If not specified ==> clock buffers will be used (Warning ENG-203).
  # ####################
  # # Need to change
  # ####################
  SetMaxFanout -instance * -type logic -fanout 16
  SetBuffer -type root   -name <root_hfn_buffer>   -library <library_name> [-fanout <max fanout>]
  SetBuffer -type branch -name <branch_hfn_buffer> -library <library_name> [-fanout <max fanout>]
  SetBuffer -type leaf   -name <leaf_hfn_buffer>   -library <library_name> [-fanout <max fanout>]

  if { ![pa_set gate_level_netlist] } {
    # If the design is expected to get synthesized using multi-VT cells
    # AND PACE cell modeling is NOT used ==> use the following settings:
    # (SetVoltageThreshold: last command overwrites/receives priority.)
    # ####################
    # # Need to review
    # ####################
    #SetVoltageThreshold -group LVT -pattern {*LI31P *LI35P *UI35P}
    #SetVoltageThreshold -group SVT -pattern {*SI35P}
    #SetVoltageThreshold -group HVT -pattern {*HI35P}
    #SetVT -mode percentage -instance ${top_module} -vt_group [list HVT:30 SVT:30 LVT:40]
    #SetVT -mode percentage -type flop -instance ${top_module} -vt_group [list HVT:30 SVT:30 LVT:40]
  }

  # Optional: specify target stdcell libraries for design or specific instances.
  # ####################
  # # Need to review
  # ####################
  #SetLibrary -instance ${top_module} -library <target stdcell libraries>
  #SetLibrary -instance <instance>    -library <target stdcell libraries>

  # Recommended for non-PACE flow.
  pa_set domain_frequency_cell_selection true

} else {

  # PACE related settings
  # ---------------------
  # I) Common settings for PACE generation and PACE usage.
  pa_set power_tech_file $PACE_DIR/pace.tech
  # Isolate buffer chain capacitances and model post-layout buffers.
  pa_set pace_isolate_buffer_caps true

  # II) Settings for PACE generation only.
  # Distinguish between different cap range categories (ex. long vs. short nets).
  pa_set pace_cap_enhanced_variation_mode true
  # Ignore fanout of other combinational cells when calculating clock buffer fanout.
  pa_set pace_clock_ignore_non_buffer_fanouts true

  # make use of these cells:
  SetAttribute -cell {EDBSVT16_SYNC*RBMSFQ_1} -name dont_touch -value false
  SetAttribute -cell {EDB*T16_BUF_ECOCT_*  EDBSVT16_SYNC*RBMSFQ_1 EDBLVT16_INV_ECOCT_*} -name dont_use -value false

  # Leave config script for PACE generation.
  if { $flow_step == "WriteTechnologyFile" } { return }
  # Following settings are only used for RTL (or mixed RTL/gate-level) designs
  # using PACE model.

  # III) Settings for PACE usage only.
  pa_set use_pace_model_category "cap clock cell"
  # Linearize wire cap model if it has several non-continuous sections.
  pa_set pace_use_linear_cap_model true

  # Set up clock gating synthesis constraints. Default min_bit_width is 3, 2x for *_ecg.
  # PACE model doesn't contain information about "min_bit_width*" settings.
  # Workaround of current issue with AnalyzeStaticEfficiency and PACE:
  # AnalyzeStaticEfficiency doesn't extract clock gating information from PACE file.
  if { $flow_step == "AnalyzeStaticEfficiency" } {
    # ####################
    # # Need to review
    # ####################
    SetClockGatingStyle -clock_cell_attribute latch_posedge_precontrol -min_bit_width 3 -min_bit_width_ecg 6
  } else {
    # ####################
    # # Need to review
    # ####################
    SetClockGatingStyle -min_bit_width 3 -min_bit_width_ecg 6
  }

  # High Fanout net characterization for buffering.
  # ####################
  # # Need to review
  # ####################
  SetMaxFanout -instance * -type logic -fanout 25

  # High Fanout net buffering.
  # Recommended flow is to not use PACE-based HFN buffering (beta feature).
  if {0} {
    # Manually specify HFN buffer topology.
    # If not specified ==> clock buffers will be used (Warning ENG-203).
    # ####################
    # # Need to change
    # ####################
    SetBuffer -type root   -name <root_hfn_buffer>   -library <library_name> [-fanout <max_fanout>]
    SetBuffer -type branch -name <branch_hfn_buffer> -library <library_name> [-fanout <max_fanout>]
    SetBuffer -type leaf   -name <leaf_hfn_buffer>   -library <library_name> [-fanout <max_fanout>]
  } else {
    # Enable HFN buffering based on PACE characterization.
    pa_set pace_buffer_high_fanout_net_gate true
    pa_set pace_new_buffer_insertion true
  }

  # Allow to use inverters for clock tree/mesh buffering.
  pa_set pace_infer_inverter_clock_tree true
  # Optional: enable advanced clock tree engine.
  pa_set enable_advanced_cts true
  # Specifc "mesh" for clock mesh and "tree" for clock tree buffer inferring.
  pa_set clock_tree_topology tree

  # Use clock buffer mapping from PACE model.
  # Use clock slews which are derived from PACE model.
  # Use max cap values from PACE model.
  SetClockTreeOptions \
    -use_clock_buffer_mapping_from_pace true \
    -use_clock_slew_from_pace true \
    -use_max_cap_from_pace true
}
