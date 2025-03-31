# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------
# Filename    : common.tcl
# Description : Common procs and settings used by CDC constraint files
## TODO: AX/SNPS discuss the purpose of these constraints, what do they do, do we need them?
if {$::synopsys_program_name eq "dc_shell"} {
  redirect /dev/null {report_clocks [get_clocks]}
}
namespace eval BCM {
  variable ignore_clock_latency_option "-ignore_clock_latency"
  variable reset_path_option ""
  variable bcm_hier_to_skip ""
  variable bcm_mod_to_skip ""
  variable cmd_list_bcm_all {}
  variable bcm_constrain_input_ports 1
  variable name_attr "name"
  variable template_style 0
  variable cmnts_arr
  # We would like to use different comments for different constraints, but it
  # seems that tools (DC/FC) only apply the last comments on the same path. So,
  # use same comments for both max delay and min delay for now.
  #array set cmnts_arr {
  #  CDC_SYN_02_max {Define set_max_delay of 1 source clock period for Gray-coded signals}
  #  CDC_SYN_02_min {Define set_min_delay of 0 for Gray-coded signals}
  #  CDC_SYN_03_max {Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period for Qualifier-based Data Bus signals}
  #  CDC_SYN_03_min {Define set_min_delay of 0 for Qualifier-based Data Bus signals}
  #  CDC_SYN_04_max {Define set_max_delay of 1 destination clock period for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)}
  #  CDC_SYN_04_min {Define set_min_delay of 0 for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)}
  #  CDC_SYN_05     {Define set_false_path -through for quasi-static signals at the output of the Bus Delay components}
  #  MCP_SYN        {Define set_multicycle_path for multi-cycle delay cells}
  #}
  array set cmnts_arr {
    CDC_SYN_02_max {Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals}
    CDC_SYN_02_min {Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals}
    CDC_SYN_03_max {Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period and set_min_delay of 0 constraints for Qualifier-based Data Bus signals}
    CDC_SYN_03_min {Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period and set_min_delay of 0 constraints for Qualifier-based Data Bus signals}
    CDC_SYN_04_max {Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)}
    CDC_SYN_04_min {Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)}
    CDC_SYN_05     {Define set_false_path -through for quasi-static signals at the output of the Bus Delay components}
    MCP_SYN        {Define set_multicycle_path for multi-cycle delay cells}
  }

  if {($::synopsys_program_name eq "fc_shell") || ($::synopsys_program_name eq "pt_shell")} {
    alias bcm_all_fanin {all_fanin -quiet}
    alias bcm_all_fanout {all_fanout -quiet}
  } else {
    alias bcm_all_fanin {all_fanin}
    alias bcm_all_fanout {all_fanout}
  }
  proc bcm_puts {severity str} {
    set msg_tag "(BcmCdcConstraint)"
    if {$severity eq "DBG"} {
      if {![catch {getenv DWC_BCM_TCL_SNPS_DEBUG}]} {
        puts "$severity: $str $msg_tag"
      }
    } elseif {$severity eq "WARNFST0"} {
      if {![catch {getenv DWC_BCM_WRN_SYNC_NOREG}]} {
        puts "WARN: $str $msg_tag"
      }
    } else {
      puts "$severity: $str $msg_tag"
    }
  }
  proc getBCMClocks { cell_name pin_name } {
    if {[get_pins -quiet $cell_name/$pin_name] eq ""} {
      return ""
    }
    # find all the clocks associated to the pin
    set clks [get_clocks -quiet [get_attribute -quiet [get_pins -quiet $cell_name/$pin_name] clocks]]
    if { [sizeof_collection $clks] == 0 } {
      # second try for compiled netlist where clock attribute only exists in leaf pins
      set pins [bcm_all_fanout -from $cell_name/$pin_name -endpoints_only -flat]
      append_to_collection -unique clks [get_attribute -quiet $pins clocks]
    }
    if { [sizeof_collection $clks] == 0 } {
      # third try if something before this cell stops the clock propagation
      set pins [bcm_all_fanin -to $cell_name/$pin_name -startpoints_only -flat]
      append_to_collection -unique clks [get_attribute -quiet $pins clocks]
    }
    if { [sizeof_collection $clks] == 0 } {
      bcm_puts "WARN" "Cannot get associated clocks on pin $pin_name of $cell_name. Cell will be skipped."
    }
    return $clks
  }
  proc getBCMClockPeriod { cell_name pin_name clks } {
    set allPeriods [get_attribute -quiet $clks period]
    if {$allPeriods ne ""} {
      set clkPeriod [tcl::mathfunc::min {*}$allPeriods]
      bcm_puts "DBG" "getBCMClockPeriod: cell name $cell_name - pin name $pin_name - clocks [get_object_name $clks] - period $clkPeriod"
    } else {
      set clkPeriod ""
      bcm_puts "WARN" "Period is not defined for clock [get_object_name $clks], which is associated to pin $pin_name of $cell_name. Cell will be skipped."
    }
    return $clkPeriod
  }
  proc checkTemplateNamingStyle {} {
    set value 0
    set template_naming_style ""
    set template_parameter_style ""
    set template_separator_style ""
    if {$::synopsys_program_name eq "fc_shell"} {
      set template_naming_style [get_app_option_value -name hdlin.naming.template_naming_style]
      set template_parameter_style [get_app_option_value -name hdlin.naming.template_parameter_style]
      set template_separator_style [get_app_option_value -name hdlin.naming.template_separator_style]
    } elseif {($::synopsys_program_name eq "dc_shell") || ($::synopsys_program_name eq "dcnxt_shell")} {
      set template_naming_style [get_app_var template_naming_style]
      set template_parameter_style [get_app_var template_parameter_style]
      set template_separator_style [get_app_var template_separator_style]
    } else {
      set value 2
    }
    if {
      ($template_naming_style eq {%s_%p}) &&
      (($template_parameter_style eq {%s%d}) || ($template_parameter_style eq {%d})) &&
      ($template_separator_style eq {_})
    } {
      set value 1
    }
    if {$value == 0} {
      puts "INFO: Cannot get the value of BCM parameters, because tool options template_*_style probably have non-default settings."
      puts "      Supported template_naming_style is %s_%p, supported template_parameter_style is %s%d or %d, supported template_separator_style is _"
      puts "      Normally this won't impact constraint setting, but you may see warnings like 'Unable to find synchronization flip-flop ...'."
      puts "      These warnings can be ignored if parameter F_SYNC_TYPE of some BCM modules is intentionally set to 0."
      puts "      Set 'template_*_style' to supported styles if you want to avoid such warnings."
    }
    return $value
  }
  set template_style [checkTemplateNamingStyle]
  proc getBCMParamFromNameOrIndex { cell bcmSuffix bcmParamName bcmParamIndex } {
    variable template_style
    set cell_name [get_object_name $cell]
    set value ""
    if {$template_style == 1} {
      set ref_name [get_attribute $cell ref_name]
      if {![regsub ".*_${bcmSuffix}_" $ref_name {} paramString]} {
        # No instance name match.
        return $value
      }
      # First look by name PARAMA<valueA>_PARAMB<valueB>_...
      if {![regexp "${bcmParamName}(\[^_\]+)" $paramString match value]} {
        # Look by index <valueA>_<valueB>_...
        set parameters [split $paramString _]
        if {[llength $parameters] >= $bcmParamIndex} {
          set value [lindex $parameters $bcmParamIndex]
        }
      }
    }
    if {$value eq ""} {
      bcm_puts "DBG" "Cannot get the value of parameter $bcmParamName in $cell_name."
    }
    return $value
  }
  # Get name of reference design 'level' levels above the given cell name
  proc getBCMParent {cell_name level} {
    set names [split $cell_name /]
    set name [join [lrange $names 0 end-$level] /]
    if {$name ne ""} {
      return [get_attribute -quiet [get_cells -quiet $name] ref_name]
    }
    return ""
  }
  proc runCmd { cmd } {
    bcm_puts "DBG" $cmd
    eval $cmd
  }
  if {![catch {getenv DWC_BCM_DISABLE_IGNORE_CLOCK_LATENCY}]} {
    set ignore_clock_latency_option ""
    bcm_puts "DBG" "DWC_BCM_DISABLE_IGNORE_CLOCK_LATENCY is defined, -ignore_clock_latency won't be used."
  }
  if {![catch {getenv DWC_BCM_RESET_PATH}]} {
    set reset_path_option "-reset_path"
    bcm_puts "DBG" "DWC_BCM_RESET_PATH is defined, -reset_path will be used."
  }
  if {![catch {getenv DWC_BCM_HIER_TO_SKIP}]} {
    set bcm_hier_to_skip [getenv DWC_BCM_HIER_TO_SKIP]
    if {[llength $bcm_hier_to_skip] > 0} {
      bcm_puts "DBG" "DWC_BCM_HIER_TO_SKIP is defined, skip constraints on BCM instances under $bcm_hier_to_skip."
    }
  }
  if {![catch {getenv DWC_BCM_MOD_TO_SKIP}]} {
    set bcm_mod_to_skip [getenv DWC_BCM_MOD_TO_SKIP]
    if {[llength $bcm_mod_to_skip] > 0} {
      bcm_puts "DBG" "DWC_BCM_MOD_TO_SKIP is defined, skip constraints on BCM modules $bcm_mod_to_skip."
    }
  }
  if {![catch {getenv DWC_BCM_CONSTRAIN_INPUT_PORTS}]} {
    if {$::env(DWC_BCM_CONSTRAIN_INPUT_PORTS) == 0} {
      set bcm_constrain_input_ports 0
      bcm_puts "DBG" "DWC_BCM_CONSTRAIN_INPUT_PORTS is defined as 0, skip constraints on the paths starting from primary inputs."
    }
  }
  if {$::synopsys_program_name eq "pt_shell"} {
    set name_attr base_name
  }
}; # end of namespace BCM (common procs and vars)
#===============================================================================
# Create Guard for file DWbb_bcm07_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm07_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm07_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_02] Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals
# BCM07 set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm07 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm07 [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm07.*) AND @ref_name!~.*_bcm07_atv.* AND @ref_name!~.*_bcm07_ef.* AND @ref_name!~.*_bcm07_rs.* AND @ref_name!~.*_bcm07_vmd.*}]
    foreach_in_collection cell $cell_collection_bcm07 {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
    
      if { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/this_addr_g_int*] != "" } {
    
        # A "set_max_delay" constraint equivalent to 1 period (or less) of the source clock domain shall be applied in all Gray-coded signals reaching the first synchronization flip-flops in the destination clock domain
        # A "set_min_delay" constraint with value 0 shall be applied to the same paths
        # Source clock_push: Gray Address to be sync into clock_pop domain
        set clk_from [getBCMClocks $cell_name "clk_push"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPushPeriod [getBCMClockPeriod $cell_name "clk_push" $clk_from]
        if {$clkPushPeriod eq ""} {
          continue
        }
        set data_d_pins ""
        if { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*] != "" } {
          # No tech cell mapping
          set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
          # Old way with DWC_SYNCHRONIZER_TECH_MAP
          set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*] != "" } {
          # New way with cT tech cell mapping
          set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/D]
        }
        if { [sizeof_collection $data_d_pins] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          set data_d_pins_name [get_object_name $data_d_pins]
          lappend cmd_list_bcm_all "set_max_delay $clkPushPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining from PUSH to POP in $cell_name because F_SYNC_TYPE of $cell_name/U_POP_FIFOFCTL/U_sync is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop from PUSH domain to POP domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
    
        # Source clock_pop: Gray Address to be sync into clock_push domain
        set clk_from [getBCMClocks $cell_name "clk_pop"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPopPeriod [getBCMClockPeriod $cell_name "clk_pop" $clk_from]
        if {$clkPopPeriod eq ""} {
          continue
        }
        set data_d_pins ""
        if { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*] != "" } {
          # No tech cell mapping
          set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
          # Old way with DWC_SYNCHRONIZER_TECH_MAP
          set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*] != "" } {
          # New way with cT tech cell mapping
          set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/D]
        }
        if { [sizeof_collection $data_d_pins] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          set data_d_pins_name [get_object_name $data_d_pins]
          lappend cmd_list_bcm_all "set_max_delay $clkPopPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining from POP to PUSH in $cell_name because F_SYNC_TYPE of $cell_name/U_PUSH_FIFOFCTL/U_sync is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop from POP domain to PUSH domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
      } else {
        bcm_puts "WARN" "Unable to find address register in $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm07
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm07$"] < 0 } {
    set_cstr_bcm07
  }
}; # end of namespace BCM (bcm07)
}
#===============================================================================
# Create Guard for file DWbb_bcm07_atv_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm07_atv_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm07_atv_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_02] Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals
# BCM07_ATV set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm07_atv {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm07_atv [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm07_atv.*}]
    foreach_in_collection cell $cell_collection_bcm07_atv {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
    
      if { [get_nets -quiet $cell_name/U_PUSH_FIFOFCTL/this_addr_g*] != "" } {
    
        # A "set_max_delay" constraint equivalent to 1 period (or less) of the source clock domain shall be applied in all Gray-coded signals reaching the first synchronization flip-flops in the destination clock domain
        # A "set_min_delay" constraint with value 0 shall be applied to the same paths
        # Source clock_push: Gray Address to be sync into clock_pop domain
        set clk_from [getBCMClocks $cell_name "clk_push"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPushPeriod [getBCMClockPeriod $cell_name "clk_push" $clk_from]
        if {$clkPushPeriod eq ""} {
          continue
        }
        set data_d_pins ""
        if { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*] != "" } {
          # No tech cell mapping
          set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
          # Old way with DWC_SYNCHRONIZER_TECH_MAP
          set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*] != "" } {
          # New way with cT tech cell mapping
          set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/D]
        }
        if { [sizeof_collection $data_d_pins] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          set data_d_pins_name [get_object_name $data_d_pins]
          lappend cmd_list_bcm_all "set_max_delay $clkPushPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21_atv F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining from PUSH to POP in $cell_name because F_SYNC_TYPE of $cell_name/U_POP_FIFOFCTL/U_sync is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop from PUSH domain to POP domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
    
        # Source clock_pop: Gray Address to be sync into clock_push domain
        set clk_from [getBCMClocks $cell_name "clk_pop"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPopPeriod [getBCMClockPeriod $cell_name "clk_pop" $clk_from]
        if {$clkPopPeriod eq ""} {
          continue
        }
        set data_d_pins ""
        if { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*] != "" } {
          # No tech cell mapping
          set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
          # Old way with DWC_SYNCHRONIZER_TECH_MAP
          set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*] != "" } {
          # New way with cT tech cell mapping
          set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/D]
        }
        if { [sizeof_collection $data_d_pins] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          set data_d_pins_name [get_object_name $data_d_pins]
          lappend cmd_list_bcm_all "set_max_delay $clkPopPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21_atv F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining from POP to PUSH in $cell_name because F_SYNC_TYPE of $cell_name/U_PUSH_FIFOFCTL/U_sync is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop from POP domain to PUSH domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
    
      } else {
        bcm_puts "WARN" "Unable to find address register in $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm07_atv
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm07_atv$"] < 0 } {
    set_cstr_bcm07_atv
  }
}; # end of namespace BCM (bcm07_atv)
}
#===============================================================================
# Create Guard for file DWbb_bcm07_ef_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm07_ef_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm07_ef_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_02] Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals
# BCM07_ef set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm07_ef {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm07_ef [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm07_ef.* AND @ref_name!~.*_bcm07_efes.* AND @ref_name!~.*_bcm07_ef_atv.*}]
    foreach_in_collection cell $cell_collection_bcm07_ef {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
    
      if { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/this_addr_g_int*] != "" } {
    
        # A "set_max_delay" constraint equivalent to 1 period (or less) of the source clock domain shall be applied in all Gray-coded signals reaching the first synchronization flip-flops in the destination clock domain
        # A "set_min_delay" constraint with value 0 shall be applied to the same paths
        # Source clock_push: Gray Address to be sync into clock_pop domain
        set clk_from [getBCMClocks $cell_name "clk_push"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPushPeriod [getBCMClockPeriod $cell_name "clk_push" $clk_from]
        if {$clkPushPeriod eq ""} {
          continue
        }
        set data_d_pins ""
        if { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*] != "" } {
          # No tech cell mapping
          set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
          # Old way with DWC_SYNCHRONIZER_TECH_MAP
          set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*] != "" } {
          # New way with cT tech cell mapping
          set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/D]
        }
        if { [sizeof_collection $data_d_pins] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          set data_d_pins_name [get_object_name $data_d_pins]
          lappend cmd_list_bcm_all "set_max_delay $clkPushPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining from PUSH to POP in $cell_name because F_SYNC_TYPE of $cell_name/U_POP_FIFOFCTL/U_sync is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop from PUSH domain to POP domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
    
        # Source clock_pop: Gray Address to be sync into clock_push domain
        set clk_from [getBCMClocks $cell_name "clk_pop"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPopPeriod [getBCMClockPeriod $cell_name "clk_pop" $clk_from]
        if {$clkPopPeriod eq ""} {
          continue
        }
        set data_d_pins ""
        if { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*] != "" } {
          # No tech cell mapping
          set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
          # Old way with DWC_SYNCHRONIZER_TECH_MAP
          set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*] != "" } {
          # New way with cT tech cell mapping
          set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/D]
        }
        if { [sizeof_collection $data_d_pins] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          set data_d_pins_name [get_object_name $data_d_pins]
          lappend cmd_list_bcm_all "set_max_delay $clkPopPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining from POP to PUSH in $cell_name because F_SYNC_TYPE of $cell_name/U_PUSH_FIFOFCTL/U_sync is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop from POP domain to PUSH domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
      } else {
        bcm_puts "WARN" "Unable to find address register in $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm07_ef
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm07_ef$"] < 0 } {
    set_cstr_bcm07_ef
  }
}; # end of namespace BCM (bcm07_ef)
}
#===============================================================================
# Create Guard for file DWbb_bcm07_ef_atv_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm07_ef_atv_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm07_ef_atv_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_02] Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals
# BCM07_ATV set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm07_ef_atv {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm07_ef_atv [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm07_ef_atv.*}]
    foreach_in_collection cell $cell_collection_bcm07_ef_atv {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
    
      if { [get_nets -quiet $cell_name/U_PUSH_FIFOFCTL/this_addr_g*] != "" } {
    
        # A "set_max_delay" constraint equivalent to 1 period (or less) of the source clock domain shall be applied in all Gray-coded signals reaching the first synchronization flip-flops in the destination clock domain
        # A "set_min_delay" constraint with value 0 shall be applied to the same paths
        # Source clock_push: Gray Address to be sync into clock_pop domain
        set clk_from [getBCMClocks $cell_name "clk_push"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPushPeriod [getBCMClockPeriod $cell_name "clk_push" $clk_from]
        if {$clkPushPeriod eq ""} {
          continue
        }
        set data_d_pins ""
        if { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*] != "" } {
          # No tech cell mapping
          set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
          # Old way with DWC_SYNCHRONIZER_TECH_MAP
          set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*] != "" } {
          # New way with cT tech cell mapping
          set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/D]
        }
        if { [sizeof_collection $data_d_pins] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          set data_d_pins_name [get_object_name $data_d_pins]
          lappend cmd_list_bcm_all "set_max_delay $clkPushPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21_atv F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining from PUSH to POP in $cell_name because F_SYNC_TYPE of $cell_name/U_POP_FIFOFCTL/U_sync is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop from PUSH domain to POP domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
    
        # Source clock_pop: Gray Address to be sync into clock_push domain
        set clk_from [getBCMClocks $cell_name "clk_pop"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPopPeriod [getBCMClockPeriod $cell_name "clk_pop" $clk_from]
        if {$clkPopPeriod eq ""} {
          continue
        }
        set data_d_pins ""
        if { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*] != "" } {
          # No tech cell mapping
          set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
          # Old way with DWC_SYNCHRONIZER_TECH_MAP
          set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
          if { [sizeof_collection $data_d_pins] == 0 } {
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
          }
        } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*] != "" } {
          # New way with cT tech cell mapping
          set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_TMR_*/GEN_FST??U_SAMPLE_META_*/D]
        }
        if { [sizeof_collection $data_d_pins] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          set data_d_pins_name [get_object_name $data_d_pins]
          lappend cmd_list_bcm_all "set_max_delay $clkPopPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21_atv F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining from POP to PUSH in $cell_name because F_SYNC_TYPE of $cell_name/U_PUSH_FIFOFCTL/U_sync is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop from POP domain to PUSH domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
    
      } else {
        bcm_puts "WARN" "Unable to find address register in $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm07_ef_atv
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm07_ef_atv$"] < 0 } {
    set_cstr_bcm07_ef_atv
  }
}; # end of namespace BCM (bcm07_ef_atv)
}
#===============================================================================
# Create Guard for file DWbb_bcm21_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm21_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm21_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_04] Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)
# BCM21 set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm21 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable bcm_constrain_input_ports
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm21 [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm21.*) AND @ref_name!~.*_bcm21_a.* AND @ref_name!~.*_bcm21_cg.* AND @ref_name!~.*_bcm21_neo.* AND @ref_name!~.*_bcm21_tgl.*}]
    # Parent modules of bcm21 which have their own constraints
    set bcm21_excl_parents_expr_lvl1 "_bcm05_cf|_bcm24|_bcm40|_bcm38"
    set bcm21_excl_parents_expr_lvl2 "_bcm07(?!_rs)|_bcm87"
    set bcm21_excl_parents_expr_lvl3 "_bcm07_atv"
    foreach_in_collection cell $cell_collection_bcm21 {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
      if { \
        [regexp $bcm21_excl_parents_expr_lvl1 [getBCMParent $cell_name 1]] || \
        [regexp $bcm21_excl_parents_expr_lvl2 [getBCMParent $cell_name 2]] || \
        [regexp $bcm21_excl_parents_expr_lvl3 [getBCMParent $cell_name 3]] \
      } {
        continue
      }
      set clk_dst [getBCMClocks $cell_name "clk_d"]
      if { [sizeof_collection $clk_dst] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clkPeriod [getBCMClockPeriod $cell_name "clk_d" $clk_dst]
      if {$clkPeriod eq ""} {
        continue
      }
      set dst_pins ""
      if { [get_cells -quiet $cell_name/GEN_FST??sample_meta*] != "" } {
        # No tech cell mapping
        set dst_pins [get_pins -quiet $cell_name/GEN_FST??sample_meta*/next_state]
        if { [sizeof_collection $dst_pins] == 0 } {
          set dst_pins [get_pins $cell_name/GEN_FST??sample_meta*/D]
        }
      } elseif { [get_cells -quiet $cell_name/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
        # Old way with DWC_SYNCHRONIZER_TECH_MAP
        set dst_pins [get_pins -quiet $cell_name/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
        if { [sizeof_collection $dst_pins] == 0 } {
          set dst_pins [get_pins $cell_name/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
        }
      } elseif { [get_cells -quiet $cell_name/GEN_FST??U_SAMPLE_META_*] != "" } {
        # New way with cT tech cell mapping
        set dst_pins [get_pins $cell_name/GEN_FST??U_SAMPLE_META_*/D]
      }
      if { [sizeof_collection $dst_pins] > 0 } {
        set dst_pins_name [get_object_name $dst_pins]
        set clk_from ""
        set data_s_regs [bcm_all_fanin -to $cell_name/data_s -startpoints_only -only_cells -flat]
        foreach_in_collection sreg $data_s_regs {
          append_to_collection -unique clk_from [get_pins -quiet [get_object_name $sreg]/* -filter "is_clock_pin == true"]
        }
        if { [sizeof_collection $clk_from] > 0 } {
          set clk_from_name [get_object_name $clk_from]
          lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
          lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
        }
        if {$bcm_constrain_input_ports == 1} {
          set i_ports [filter_collection [bcm_all_fanin -to $cell_name/data_s -startpoints_only -flat] "object_class == port"]
          if {[sizeof_collection $i_ports] > 0} {
            set i_ports_name [get_object_name $i_ports]
            lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_ports {$i_ports_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_ports {$i_ports_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
          }
        }
      } else {
        set f_sync_type [getBCMParamFromNameOrIndex $cell bcm21 F_SYNC_TYPE 1]
        if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
          # Nothing to be done when F_SYNC_TYPE is 0
          bcm_puts "WARNFST0" "Skip constraining $cell_name because F_SYNC_TYPE is set to 0."
        } else {
          bcm_puts "WARN" "Unable to find first synchronization flip-flop to destination domain in cell $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
        }
      }
    }
  }; # end of proc set_cstr_bcm21
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm21$"] < 0 } {
    set_cstr_bcm21
  }
}; # end of namespace BCM (bcm21)
}
#===============================================================================
# Create Guard for file DWbb_bcm25_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm25_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm25_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_03] Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period and set_min_delay of 0 constraints for Qualifier-based Data Bus signals
# BCM25 set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm25 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm25 [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm25.*) AND @ref_name!~.*_bcm25_atv.* AND @ref_name!~.*_bcm25_c.*}]
    foreach_in_collection cell $cell_collection_bcm25 {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_03_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_03_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
    
      set clk_from [getBCMClocks $cell_name "clk_s"]
      if { [sizeof_collection $clk_from] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clk_dst [getBCMClocks $cell_name "clk_d"]
      if { [sizeof_collection $clk_dst] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clkPeriod [getBCMClockPeriod $cell_name "clk_d" $clk_dst]
      if {$clkPeriod eq ""} {
        continue
      }
    
      if { [get_cells -quiet $cell_name/data_d_reg*] != "" } {
        if { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST* ] != "" } {
          set clkPeriodFactor ""
          if { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST1* ] != "" } {
            set clkPeriodFactor 1
          } elseif { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST2* ] != "" } {
            set clkPeriodFactor 1.5
          } elseif { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST3* ] != "" } {
            set clkPeriodFactor 2.5
          } elseif { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST4* ] != "" } {
            set clkPeriodFactor 3.5
          } else {
            bcm_puts "WARN" "Unable to find first synchronization flip-flop to destination domain in cell $cell_name"
          }
    
          foreach_in_collection data_d_reg [get_cells $cell_name/data_d_reg*] {
            set data_d_reg_name [get_object_name $data_d_reg]
            set data_d_pin [get_pins -quiet $data_d_reg_name/next_state]
            if { [sizeof_collection $data_d_pin] == 0 } {
              set data_d_pin [get_pins $data_d_reg_name/D]
            }
            set data_d_pin_name [get_object_name $data_d_pin]
            set clk_from_name [get_object_name $clk_from]
            if { $clkPeriodFactor != "" } {
              set maxdelay [expr $clkPeriodFactor*$clkPeriod]
              lappend cmd_list_bcm_all "set_max_delay $maxdelay -from \[get_clocks {$clk_from_name}\] -to {$data_d_pin_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
              lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pin_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
            }
          }
        } else {
          set f_sync_type ""
          set sync_cell [get_cells -quiet $cell_name/U1/U_DW_SYNC_F]
          if { [sizeof_collection $sync_cell] > 0 } {
            set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
          }
          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
            # Nothing to be done when F_SYNC_TYPE is 0
            bcm_puts "WARNFST0" "Skip constraining $cell_name because F_SYNC_TYPE of $cell_name/U1/U_DW_SYNC_F is set to 0."
          } else {
            bcm_puts "WARN" "Unable to find synchronization flip-flops to destination domain in cell $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
          }
        }
      }
    }
  }; # end of proc set_cstr_bcm25
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm25$"] < 0 } {
    set_cstr_bcm25
  }
}; # end of namespace BCM (bcm25)
}
#===============================================================================
# Create Guard for file DWbb_bcm36_nhs_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm36_nhs_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm36_nhs_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_05] Define "set_false_path -through" constraint for quasi-static signals at the output of the Bus Delay components
# BCM36_NHS set_false_path constraints
namespace eval BCM {
  proc set_cstr_bcm36_nhs {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm36_nhs [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm36_nhs.*}]
    # Parent modules of bcm36_nhs which have their own constraints
    set bcm36_nhs_excl_parents_expr_lvl1 "(_bcm36_(ack|tgl)|_bcm31_p2d_fifomem)"
    foreach_in_collection cell $cell_collection_bcm36_nhs {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_05)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
      if { [regexp $bcm36_nhs_excl_parents_expr_lvl1 [getBCMParent $cell_name 1]] } {
        continue
      }
      lappend cmd_list_bcm_all "set_false_path -through \[get_pins $cell_name/data_d*\] $cmd_cmnt"
    }
  }; # end of proc set_cstr_bcm36_nhs
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm36_nhs$"] < 0 } {
    set_cstr_bcm36_nhs
  }
}; # end of namespace BCM (bcm36_nhs)
}
#===============================================================================
# Create Guard for file DWbb_bcm40_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm40_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm40_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_04] Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)
# bcm40 set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm40 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable bcm_constrain_input_ports
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm40 [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm40.*}]
    foreach_in_collection cell $cell_collection_bcm40 {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
      set clk_dst [getBCMClocks $cell_name "clk_d"]
      if { [sizeof_collection $clk_dst] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clkPeriod [getBCMClockPeriod $cell_name "clk_d" $clk_dst]
      if {$clkPeriod eq ""} {
        continue
      }
      if { [get_pins -quiet $cell_name/rst_s_n] != "" } {
        if { [get_cells -quiet $cell_name/U_SYNC/GEN_FST* ] != "" } {
          set dst_pins [filter_collection [bcm_all_fanout -from $cell_name/rst_s_n -endpoints_only -flat] -regexp {full_name !~ .*\*cell\*\d+.*}]
          if { [sizeof_collection $dst_pins] > 0 } {
            set dst_pins_name [get_object_name $dst_pins]
            set clk_from ""
            set rst_s_regs [bcm_all_fanin -to $cell_name/rst_s_n -startpoints_only -only_cells -flat]
            foreach_in_collection sreg $rst_s_regs {
              append_to_collection -unique clk_from [get_pins -quiet [get_object_name $sreg]/* -filter "is_clock_pin == true"]
            }
            if { [sizeof_collection $clk_from] > 0 } {
              set clk_from_name [get_object_name $clk_from]
              lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
              lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
            }
            if {$bcm_constrain_input_ports == 1} {
              set i_ports [filter_collection [bcm_all_fanin -to $cell_name/rst_s_n -startpoints_only -flat] "object_class == port"]
              if {[sizeof_collection $i_ports] > 0} {
                set i_ports_name [get_object_name $i_ports]
                lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_ports {$i_ports_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_ports {$i_ports_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
              }
            }
          }
        }
      } else {
        bcm_puts "WARN" "Unable to find rst_s_n pin in cell $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm40
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm40$"] < 0 } {
    set_cstr_bcm40
  }
}; # end of namespace BCM (bcm40)
}
#===============================================================================
# Create Guard for file DWbb_bcm58_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm58_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm58_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_04] Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)
# BCM58 set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm58 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm58 [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm58.* AND @ref_name!~.*_bcm58_atv.*}]
    # Parent modules of bcm58 which have their own constraints
    set bcm58_excl_parents_expr_lvl1 "_bcm66(?!_(dms|efes))"
    foreach_in_collection cell $cell_collection_bcm58 {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
      if { [regexp $bcm58_excl_parents_expr_lvl1 [getBCMParent $cell_name 1]] } {
        continue
      }
      set clk_rd [getBCMClocks $cell_name "clk_r"]
      if { [sizeof_collection $clk_rd] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clkPeriod [getBCMClockPeriod $cell_name "clk_r" $clk_rd]
      if {$clkPeriod eq ""} {
        continue
      }
      set mem_regs [get_cells -quiet $cell_name/mem_array_reg*]
      if { [sizeof_collection $mem_regs] > 0 } {
        set from_pins [get_pins -quiet -of_objects $mem_regs -filter "is_clock_pin==true"]
        if { [sizeof_collection $from_pins] > 0 } {
          set from_pin_names [get_object_name $from_pins]
          set o_ports [filter_collection [bcm_all_fanout -from $cell_name/mem_array_reg*/Q -endpoints_only -flat] "object_class == port"]
          if {[sizeof_collection $o_ports] > 0} {
            set o_ports_name [get_object_name $o_ports]
            lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$from_pin_names}\] -to \[get_ports {$o_ports_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_ports {$o_ports_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
          }
          set o_regs [bcm_all_fanout -from $cell_name/mem_array_reg*/Q -endpoints_only -flat -only_cells]
          if {[sizeof_collection $o_regs] > 0} {
            set o_reg_clks [get_pins -quiet -of_objects $o_regs -filter "is_clock_pin==true"]
            if {[sizeof_collection $o_reg_clks] > 0} {
              set o_clks ""
              append_to_collection -unique o_clks [get_clocks -quiet [get_attribute -quiet $o_reg_clks clocks]]
              if {[sizeof_collection $o_clks] > 0} {
                set o_clk_name [get_object_name $o_clks]
                lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$from_pin_names}\] -to \[get_clocks {$o_clk_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_clocks {$o_clk_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
              } else {
                set o_pins [filter_collection [bcm_all_fanout -from $cell_name/mem_array_reg*/Q -endpoints_only -flat] -regexp {full_name !~ .*\*cell\*\d+.* AND object_class == pin}]
                if {[sizeof_collection $o_pins] > 0} {
                  set o_pins_name [get_object_name $o_pins]
                  lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$from_pin_names}\] -to \[get_pins {$o_pins_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                  lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_pins {$o_pins_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
                }
              }
            }
          }
        }
      } else {
        bcm_puts "ERROR" "Unable to find the memory array inside the memory cell $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm58
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm58$"] < 0 } {
    set_cstr_bcm58
  }
}; # end of namespace BCM (bcm58)
}
#===============================================================================
# Create Guard for file DWbb_bcm58_atv_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm58_atv_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm58_atv_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_04] Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)
# bcm58_atv set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm58_atv {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm58_atv [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm58_atv.*}]
    # Parent modules of bcm58_atv which have their own constraints
    set bcm58_atv_excl_parents_expr_lvl1 "_bcm66_atv|_bcm66_wae_atv"
    foreach_in_collection cell $cell_collection_bcm58_atv {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
      if { [regexp $bcm58_atv_excl_parents_expr_lvl1 [getBCMParent $cell_name 1]] } {
        continue
      }
      set clk_rd [getBCMClocks $cell_name "clk_r"]
      if { [sizeof_collection $clk_rd] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clkPeriod [getBCMClockPeriod $cell_name "clk_r" $clk_rd]
      if {$clkPeriod eq ""} {
        continue
      }
      set mem_regs [get_cells -quiet $cell_name/mem_array_reg*]
      if { [sizeof_collection $mem_regs] > 0 } {
        set from_pins [get_pins -quiet -of_objects $mem_regs -filter "is_clock_pin==true"]
        if { [sizeof_collection $from_pins] > 0 } {
          set from_pin_names [get_object_name $from_pins]
          set o_ports [filter_collection [bcm_all_fanout -from $cell_name/mem_array_reg*/Q -endpoints_only -flat] "object_class == port"]
          if {[sizeof_collection $o_ports] > 0} {
            set o_ports_name [get_object_name $o_ports]
            lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$from_pin_names}\] -to \[get_ports {$o_ports_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_ports {$o_ports_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
          }
          set o_regs [bcm_all_fanout -from $cell_name/mem_array_reg*/Q -endpoints_only -flat -only_cells]
          if {[sizeof_collection $o_regs] > 0} {
            set o_reg_clks [get_pins -quiet -of_objects $o_regs -filter "is_clock_pin==true"]
            if {[sizeof_collection $o_reg_clks] > 0} {
              set o_clks ""
              append_to_collection -unique o_clks [get_clocks -quiet [get_attribute -quiet $o_reg_clks clocks]]
              if {[sizeof_collection $o_clks] > 0} {
                set o_clk_name [get_object_name $o_clks]
                lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$from_pin_names}\] -to \[get_clocks {$o_clk_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_clocks {$o_clk_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
              } else {
                set o_pins [filter_collection [bcm_all_fanout -from $cell_name/mem_array_reg*/Q -endpoints_only -flat] -regexp {full_name !~ .*\*cell\*\d+.* AND object_class == pin}]
                if {[sizeof_collection $o_pins] > 0} {
                  set o_pins_name [get_object_name $o_pins]
                  lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$from_pin_names}\] -to \[get_pins {$o_pins_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                  lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_pins {$o_pins_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
                }
              }
            }
          }
        }
      } else {
        bcm_puts "ERROR" "Unable to find the memory array inside the memory cell $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm58_atv
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm58_atv$"] < 0 } {
    set_cstr_bcm58_atv
  }
}; # end of namespace BCM (bcm58_atv)
}
#===============================================================================
# Create Guard for file DWbb_bcm66_wae_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm66_wae_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm66_wae_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_03] Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period and set_min_delay of 0 constraints for Qualifier-based Data Bus signals
# bcm66_wae set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm66_wae {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm66_wae [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm66_wae.*) AND @ref_name!~.*_bcm66_wae_atv.*}]
    foreach_in_collection cell $cell_collection_bcm66_wae {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_03_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_03_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
    
      set clk_from [getBCMClocks $cell_name "clk_push"]
      if { [sizeof_collection $clk_from] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clk_dst [getBCMClocks $cell_name "clk_pop"]
      if { [sizeof_collection $clk_dst] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clkPeriod [getBCMClockPeriod $cell_name "clk_pop" $clk_dst]
      if {$clkPeriod eq ""} {
        continue
      }
    
      set mem_reg_name "$cell_name/U_FIFO_MEM/mem_array_reg*"
      set sync_cell_name "$cell_name/*U_FIFO_CTL/U_POP_FIFOFCTL/U_sync"
      set mem_regs [get_cells -quiet $mem_reg_name]
      if { [sizeof_collection $mem_regs] > 0 } {
        set clkPeriodFactor 1
        if { [get_cells -quiet $sync_cell_name/GEN_FST2* ] != "" } {
          set clkPeriodFactor 1.5
        } elseif { [get_cells -quiet $sync_cell_name/GEN_FST3* ] != "" } {
          set clkPeriodFactor 2.5
        } elseif { [get_cells -quiet $sync_cell_name/GEN_FST4* ] != "" } {
          set clkPeriodFactor 3.5
        }
        set maxdelay [expr $clkPeriodFactor*$clkPeriod]
        set from_pins [get_pins -quiet -of_objects $mem_regs -filter "is_clock_pin==true"]
        if { [sizeof_collection $from_pins] > 0 } {
          set from_pin_names [get_object_name $from_pins]
          set o_ports [filter_collection [bcm_all_fanout -from $mem_reg_name/Q -endpoints_only -flat] "object_class == port"]
          if {[sizeof_collection $o_ports] > 0} {
            set o_ports_name [get_object_name $o_ports]
            lappend cmd_list_bcm_all "set_max_delay $maxdelay -from \[get_pins {$from_pin_names}\] -to \[get_ports {$o_ports_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_ports {$o_ports_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
          }
          set o_regs [bcm_all_fanout -from $mem_reg_name/Q -endpoints_only -flat -only_cells]
          if {[sizeof_collection $o_regs] > 0} {
            set o_reg_clks [get_pins -quiet -of_objects $o_regs -filter "is_clock_pin==true"]
            if {[sizeof_collection $o_reg_clks] > 0} {
              set o_clks ""
              append_to_collection -unique o_clks [get_clocks -quiet [get_attribute -quiet $o_reg_clks clocks]]
              if {[sizeof_collection $o_clks] > 0} {
                set o_clk_name [get_object_name $o_clks]
                lappend cmd_list_bcm_all "set_max_delay $maxdelay -from \[get_pins {$from_pin_names}\] -to \[get_clocks {$o_clk_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_clocks {$o_clk_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
              } else {
                set o_pins [filter_collection [bcm_all_fanout -from $mem_reg_name/Q -endpoints_only -flat] -regexp {full_name !~ .*\*cell\*\d+.* AND object_class == pin}]
                if {[sizeof_collection $o_pins] > 0} {
                  set o_pins_name [get_object_name $o_pins]
                  lappend cmd_list_bcm_all "set_max_delay $maxdelay -from \[get_pins {$from_pin_names}\] -to \[get_pins {$o_pins_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                  lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_pins {$o_pins_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
                }
              }
            }
          }
        }
      } else {
        bcm_puts "ERROR" "Unable to find the memory array inside $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm66_wae
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm66_wae$"] < 0 } {
    set_cstr_bcm66_wae
  }
}; # end of namespace BCM (bcm66_wae)
}
#===============================================================================
# Create Guard for file DWbb_bcm66_wae_atv_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm66_wae_atv_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm66_wae_atv_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints

# -----------------------------------------------------------------------------
# [CDC_SYN_03] Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period and set_min_delay of 0 constraints for Qualifier-based Data Bus signals
# bcm66_wae_atv set_max_delay | set_min_delay constraints
namespace eval BCM {
  proc set_cstr_bcm66_wae_atv {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm66_wae_atv [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm66_wae_atv.*)}]
    foreach_in_collection cell $cell_collection_bcm66_wae_atv {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_03_max)}"
      set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_03_min)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
    
      set clk_from [getBCMClocks $cell_name "clk_push"]
      if { [sizeof_collection $clk_from] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clk_dst [getBCMClocks $cell_name "clk_pop"]
      if { [sizeof_collection $clk_dst] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set clkPeriod [getBCMClockPeriod $cell_name "clk_pop" $clk_dst]
      if {$clkPeriod eq ""} {
        continue
      }
    
      set mem_reg_name "$cell_name/U_FIFO_MEM/mem_array_reg*"
      set sync_cell_name "$cell_name/*U_FIFO_CTL/U_POP_FIFOFCTL/U_sync/GEN_TMR_*"
      set mem_regs [get_cells -quiet $mem_reg_name]
      if { [sizeof_collection $mem_regs] > 0 } {
        set clkPeriodFactor 1
        if { [get_cells -quiet $sync_cell_name/GEN_FST2* ] != "" } {
          set clkPeriodFactor 1.5
        } elseif { [get_cells -quiet $sync_cell_name/GEN_FST3* ] != "" } {
          set clkPeriodFactor 2.5
        } elseif { [get_cells -quiet $sync_cell_name/GEN_FST4* ] != "" } {
          set clkPeriodFactor 3.5
        }
        set maxdelay [expr $clkPeriodFactor*$clkPeriod]
        set from_pins [get_pins -quiet -of_objects $mem_regs -filter "is_clock_pin==true"]
        if { [sizeof_collection $from_pins] > 0 } {
          set from_pin_names [get_object_name $from_pins]
          set o_ports [filter_collection [bcm_all_fanout -from $mem_reg_name/Q -endpoints_only -flat] "object_class == port"]
          if {[sizeof_collection $o_ports] > 0} {
            set o_ports_name [get_object_name $o_ports]
            lappend cmd_list_bcm_all "set_max_delay $maxdelay -from \[get_pins {$from_pin_names}\] -to \[get_ports {$o_ports_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_ports {$o_ports_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
          }
          set o_regs [bcm_all_fanout -from $mem_reg_name/Q -endpoints_only -flat -only_cells]
          if {[sizeof_collection $o_regs] > 0} {
            set o_reg_clks [get_pins -quiet -of_objects $o_regs -filter "is_clock_pin==true"]
            if {[sizeof_collection $o_reg_clks] > 0} {
              set o_clks ""
              append_to_collection -unique o_clks [get_clocks -quiet [get_attribute -quiet $o_reg_clks clocks]]
              if {[sizeof_collection $o_clks] > 0} {
                set o_clk_name [get_object_name $o_clks]
                lappend cmd_list_bcm_all "set_max_delay $maxdelay -from \[get_pins {$from_pin_names}\] -to \[get_clocks {$o_clk_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_clocks {$o_clk_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
              } else {
                set o_pins [filter_collection [bcm_all_fanout -from $mem_reg_name/Q -endpoints_only -flat] -regexp {full_name !~ .*\*cell\*\d+.* AND object_class == pin}]
                if {[sizeof_collection $o_pins] > 0} {
                  set o_pins_name [get_object_name $o_pins]
                  lappend cmd_list_bcm_all "set_max_delay $maxdelay -from \[get_pins {$from_pin_names}\] -to \[get_pins {$o_pins_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                  lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$from_pin_names}\] -to \[get_pins {$o_pins_name}\] $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
                }
              }
            }
          }
        }
      } else {
        bcm_puts "ERROR" "Unable to find the memory array inside $cell_name"
      }
    }
  }; # end of proc set_cstr_bcm66_wae_atv
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm66_wae_atv$"] < 0 } {
    set_cstr_bcm66_wae_atv
  }
}; # end of namespace BCM (bcm66_wae_atv)
}
#===============================================================================
# Create Guard for file DWbb_bcm94_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__DWC_ddrctl_bcm94_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : DWbb_bcm94_cdc_constraints.tcl
# Description : Synthesis timing constraints

# -----------------------------------------------------------------------------
# [MCP_SYN] Define set_multicycle_path as the value of parameter CYCLES
# Set multiple cycles path
namespace eval BCM {
  proc set_cstr_bcm94 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    set cell_collection_bcm94 [filter_collection [get_cells -hierarchical *] -regexp {(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm94.*)}]
    foreach_in_collection cell $cell_collection_bcm94 {
      set cell_name [get_object_name $cell]
      set inst_name [get_attribute $cell $name_attr]
      set cmd_cmnt "-comment {Instance $inst_name: $cmnts_arr(MCP_SYN)}"
      if { [llength $bcm_hier_to_skip] > 0 } {
        set bcm_skip 0
        foreach bcm_skip_inst $bcm_hier_to_skip {
          if { [regexp "^$bcm_skip_inst" $cell_name] } {
            set bcm_skip 1
            break
          }
        }
        if {$bcm_skip == 1} {
          continue
        }
      }
      set clks [getBCMClocks $cell_name "clk"]
      if { [sizeof_collection $clks] == 0 } {
        # Skip, the clock is probably tied off
        continue
      }
      set N [getBCMParamFromNameOrIndex $cell bcm94 CYCLES 1]
      if { [string is digit -strict $N] && ($N > 0) } {
        set clk_name [get_object_name $clks]
        set d_pins [get_pins -quiet $cell_name/GEN_MCP_?CYC?mcp_data_?cyc*/next_state]
        if { [sizeof_collection $d_pins] == 0 } {
          set d_pins [get_pins $cell_name/GEN_MCP_?CYC?mcp_data_?cyc*/D]
        }
        if { [sizeof_collection $d_pins] > 0 } {
          set d_pins_name [get_object_name $d_pins]
          lappend cmd_list_bcm_all "set_multicycle_path $N -from \[get_clocks {$clk_name}\] -to {$d_pins_name} $reset_path_option $cmd_cmnt"
        } else {
          bcm_puts "WARN" "Unrecognized bcm94 structure in $cell_name"
        }
      } else {
        bcm_puts "WARN" "Unable to get value of CYCLES in $cell_name, skip constraining this instance."
      }
    }
  }; # end of proc set_cstr_bcm94
  if { [lsearch -regexp $bcm_mod_to_skip ".*_bcm94$"] < 0 } {
    set_cstr_bcm94
  }
}; # end of namespace BCM (bcm94)
}
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
# -------------------------------------------------------------------------------

# Filename    : common_end.tcl
# Description : Common procs which will be exectued at the end

namespace eval BCM {
  variable cmd
  if { [llength $cmd_list_bcm_all] > 0 } {
    echo " bcm constraints " >> ../../constraints/bcm_constraints_generated.txt
    foreach cmd $cmd_list_bcm_all {
      runCmd $cmd
      echo "$cmd"  >> ../../constraints/bcm_constraints_generated.txt 
    }
  } else {
    bcm_puts "INFO" "No BCM CDC constraints are applied."
  }
  unalias bcm_all_fanin
  unalias bcm_all_fanout
}

set _sDWC_ddrctl_hierarchy i_uddrctl/
#if {[info exists ::env(sDWC_ddrctl_hierarchy)]} {
#set _sDWC_ddrctl_hierarchy  $::env(sDWC_ddrctl_hierarchy)
#}
echo "${_sDWC_ddrctl_hierarchy}"  >> ../../constraints/bcm_constraints_generated.txt

      # Register MSTR0 field lpddr4 
      set regb_ddrc_ch0_mstr0_lpddr4BaseOffset 1
      set regb_ddrc_ch0_mstr0_lpddr4Width 1

         if {${regb_ddrc_ch0_mstr0_lpddr4Width} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_mstr0_lpddr4Width}} {incr bit} {
               set regb_ddrc_ch0_mstr0_lpddr4Offset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_reg[${regb_ddrc_ch0_mstr0_lpddr4Offset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_reg[${regb_ddrc_ch0_mstr0_lpddr4Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_reg[${regb_ddrc_ch0_mstr0_lpddr4Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      # Register MSTR0 field lpddr5 
      set regb_ddrc_ch0_mstr0_lpddr5BaseOffset 3
      set regb_ddrc_ch0_mstr0_lpddr5Width 1

         if {${regb_ddrc_ch0_mstr0_lpddr5Width} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_mstr0_lpddr5Width}} {incr bit} {
               set regb_ddrc_ch0_mstr0_lpddr5Offset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5_reg[${regb_ddrc_ch0_mstr0_lpddr5Offset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5_reg[${regb_ddrc_ch0_mstr0_lpddr5Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5_reg[${regb_ddrc_ch0_mstr0_lpddr5Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      # Register MSTR0 field lpddr5x 
      set regb_ddrc_ch0_mstr0_lpddr5xBaseOffset 11
      set regb_ddrc_ch0_mstr0_lpddr5xWidth 1

         if {${regb_ddrc_ch0_mstr0_lpddr5xWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_mstr0_lpddr5xWidth}} {incr bit} {
               set regb_ddrc_ch0_mstr0_lpddr5xOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5x_reg[${regb_ddrc_ch0_mstr0_lpddr5xOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5x_reg[${regb_ddrc_ch0_mstr0_lpddr5xOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5x_reg[${regb_ddrc_ch0_mstr0_lpddr5xOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5x_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5x_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr5x_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }

   # Register MSTR0 field data_bus_width 
   set regb_ddrc_ch0_mstr0_data_bus_widthBaseOffset 12
   set regb_ddrc_ch0_mstr0_data_bus_widthWidth 2

      if {${regb_ddrc_ch0_mstr0_data_bus_widthWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_mstr0_data_bus_widthWidth}} {incr bit} {
            set regb_ddrc_ch0_mstr0_data_bus_widthOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_data_bus_width_reg[${regb_ddrc_ch0_mstr0_data_bus_widthOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_data_bus_width_reg[${regb_ddrc_ch0_mstr0_data_bus_widthOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_data_bus_width_reg[${regb_ddrc_ch0_mstr0_data_bus_widthOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_data_bus_width_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_data_bus_width_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_data_bus_width_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

   # Register MSTR0 field burst_rdwr 
   set regb_ddrc_ch0_mstr0_burst_rdwrBaseOffset 16
   set regb_ddrc_ch0_mstr0_burst_rdwrWidth 5

      if {${regb_ddrc_ch0_mstr0_burst_rdwrWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_mstr0_burst_rdwrWidth}} {incr bit} {
            set regb_ddrc_ch0_mstr0_burst_rdwrOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_burst_rdwr_reg[${regb_ddrc_ch0_mstr0_burst_rdwrOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_burst_rdwr_reg[${regb_ddrc_ch0_mstr0_burst_rdwrOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_burst_rdwr_reg[${regb_ddrc_ch0_mstr0_burst_rdwrOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_burst_rdwr_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_burst_rdwr_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_burst_rdwr_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }


      # Register MSTR0 field active_ranks 
      set regb_ddrc_ch0_mstr0_active_ranksBaseOffset 24
      set regb_ddrc_ch0_mstr0_active_ranks_size_cc_constant 2
      if {${regb_ddrc_ch0_mstr0_active_ranks_size_cc_constant} == 2} {
         set regb_ddrc_ch0_mstr0_active_ranksWidth 2
      } else {
         set regb_ddrc_ch0_mstr0_active_ranksWidth 4
      }

         if {${regb_ddrc_ch0_mstr0_active_ranksWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_mstr0_active_ranksWidth}} {incr bit} {
               set regb_ddrc_ch0_mstr0_active_ranksOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_ranks_reg[${regb_ddrc_ch0_mstr0_active_ranksOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_ranks_reg[${regb_ddrc_ch0_mstr0_active_ranksOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_ranks_reg[${regb_ddrc_ch0_mstr0_active_ranksOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_ranks_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_ranks_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_ranks_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      # Register MSTR2 field target_frequency 
      set regb_ddrc_ch0_mstr2_target_frequencyBaseOffset 0
      set regb_ddrc_ch0_mstr2_target_frequencyWidth 2

         if {${regb_ddrc_ch0_mstr2_target_frequencyWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_mstr2_target_frequencyWidth}} {incr bit} {
               set regb_ddrc_ch0_mstr2_target_frequencyOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_frequency_reg[${regb_ddrc_ch0_mstr2_target_frequencyOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_frequency_reg[${regb_ddrc_ch0_mstr2_target_frequencyOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_frequency_reg[${regb_ddrc_ch0_mstr2_target_frequencyOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_frequency_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_frequency_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_frequency_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }

      # Register DERATECTL0 field lpddr4_refresh_mode 
      set regb_ddrc_ch0_deratectl0_lpddr4_refresh_modeBaseOffset 1
      set regb_ddrc_ch0_deratectl0_lpddr4_refresh_modeWidth 1

         if {${regb_ddrc_ch0_deratectl0_lpddr4_refresh_modeWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_deratectl0_lpddr4_refresh_modeWidth}} {incr bit} {
               set regb_ddrc_ch0_deratectl0_lpddr4_refresh_modeOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_refresh_mode_reg[${regb_ddrc_ch0_deratectl0_lpddr4_refresh_modeOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_refresh_mode_reg[${regb_ddrc_ch0_deratectl0_lpddr4_refresh_modeOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_refresh_mode_reg[${regb_ddrc_ch0_deratectl0_lpddr4_refresh_modeOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_refresh_mode_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_refresh_mode_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_lpddr4_refresh_mode_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register DERATECTL0 field dis_trefi_x0125 
      set regb_ddrc_ch0_deratectl0_dis_trefi_x0125BaseOffset 4
      set regb_ddrc_ch0_deratectl0_dis_trefi_x0125Width 1

         if {${regb_ddrc_ch0_deratectl0_dis_trefi_x0125Width} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_deratectl0_dis_trefi_x0125Width}} {incr bit} {
               set regb_ddrc_ch0_deratectl0_dis_trefi_x0125Offset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_trefi_x0125_reg[${regb_ddrc_ch0_deratectl0_dis_trefi_x0125Offset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_trefi_x0125_reg[${regb_ddrc_ch0_deratectl0_dis_trefi_x0125Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_trefi_x0125_reg[${regb_ddrc_ch0_deratectl0_dis_trefi_x0125Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_trefi_x0125_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_trefi_x0125_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_trefi_x0125_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register DERATECTL0 field use_slow_rm_in_low_temp 
      set regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_tempBaseOffset 5
      set regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_tempWidth 1

         if {${regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_tempWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_tempWidth}} {incr bit} {
               set regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_tempOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_use_slow_rm_in_low_temp_reg[${regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_tempOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_use_slow_rm_in_low_temp_reg[${regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_tempOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_use_slow_rm_in_low_temp_reg[${regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_tempOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_use_slow_rm_in_low_temp_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_use_slow_rm_in_low_temp_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_use_slow_rm_in_low_temp_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register DERATECTL1 field active_derate_byte_rank0 
      set regb_ddrc_ch0_deratectl1_active_derate_byte_rank0BaseOffset 0
      set regb_ddrc_ch0_deratectl1_active_derate_byte_rank0Width 8

         if {${regb_ddrc_ch0_deratectl1_active_derate_byte_rank0Width} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_deratectl1_active_derate_byte_rank0Width}} {incr bit} {
               set regb_ddrc_ch0_deratectl1_active_derate_byte_rank0Offset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank0_reg[${regb_ddrc_ch0_deratectl1_active_derate_byte_rank0Offset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank0_reg[${regb_ddrc_ch0_deratectl1_active_derate_byte_rank0Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank0_reg[${regb_ddrc_ch0_deratectl1_active_derate_byte_rank0Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank0_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank0_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank0_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


         # Register DERATECTL2 field active_derate_byte_rank1 
         set regb_ddrc_ch0_deratectl2_active_derate_byte_rank1BaseOffset 0
         set regb_ddrc_ch0_deratectl2_active_derate_byte_rank1Width 8

            if {${regb_ddrc_ch0_deratectl2_active_derate_byte_rank1Width} > 1} {
               for {set bit 0} {$bit < ${regb_ddrc_ch0_deratectl2_active_derate_byte_rank1Width}} {incr bit} {
                  set regb_ddrc_ch0_deratectl2_active_derate_byte_rank1Offset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank1_reg[${regb_ddrc_ch0_deratectl2_active_derate_byte_rank1Offset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank1_reg[${regb_ddrc_ch0_deratectl2_active_derate_byte_rank1Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank1_reg[${regb_ddrc_ch0_deratectl2_active_derate_byte_rank1Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank1_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank1_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_active_derate_byte_rank1_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


      # Register DERATEDBGCTL field dbg_mr4_rank_sel 
      set regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_selBaseOffset 4
      set regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_selWidth 2

         if {${regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_selWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_selWidth}} {incr bit} {
               set regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_selOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dbg_mr4_rank_sel_reg[${regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_selOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dbg_mr4_rank_sel_reg[${regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_selOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dbg_mr4_rank_sel_reg[${regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_selOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dbg_mr4_rank_sel_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dbg_mr4_rank_sel_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dbg_mr4_rank_sel_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      # Register CLKGATECTL field bsm_clk_on 
      set regb_ddrc_ch0_clkgatectl_bsm_clk_onBaseOffset 0
      set regb_ddrc_ch0_clkgatectl_bsm_clk_onWidth 6

         if {${regb_ddrc_ch0_clkgatectl_bsm_clk_onWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_clkgatectl_bsm_clk_onWidth}} {incr bit} {
               set regb_ddrc_ch0_clkgatectl_bsm_clk_onOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_bsm_clk_on_reg[${regb_ddrc_ch0_clkgatectl_bsm_clk_onOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_bsm_clk_on_reg[${regb_ddrc_ch0_clkgatectl_bsm_clk_onOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_bsm_clk_on_reg[${regb_ddrc_ch0_clkgatectl_bsm_clk_onOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_bsm_clk_on_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_bsm_clk_on_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_bsm_clk_on_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register RFSHMOD0 field per_bank_refresh 
      set regb_ddrc_ch0_rfshmod0_per_bank_refreshBaseOffset 8
      set regb_ddrc_ch0_rfshmod0_per_bank_refreshWidth 1

         if {${regb_ddrc_ch0_rfshmod0_per_bank_refreshWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_rfshmod0_per_bank_refreshWidth}} {incr bit} {
               set regb_ddrc_ch0_rfshmod0_per_bank_refreshOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_reg[${regb_ddrc_ch0_rfshmod0_per_bank_refreshOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_reg[${regb_ddrc_ch0_rfshmod0_per_bank_refreshOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_reg[${regb_ddrc_ch0_rfshmod0_per_bank_refreshOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register RFSHMOD0 field per_bank_refresh_opt_en 
      set regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_enBaseOffset 9
      set regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_enWidth 1

         if {${regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_enWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_enWidth}} {incr bit} {
               set regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_enOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_opt_en_reg[${regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_enOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_opt_en_reg[${regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_opt_en_reg[${regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_opt_en_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_opt_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_per_bank_refresh_opt_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register RFSHMOD0 field fixed_crit_refpb_bank_en 
      set regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_enBaseOffset 24
      set regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_enWidth 1

         if {${regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_enWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_enWidth}} {incr bit} {
               set regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_enOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en_reg[${regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_enOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en_reg[${regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en_reg[${regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
         # Register RFMMOD0 field rfmsbc 
         set regb_ddrc_ch0_rfmmod0_rfmsbcBaseOffset 4
         set regb_ddrc_ch0_rfmmod0_rfmsbcWidth 1

            if {${regb_ddrc_ch0_rfmmod0_rfmsbcWidth} > 1} {
               for {set bit 0} {$bit < ${regb_ddrc_ch0_rfmmod0_rfmsbcWidth}} {incr bit} {
                  set regb_ddrc_ch0_rfmmod0_rfmsbcOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rfmsbc_reg[${regb_ddrc_ch0_rfmmod0_rfmsbcOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rfmsbc_reg[${regb_ddrc_ch0_rfmmod0_rfmsbcOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rfmsbc_reg[${regb_ddrc_ch0_rfmmod0_rfmsbcOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rfmsbc_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rfmsbc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rfmsbc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


      # Register RFMMOD1 field init_raa_cnt 
      set regb_ddrc_ch0_rfmmod1_init_raa_cntBaseOffset 0
      set regb_ddrc_ch0_rfmmod1_init_raa_cntWidth 11

         if {${regb_ddrc_ch0_rfmmod1_init_raa_cntWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_rfmmod1_init_raa_cntWidth}} {incr bit} {
               set regb_ddrc_ch0_rfmmod1_init_raa_cntOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_raa_cnt_reg[${regb_ddrc_ch0_rfmmod1_init_raa_cntOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_raa_cnt_reg[${regb_ddrc_ch0_rfmmod1_init_raa_cntOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_raa_cnt_reg[${regb_ddrc_ch0_rfmmod1_init_raa_cntOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_raa_cnt_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_raa_cnt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_raa_cnt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


   # Register ZQCTL0 field zq_resistor_shared 
   set regb_ddrc_ch0_zqctl0_zq_resistor_sharedBaseOffset 29
   set regb_ddrc_ch0_zqctl0_zq_resistor_sharedWidth 1

      if {${regb_ddrc_ch0_zqctl0_zq_resistor_sharedWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_zqctl0_zq_resistor_sharedWidth}} {incr bit} {
            set regb_ddrc_ch0_zqctl0_zq_resistor_sharedOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_zq_resistor_shared_reg[${regb_ddrc_ch0_zqctl0_zq_resistor_sharedOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_zq_resistor_shared_reg[${regb_ddrc_ch0_zqctl0_zq_resistor_sharedOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_zq_resistor_shared_reg[${regb_ddrc_ch0_zqctl0_zq_resistor_sharedOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_zq_resistor_shared_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_zq_resistor_shared_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_zq_resistor_shared_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }
         # Register HWFFCCTL field init_fsp 
         set regb_ddrc_ch0_hwffcctl_init_fspBaseOffset 4
         set regb_ddrc_ch0_hwffcctl_init_fspWidth 1

            if {${regb_ddrc_ch0_hwffcctl_init_fspWidth} > 1} {
               for {set bit 0} {$bit < ${regb_ddrc_ch0_hwffcctl_init_fspWidth}} {incr bit} {
                  set regb_ddrc_ch0_hwffcctl_init_fspOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_fsp_reg[${regb_ddrc_ch0_hwffcctl_init_fspOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_fsp_reg[${regb_ddrc_ch0_hwffcctl_init_fspOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_fsp_reg[${regb_ddrc_ch0_hwffcctl_init_fspOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_fsp_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_fsp_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_fsp_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


      # Register HWFFCCTL field init_vrcg 
      set regb_ddrc_ch0_hwffcctl_init_vrcgBaseOffset 5
      set regb_ddrc_ch0_hwffcctl_init_vrcgWidth 1

         if {${regb_ddrc_ch0_hwffcctl_init_vrcgWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_hwffcctl_init_vrcgWidth}} {incr bit} {
               set regb_ddrc_ch0_hwffcctl_init_vrcgOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_vrcg_reg[${regb_ddrc_ch0_hwffcctl_init_vrcgOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_vrcg_reg[${regb_ddrc_ch0_hwffcctl_init_vrcgOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_vrcg_reg[${regb_ddrc_ch0_hwffcctl_init_vrcgOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_vrcg_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_vrcg_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_init_vrcg_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register HWFFCCTL field target_vrcg 
      set regb_ddrc_ch0_hwffcctl_target_vrcgBaseOffset 6
      set regb_ddrc_ch0_hwffcctl_target_vrcgWidth 1

         if {${regb_ddrc_ch0_hwffcctl_target_vrcgWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_hwffcctl_target_vrcgWidth}} {incr bit} {
               set regb_ddrc_ch0_hwffcctl_target_vrcgOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_vrcg_reg[${regb_ddrc_ch0_hwffcctl_target_vrcgOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_vrcg_reg[${regb_ddrc_ch0_hwffcctl_target_vrcgOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_vrcg_reg[${regb_ddrc_ch0_hwffcctl_target_vrcgOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_vrcg_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_vrcg_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_target_vrcg_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


   # Register DFILPCFG0 field dfi_lp_en_pd 
   set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pdBaseOffset 0
   set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pdWidth 1

      if {${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pdWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pdWidth}} {incr bit} {
            set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pdOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_pd_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pdOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_pd_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pdOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_pd_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pdOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_pd_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_pd_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_pd_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

   # Register DFILPCFG0 field dfi_lp_en_sr 
   set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_srBaseOffset 4
   set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_srWidth 1

      if {${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_srWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_srWidth}} {incr bit} {
            set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_srOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_sr_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_srOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_sr_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_srOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_sr_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_srOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_sr_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_sr_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_sr_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

      # Register DFILPCFG0 field dfi_lp_en_dsm 
      set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsmBaseOffset 8
      set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsmWidth 1

         if {${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsmWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsmWidth}} {incr bit} {
               set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsmOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_dsm_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsmOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_dsm_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsmOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_dsm_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsmOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_dsm_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_dsm_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_dsm_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


   # Register DFILPCFG0 field dfi_lp_en_data 
   set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dataBaseOffset 16
   set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dataWidth 1

      if {${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dataWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dataWidth}} {incr bit} {
            set regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dataOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_data_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dataOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_data_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dataOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_data_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dataOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_data_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_data_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_en_data_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

      # Register DFILPCFG0 field dfi_lp_data_req_en 
      set regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_enBaseOffset 20
      set regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_enWidth 1

         if {${regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_enWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_enWidth}} {incr bit} {
               set regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_enOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_data_req_en_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_enOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_data_req_en_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_data_req_en_reg[${regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_data_req_en_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_data_req_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_lp_data_req_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      # Register DFILPCFG0 field extra_gap_for_dfi_lp_data 
      set regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_dataBaseOffset 28
      set regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_dataWidth 2

         if {${regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_dataWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_dataWidth}} {incr bit} {
               set regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_dataOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data_reg[${regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_dataOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data_reg[${regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_dataOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data_reg[${regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_dataOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register DFIUPD0 field dfi_phyupd_en 
      set regb_ddrc_ch0_dfiupd0_dfi_phyupd_enBaseOffset 15
      set regb_ddrc_ch0_dfiupd0_dfi_phyupd_enWidth 1

         if {${regb_ddrc_ch0_dfiupd0_dfi_phyupd_enWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_dfiupd0_dfi_phyupd_enWidth}} {incr bit} {
               set regb_ddrc_ch0_dfiupd0_dfi_phyupd_enOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phyupd_en_reg[${regb_ddrc_ch0_dfiupd0_dfi_phyupd_enOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phyupd_en_reg[${regb_ddrc_ch0_dfiupd0_dfi_phyupd_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phyupd_en_reg[${regb_ddrc_ch0_dfiupd0_dfi_phyupd_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phyupd_en_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phyupd_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phyupd_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }

   # Register DFIUPD0 field ctrlupd_pre_srx 
   set regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srxBaseOffset 29
   set regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srxWidth 1

      if {${regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srxWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srxWidth}} {incr bit} {
            set regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srxOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ctrlupd_pre_srx_reg[${regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srxOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ctrlupd_pre_srx_reg[${regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srxOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ctrlupd_pre_srx_reg[${regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srxOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ctrlupd_pre_srx_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ctrlupd_pre_srx_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ctrlupd_pre_srx_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

   # Register DFIUPD0 field dis_auto_ctrlupd_srx 
   set regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srxBaseOffset 30
   set regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srxWidth 1

      if {${regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srxWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srxWidth}} {incr bit} {
            set regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srxOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx_reg[${regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srxOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx_reg[${regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srxOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx_reg[${regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srxOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

      # Register DFIMISC field phy_dbi_mode 
      set regb_ddrc_ch0_dfimisc_phy_dbi_modeBaseOffset 1
      set regb_ddrc_ch0_dfimisc_phy_dbi_modeWidth 1

         if {${regb_ddrc_ch0_dfimisc_phy_dbi_modeWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_dfimisc_phy_dbi_modeWidth}} {incr bit} {
               set regb_ddrc_ch0_dfimisc_phy_dbi_modeOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_phy_dbi_mode_reg[${regb_ddrc_ch0_dfimisc_phy_dbi_modeOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_phy_dbi_mode_reg[${regb_ddrc_ch0_dfimisc_phy_dbi_modeOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_phy_dbi_mode_reg[${regb_ddrc_ch0_dfimisc_phy_dbi_modeOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_phy_dbi_mode_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_phy_dbi_mode_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_phy_dbi_mode_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }

   # Register DFIMISC field dfi_data_cs_polarity 
   set regb_ddrc_ch0_dfimisc_dfi_data_cs_polarityBaseOffset 2
   set regb_ddrc_ch0_dfimisc_dfi_data_cs_polarityWidth 1

      if {${regb_ddrc_ch0_dfimisc_dfi_data_cs_polarityWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_dfimisc_dfi_data_cs_polarityWidth}} {incr bit} {
            set regb_ddrc_ch0_dfimisc_dfi_data_cs_polarityOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_data_cs_polarity_reg[${regb_ddrc_ch0_dfimisc_dfi_data_cs_polarityOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_data_cs_polarity_reg[${regb_ddrc_ch0_dfimisc_dfi_data_cs_polarityOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_data_cs_polarity_reg[${regb_ddrc_ch0_dfimisc_dfi_data_cs_polarityOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_data_cs_polarity_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_data_cs_polarity_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_data_cs_polarity_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }


      # Register DFIMISC field dfi_channel_mode 
      set regb_ddrc_ch0_dfimisc_dfi_channel_modeBaseOffset 16
      set regb_ddrc_ch0_dfimisc_dfi_channel_modeWidth 2

         if {${regb_ddrc_ch0_dfimisc_dfi_channel_modeWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_dfimisc_dfi_channel_modeWidth}} {incr bit} {
               set regb_ddrc_ch0_dfimisc_dfi_channel_modeOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_channel_mode_reg[${regb_ddrc_ch0_dfimisc_dfi_channel_modeOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_channel_mode_reg[${regb_ddrc_ch0_dfimisc_dfi_channel_modeOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_channel_mode_reg[${regb_ddrc_ch0_dfimisc_dfi_channel_modeOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_channel_mode_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_channel_mode_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_channel_mode_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register DFIPHYMSTR field dfi_phymstr_en 
      set regb_ddrc_ch0_dfiphymstr_dfi_phymstr_enBaseOffset 0
      set regb_ddrc_ch0_dfiphymstr_dfi_phymstr_enWidth 1

         if {${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_enWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_enWidth}} {incr bit} {
               set regb_ddrc_ch0_dfiphymstr_dfi_phymstr_enOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_en_reg[${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_enOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_en_reg[${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_en_reg[${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_en_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register DFIPHYMSTR field dfi_phymstr_blk_ref_x32 
      set regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32BaseOffset 24
      set regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32Width 8

         if {${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32Width} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32Width}} {incr bit} {
               set regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32Offset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32_reg[${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32Offset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32_reg[${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32_reg[${regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register ECCCFG0 field ecc_mode 
      set regb_ddrc_ch0_ecccfg0_ecc_modeBaseOffset 0
      set regb_ddrc_ch0_ecccfg0_ecc_modeWidth 3

         if {${regb_ddrc_ch0_ecccfg0_ecc_modeWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_ecccfg0_ecc_modeWidth}} {incr bit} {
               set regb_ddrc_ch0_ecccfg0_ecc_modeOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_mode_reg[${regb_ddrc_ch0_ecccfg0_ecc_modeOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_mode_reg[${regb_ddrc_ch0_ecccfg0_ecc_modeOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_mode_reg[${regb_ddrc_ch0_ecccfg0_ecc_modeOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_mode_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_mode_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_mode_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


         # Register ECCCFG0 field ecc_ap_en 
         set regb_ddrc_ch0_ecccfg0_ecc_ap_enBaseOffset 6
         set regb_ddrc_ch0_ecccfg0_ecc_ap_enWidth 1

            if {${regb_ddrc_ch0_ecccfg0_ecc_ap_enWidth} > 1} {
               for {set bit 0} {$bit < ${regb_ddrc_ch0_ecccfg0_ecc_ap_enWidth}} {incr bit} {
                  set regb_ddrc_ch0_ecccfg0_ecc_ap_enOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_en_reg[${regb_ddrc_ch0_ecccfg0_ecc_ap_enOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_en_reg[${regb_ddrc_ch0_ecccfg0_ecc_ap_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_en_reg[${regb_ddrc_ch0_ecccfg0_ecc_ap_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_en_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         # Register ECCCFG0 field ecc_region_remap_en 
         set regb_ddrc_ch0_ecccfg0_ecc_region_remap_enBaseOffset 7
         set regb_ddrc_ch0_ecccfg0_ecc_region_remap_enWidth 1

            if {${regb_ddrc_ch0_ecccfg0_ecc_region_remap_enWidth} > 1} {
               for {set bit 0} {$bit < ${regb_ddrc_ch0_ecccfg0_ecc_region_remap_enWidth}} {incr bit} {
                  set regb_ddrc_ch0_ecccfg0_ecc_region_remap_enOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_remap_en_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_remap_enOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_remap_en_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_remap_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_remap_en_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_remap_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_remap_en_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_remap_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_remap_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         # Register ECCCFG0 field ecc_ap_err_threshold 
         set regb_ddrc_ch0_ecccfg0_ecc_ap_err_thresholdBaseOffset 24
         set regb_ddrc_ch0_ecccfg0_ecc_ap_err_thresholdWidth 3

            if {${regb_ddrc_ch0_ecccfg0_ecc_ap_err_thresholdWidth} > 1} {
               for {set bit 0} {$bit < ${regb_ddrc_ch0_ecccfg0_ecc_ap_err_thresholdWidth}} {incr bit} {
                  set regb_ddrc_ch0_ecccfg0_ecc_ap_err_thresholdOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_err_threshold_reg[${regb_ddrc_ch0_ecccfg0_ecc_ap_err_thresholdOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_err_threshold_reg[${regb_ddrc_ch0_ecccfg0_ecc_ap_err_thresholdOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_err_threshold_reg[${regb_ddrc_ch0_ecccfg0_ecc_ap_err_thresholdOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_err_threshold_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_err_threshold_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_ap_err_threshold_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         # Register ECCCFG0 field ecc_region_map_other 
         set regb_ddrc_ch0_ecccfg0_ecc_region_map_otherBaseOffset 29
         set regb_ddrc_ch0_ecccfg0_ecc_region_map_otherWidth 1

            if {${regb_ddrc_ch0_ecccfg0_ecc_region_map_otherWidth} > 1} {
               for {set bit 0} {$bit < ${regb_ddrc_ch0_ecccfg0_ecc_region_map_otherWidth}} {incr bit} {
                  set regb_ddrc_ch0_ecccfg0_ecc_region_map_otherOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_other_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_map_otherOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_other_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_map_otherOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_other_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_map_otherOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_other_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_other_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_other_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         # Register ECCCFG0 field ecc_region_map_granu 
         set regb_ddrc_ch0_ecccfg0_ecc_region_map_granuBaseOffset 30
         set regb_ddrc_ch0_ecccfg0_ecc_region_map_granuWidth 2

            if {${regb_ddrc_ch0_ecccfg0_ecc_region_map_granuWidth} > 1} {
               for {set bit 0} {$bit < ${regb_ddrc_ch0_ecccfg0_ecc_region_map_granuWidth}} {incr bit} {
                  set regb_ddrc_ch0_ecccfg0_ecc_region_map_granuOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_granu_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_map_granuOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_granu_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_map_granuOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_granu_reg[${regb_ddrc_ch0_ecccfg0_ecc_region_map_granuOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_granu_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_granu_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_ecc_region_map_granu_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


   # Register DBICTL field dm_en 
   set regb_ddrc_ch0_dbictl_dm_enBaseOffset 0
   set regb_ddrc_ch0_dbictl_dm_enWidth 1

      if {${regb_ddrc_ch0_dbictl_dm_enWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_dbictl_dm_enWidth}} {incr bit} {
            set regb_ddrc_ch0_dbictl_dm_enOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dm_en_reg[${regb_ddrc_ch0_dbictl_dm_enOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dm_en_reg[${regb_ddrc_ch0_dbictl_dm_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dm_en_reg[${regb_ddrc_ch0_dbictl_dm_enOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dm_en_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dm_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_dm_en_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

   # Register ODTMAP field rank0_wr_odt 
   set regb_ddrc_ch0_odtmap_rank0_wr_odtBaseOffset 0
   set regb_ddrc_ch0_odtmap_rank0_wr_odtWidth 2

      if {${regb_ddrc_ch0_odtmap_rank0_wr_odtWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_odtmap_rank0_wr_odtWidth}} {incr bit} {
            set regb_ddrc_ch0_odtmap_rank0_wr_odtOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_wr_odt_reg[${regb_ddrc_ch0_odtmap_rank0_wr_odtOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_wr_odt_reg[${regb_ddrc_ch0_odtmap_rank0_wr_odtOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_wr_odt_reg[${regb_ddrc_ch0_odtmap_rank0_wr_odtOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_wr_odt_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_wr_odt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_wr_odt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

   # Register ODTMAP field rank0_rd_odt 
   set regb_ddrc_ch0_odtmap_rank0_rd_odtBaseOffset 4
   set regb_ddrc_ch0_odtmap_rank0_rd_odtWidth 2

      if {${regb_ddrc_ch0_odtmap_rank0_rd_odtWidth} > 1} {
         for {set bit 0} {$bit < ${regb_ddrc_ch0_odtmap_rank0_rd_odtWidth}} {incr bit} {
            set regb_ddrc_ch0_odtmap_rank0_rd_odtOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_rd_odt_reg[${regb_ddrc_ch0_odtmap_rank0_rd_odtOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_rd_odt_reg[${regb_ddrc_ch0_odtmap_rank0_rd_odtOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_rd_odt_reg[${regb_ddrc_ch0_odtmap_rank0_rd_odtOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_rd_odt_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_rd_odt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank0_rd_odt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }

      # Register ODTMAP field rank1_wr_odt 
      set regb_ddrc_ch0_odtmap_rank1_wr_odtBaseOffset 8
      set regb_ddrc_ch0_odtmap_rank1_wr_odtWidth 2

         if {${regb_ddrc_ch0_odtmap_rank1_wr_odtWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_odtmap_rank1_wr_odtWidth}} {incr bit} {
               set regb_ddrc_ch0_odtmap_rank1_wr_odtOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_wr_odt_reg[${regb_ddrc_ch0_odtmap_rank1_wr_odtOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_wr_odt_reg[${regb_ddrc_ch0_odtmap_rank1_wr_odtOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_wr_odt_reg[${regb_ddrc_ch0_odtmap_rank1_wr_odtOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_wr_odt_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_wr_odt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_wr_odt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register ODTMAP field rank1_rd_odt 
      set regb_ddrc_ch0_odtmap_rank1_rd_odtBaseOffset 12
      set regb_ddrc_ch0_odtmap_rank1_rd_odtWidth 2

         if {${regb_ddrc_ch0_odtmap_rank1_rd_odtWidth} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_odtmap_rank1_rd_odtWidth}} {incr bit} {
               set regb_ddrc_ch0_odtmap_rank1_rd_odtOffset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_rd_odt_reg[${regb_ddrc_ch0_odtmap_rank1_rd_odtOffset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_rd_odt_reg[${regb_ddrc_ch0_odtmap_rank1_rd_odtOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_rd_odt_reg[${regb_ddrc_ch0_odtmap_rank1_rd_odtOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_rd_odt_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_rd_odt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_rank1_rd_odt_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register INITTMG0 field pre_cke_x1024 
      set regb_ddrc_ch0_inittmg0_pre_cke_x1024BaseOffset 0
      set regb_ddrc_ch0_inittmg0_pre_cke_x1024Width 13

         if {${regb_ddrc_ch0_inittmg0_pre_cke_x1024Width} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_inittmg0_pre_cke_x1024Width}} {incr bit} {
               set regb_ddrc_ch0_inittmg0_pre_cke_x1024Offset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_pre_cke_x1024_reg[${regb_ddrc_ch0_inittmg0_pre_cke_x1024Offset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_pre_cke_x1024_reg[${regb_ddrc_ch0_inittmg0_pre_cke_x1024Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_pre_cke_x1024_reg[${regb_ddrc_ch0_inittmg0_pre_cke_x1024Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_pre_cke_x1024_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_pre_cke_x1024_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_pre_cke_x1024_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }


      # Register INITTMG0 field post_cke_x1024 
      set regb_ddrc_ch0_inittmg0_post_cke_x1024BaseOffset 16
      set regb_ddrc_ch0_inittmg0_post_cke_x1024Width 10

         if {${regb_ddrc_ch0_inittmg0_post_cke_x1024Width} > 1} {
            for {set bit 0} {$bit < ${regb_ddrc_ch0_inittmg0_post_cke_x1024Width}} {incr bit} {
               set regb_ddrc_ch0_inittmg0_post_cke_x1024Offset $bit
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_post_cke_x1024_reg[${regb_ddrc_ch0_inittmg0_post_cke_x1024Offset}]]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_post_cke_x1024_reg[${regb_ddrc_ch0_inittmg0_post_cke_x1024Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_post_cke_x1024_reg[${regb_ddrc_ch0_inittmg0_post_cke_x1024Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
         } else {
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_post_cke_x1024_reg*]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_post_cke_x1024_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_ddrc_ch0_post_cke_x1024_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }

   # Register ADDRMAP12 field nonbinary_device_density 
   set regb_addr_map0_addrmap12_nonbinary_device_densityBaseOffset 0
   set regb_addr_map0_addrmap12_nonbinary_device_densityWidth 3

      if {${regb_addr_map0_addrmap12_nonbinary_device_densityWidth} > 1} {
         for {set bit 0} {$bit < ${regb_addr_map0_addrmap12_nonbinary_device_densityWidth}} {incr bit} {
            set regb_addr_map0_addrmap12_nonbinary_device_densityOffset $bit
            if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_addr_map0_nonbinary_device_density_reg[${regb_addr_map0_addrmap12_nonbinary_device_densityOffset}]]] } {
               set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_addr_map0_nonbinary_device_density_reg[${regb_addr_map0_addrmap12_nonbinary_device_densityOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_addr_map0_nonbinary_device_density_reg[${regb_addr_map0_addrmap12_nonbinary_device_densityOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            }
         }
      } else {
         if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_addr_map0_nonbinary_device_density_reg*]] } {
            set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_addr_map0_nonbinary_device_density_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
            set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_addr_map0_nonbinary_device_density_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
         }
      }


               # Register DRAMSET1TMG32 field ws_fs2wck_sus 
               set regb_freq0_ch0_dramset1tmg32_ws_fs2wck_susBaseOffset 0
               set regb_freq0_ch0_dramset1tmg32_ws_fs2wck_susWidth 4

                  if {${regb_freq0_ch0_dramset1tmg32_ws_fs2wck_susWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq0_ch0_dramset1tmg32_ws_fs2wck_susWidth}} {incr bit} {
                        set regb_freq0_ch0_dramset1tmg32_ws_fs2wck_susOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_fs2wck_sus_reg[${regb_freq0_ch0_dramset1tmg32_ws_fs2wck_susOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_fs2wck_sus_reg[${regb_freq0_ch0_dramset1tmg32_ws_fs2wck_susOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_fs2wck_sus_reg[${regb_freq0_ch0_dramset1tmg32_ws_fs2wck_susOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_fs2wck_sus_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_fs2wck_sus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_fs2wck_sus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               # Register DRAMSET1TMG32 field t_wcksus 
               set regb_freq0_ch0_dramset1tmg32_t_wcksusBaseOffset 8
               set regb_freq0_ch0_dramset1tmg32_t_wcksusWidth 4

                  if {${regb_freq0_ch0_dramset1tmg32_t_wcksusWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq0_ch0_dramset1tmg32_t_wcksusWidth}} {incr bit} {
                        set regb_freq0_ch0_dramset1tmg32_t_wcksusOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_wcksus_reg[${regb_freq0_ch0_dramset1tmg32_t_wcksusOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_wcksus_reg[${regb_freq0_ch0_dramset1tmg32_t_wcksusOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_wcksus_reg[${regb_freq0_ch0_dramset1tmg32_t_wcksusOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_wcksus_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_wcksus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_wcksus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               # Register DRAMSET1TMG32 field ws_off2ws_fs 
               set regb_freq0_ch0_dramset1tmg32_ws_off2ws_fsBaseOffset 16
               set regb_freq0_ch0_dramset1tmg32_ws_off2ws_fsWidth 4

                  if {${regb_freq0_ch0_dramset1tmg32_ws_off2ws_fsWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq0_ch0_dramset1tmg32_ws_off2ws_fsWidth}} {incr bit} {
                        set regb_freq0_ch0_dramset1tmg32_ws_off2ws_fsOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_off2ws_fs_reg[${regb_freq0_ch0_dramset1tmg32_ws_off2ws_fsOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_off2ws_fs_reg[${regb_freq0_ch0_dramset1tmg32_ws_off2ws_fsOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_off2ws_fs_reg[${regb_freq0_ch0_dramset1tmg32_ws_off2ws_fsOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_off2ws_fs_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_off2ws_fs_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ws_off2ws_fs_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
            # Register INITMR1 field emr3 
            set regb_freq0_ch0_initmr1_emr3BaseOffset 0
            set regb_freq0_ch0_initmr1_emr3Width 16

               if {${regb_freq0_ch0_initmr1_emr3Width} > 1} {
                  for {set bit 0} {$bit < ${regb_freq0_ch0_initmr1_emr3Width}} {incr bit} {
                     set regb_freq0_ch0_initmr1_emr3Offset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_emr3_reg[${regb_freq0_ch0_initmr1_emr3Offset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_emr3_reg[${regb_freq0_ch0_initmr1_emr3Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_emr3_reg[${regb_freq0_ch0_initmr1_emr3Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_emr3_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_emr3_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_emr3_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
         # Register DFILPTMG0 field dfi_lp_wakeup_pd 
         set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pdBaseOffset 0
         set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pdWidth 5

            if {${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pdWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pdWidth}} {incr bit} {
                  set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pdOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_pd_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pdOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_pd_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pdOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_pd_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pdOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_pd_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_pd_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_pd_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


         # Register DFILPTMG0 field dfi_lp_wakeup_sr 
         set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_srBaseOffset 8
         set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_srWidth 5

            if {${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_srWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_srWidth}} {incr bit} {
                  set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_srOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_sr_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_srOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_sr_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_srOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_sr_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_srOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_sr_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_sr_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_sr_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }
            # Register DFILPTMG0 field dfi_lp_wakeup_dsm 
            set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsmBaseOffset 16
            set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsmWidth 5

               if {${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsmWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsmWidth}} {incr bit} {
                     set regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsmOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_dsm_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsmOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_dsm_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsmOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_dsm_reg[${regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsmOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_dsm_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_dsm_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_dsm_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }


            # Register DFILPTMG1 field dfi_lp_wakeup_data 
            set regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_dataBaseOffset 0
            set regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_dataWidth 5

               if {${regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_dataWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_dataWidth}} {incr bit} {
                     set regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_dataOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_data_reg[${regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_dataOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_data_reg[${regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_dataOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_data_reg[${regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_dataOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_data_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_data_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_lp_wakeup_data_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
         # Register DFILPTMG1 field dfi_tlp_resp 
         set regb_freq0_ch0_dfilptmg1_dfi_tlp_respBaseOffset 8
         set regb_freq0_ch0_dfilptmg1_dfi_tlp_respWidth 5

            if {${regb_freq0_ch0_dfilptmg1_dfi_tlp_respWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq0_ch0_dfilptmg1_dfi_tlp_respWidth}} {incr bit} {
                  set regb_freq0_ch0_dfilptmg1_dfi_tlp_respOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_tlp_resp_reg[${regb_freq0_ch0_dfilptmg1_dfi_tlp_respOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_tlp_resp_reg[${regb_freq0_ch0_dfilptmg1_dfi_tlp_respOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_tlp_resp_reg[${regb_freq0_ch0_dfilptmg1_dfi_tlp_respOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_tlp_resp_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_tlp_resp_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_tlp_resp_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


         # Register DFIUPDTMG0 field dfi_t_ctrlup_min 
         set regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_minBaseOffset 0
         set regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_minWidth 10

            if {${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_minWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_minWidth}} {incr bit} {
                  set regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_minOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_min_reg[${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_minOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_min_reg[${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_minOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_min_reg[${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_minOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_min_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_min_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_min_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


         # Register DFIUPDTMG0 field dfi_t_ctrlup_max 
         set regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_maxBaseOffset 16
         set regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_maxWidth 10

            if {${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_maxWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_maxWidth}} {incr bit} {
                  set regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_maxOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_max_reg[${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_maxOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_max_reg[${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_maxOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_max_reg[${regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_maxOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_max_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_max_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_dfi_t_ctrlup_max_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }

            # Register DFIUPDTMG2 field ctrlupd_after_dqsosc 
            set regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsoscBaseOffset 27
            set regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth 1

               if {${regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth}} {incr bit} {
                     set regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ctrlupd_after_dqsosc_reg[${regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ctrlupd_after_dqsosc_reg[${regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ctrlupd_after_dqsosc_reg[${regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ctrlupd_after_dqsosc_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ctrlupd_after_dqsosc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ctrlupd_after_dqsosc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register DFIUPDTMG2 field ppt2_override 
            set regb_freq0_ch0_dfiupdtmg2_ppt2_overrideBaseOffset 28
            set regb_freq0_ch0_dfiupdtmg2_ppt2_overrideWidth 1

               if {${regb_freq0_ch0_dfiupdtmg2_ppt2_overrideWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq0_ch0_dfiupdtmg2_ppt2_overrideWidth}} {incr bit} {
                     set regb_freq0_ch0_dfiupdtmg2_ppt2_overrideOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ppt2_override_reg[${regb_freq0_ch0_dfiupdtmg2_ppt2_overrideOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ppt2_override_reg[${regb_freq0_ch0_dfiupdtmg2_ppt2_overrideOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ppt2_override_reg[${regb_freq0_ch0_dfiupdtmg2_ppt2_overrideOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ppt2_override_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ppt2_override_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_ppt2_override_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }

         # Register ZQSET1TMG0 field t_zq_long_nop 
         set regb_freq0_ch0_zqset1tmg0_t_zq_long_nopBaseOffset 0
         set regb_freq0_ch0_zqset1tmg0_t_zq_long_nopWidth 14

            if {${regb_freq0_ch0_zqset1tmg0_t_zq_long_nopWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq0_ch0_zqset1tmg0_t_zq_long_nopWidth}} {incr bit} {
                  set regb_freq0_ch0_zqset1tmg0_t_zq_long_nopOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_long_nop_reg[${regb_freq0_ch0_zqset1tmg0_t_zq_long_nopOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_long_nop_reg[${regb_freq0_ch0_zqset1tmg0_t_zq_long_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_long_nop_reg[${regb_freq0_ch0_zqset1tmg0_t_zq_long_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_long_nop_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_long_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_long_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


         # Register ZQSET1TMG0 field t_zq_short_nop 
         set regb_freq0_ch0_zqset1tmg0_t_zq_short_nopBaseOffset 16
         set regb_freq0_ch0_zqset1tmg0_t_zq_short_nopWidth 10

            if {${regb_freq0_ch0_zqset1tmg0_t_zq_short_nopWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq0_ch0_zqset1tmg0_t_zq_short_nopWidth}} {incr bit} {
                  set regb_freq0_ch0_zqset1tmg0_t_zq_short_nopOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_short_nop_reg[${regb_freq0_ch0_zqset1tmg0_t_zq_short_nopOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_short_nop_reg[${regb_freq0_ch0_zqset1tmg0_t_zq_short_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_short_nop_reg[${regb_freq0_ch0_zqset1tmg0_t_zq_short_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_short_nop_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_short_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_t_zq_short_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }

            # Register TMGCFG field frequency_ratio 
            set regb_freq0_ch0_tmgcfg_frequency_ratioBaseOffset 0
            set regb_freq0_ch0_tmgcfg_frequency_ratioWidth 1

               if {${regb_freq0_ch0_tmgcfg_frequency_ratioWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq0_ch0_tmgcfg_frequency_ratioWidth}} {incr bit} {
                     set regb_freq0_ch0_tmgcfg_frequency_ratioOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_frequency_ratio_reg[${regb_freq0_ch0_tmgcfg_frequency_ratioOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_frequency_ratio_reg[${regb_freq0_ch0_tmgcfg_frequency_ratioOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_frequency_ratio_reg[${regb_freq0_ch0_tmgcfg_frequency_ratioOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_frequency_ratio_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_frequency_ratio_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_frequency_ratio_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register LNKECCCTL0 field wr_link_ecc_enable 
            set regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enableBaseOffset 0
            set regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enableWidth 1

               if {${regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enableWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enableWidth}} {incr bit} {
                     set regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enableOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_wr_link_ecc_enable_reg[${regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enableOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_wr_link_ecc_enable_reg[${regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_wr_link_ecc_enable_reg[${regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_wr_link_ecc_enable_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_wr_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_wr_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register LNKECCCTL0 field rd_link_ecc_enable 
            set regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enableBaseOffset 1
            set regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enableWidth 1

               if {${regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enableWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enableWidth}} {incr bit} {
                     set regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enableOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_rd_link_ecc_enable_reg[${regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enableOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_rd_link_ecc_enable_reg[${regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_rd_link_ecc_enable_reg[${regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_rd_link_ecc_enable_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_rd_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq0_ch0_rd_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
               # Register DRAMSET1TMG32 field ws_fs2wck_sus 
               set regb_freq1_ch0_dramset1tmg32_ws_fs2wck_susBaseOffset 0
               set regb_freq1_ch0_dramset1tmg32_ws_fs2wck_susWidth 4

                  if {${regb_freq1_ch0_dramset1tmg32_ws_fs2wck_susWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq1_ch0_dramset1tmg32_ws_fs2wck_susWidth}} {incr bit} {
                        set regb_freq1_ch0_dramset1tmg32_ws_fs2wck_susOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_fs2wck_sus_reg[${regb_freq1_ch0_dramset1tmg32_ws_fs2wck_susOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_fs2wck_sus_reg[${regb_freq1_ch0_dramset1tmg32_ws_fs2wck_susOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_fs2wck_sus_reg[${regb_freq1_ch0_dramset1tmg32_ws_fs2wck_susOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_fs2wck_sus_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_fs2wck_sus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_fs2wck_sus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               # Register DRAMSET1TMG32 field t_wcksus 
               set regb_freq1_ch0_dramset1tmg32_t_wcksusBaseOffset 8
               set regb_freq1_ch0_dramset1tmg32_t_wcksusWidth 4

                  if {${regb_freq1_ch0_dramset1tmg32_t_wcksusWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq1_ch0_dramset1tmg32_t_wcksusWidth}} {incr bit} {
                        set regb_freq1_ch0_dramset1tmg32_t_wcksusOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_wcksus_reg[${regb_freq1_ch0_dramset1tmg32_t_wcksusOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_wcksus_reg[${regb_freq1_ch0_dramset1tmg32_t_wcksusOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_wcksus_reg[${regb_freq1_ch0_dramset1tmg32_t_wcksusOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_wcksus_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_wcksus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_wcksus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               # Register DRAMSET1TMG32 field ws_off2ws_fs 
               set regb_freq1_ch0_dramset1tmg32_ws_off2ws_fsBaseOffset 16
               set regb_freq1_ch0_dramset1tmg32_ws_off2ws_fsWidth 4

                  if {${regb_freq1_ch0_dramset1tmg32_ws_off2ws_fsWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq1_ch0_dramset1tmg32_ws_off2ws_fsWidth}} {incr bit} {
                        set regb_freq1_ch0_dramset1tmg32_ws_off2ws_fsOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_off2ws_fs_reg[${regb_freq1_ch0_dramset1tmg32_ws_off2ws_fsOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_off2ws_fs_reg[${regb_freq1_ch0_dramset1tmg32_ws_off2ws_fsOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_off2ws_fs_reg[${regb_freq1_ch0_dramset1tmg32_ws_off2ws_fsOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_off2ws_fs_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_off2ws_fs_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ws_off2ws_fs_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
            # Register INITMR1 field emr3 
            set regb_freq1_ch0_initmr1_emr3BaseOffset 0
            set regb_freq1_ch0_initmr1_emr3Width 16

               if {${regb_freq1_ch0_initmr1_emr3Width} > 1} {
                  for {set bit 0} {$bit < ${regb_freq1_ch0_initmr1_emr3Width}} {incr bit} {
                     set regb_freq1_ch0_initmr1_emr3Offset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_emr3_reg[${regb_freq1_ch0_initmr1_emr3Offset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_emr3_reg[${regb_freq1_ch0_initmr1_emr3Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_emr3_reg[${regb_freq1_ch0_initmr1_emr3Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_emr3_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_emr3_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_emr3_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register DFIUPDTMG2 field ctrlupd_after_dqsosc 
            set regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsoscBaseOffset 27
            set regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth 1

               if {${regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth}} {incr bit} {
                     set regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ctrlupd_after_dqsosc_reg[${regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ctrlupd_after_dqsosc_reg[${regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ctrlupd_after_dqsosc_reg[${regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ctrlupd_after_dqsosc_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ctrlupd_after_dqsosc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ctrlupd_after_dqsosc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register DFIUPDTMG2 field ppt2_override 
            set regb_freq1_ch0_dfiupdtmg2_ppt2_overrideBaseOffset 28
            set regb_freq1_ch0_dfiupdtmg2_ppt2_overrideWidth 1

               if {${regb_freq1_ch0_dfiupdtmg2_ppt2_overrideWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq1_ch0_dfiupdtmg2_ppt2_overrideWidth}} {incr bit} {
                     set regb_freq1_ch0_dfiupdtmg2_ppt2_overrideOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ppt2_override_reg[${regb_freq1_ch0_dfiupdtmg2_ppt2_overrideOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ppt2_override_reg[${regb_freq1_ch0_dfiupdtmg2_ppt2_overrideOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ppt2_override_reg[${regb_freq1_ch0_dfiupdtmg2_ppt2_overrideOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ppt2_override_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ppt2_override_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_ppt2_override_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }

         # Register ZQSET1TMG0 field t_zq_long_nop 
         set regb_freq1_ch0_zqset1tmg0_t_zq_long_nopBaseOffset 0
         set regb_freq1_ch0_zqset1tmg0_t_zq_long_nopWidth 14

            if {${regb_freq1_ch0_zqset1tmg0_t_zq_long_nopWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq1_ch0_zqset1tmg0_t_zq_long_nopWidth}} {incr bit} {
                  set regb_freq1_ch0_zqset1tmg0_t_zq_long_nopOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_long_nop_reg[${regb_freq1_ch0_zqset1tmg0_t_zq_long_nopOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_long_nop_reg[${regb_freq1_ch0_zqset1tmg0_t_zq_long_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_long_nop_reg[${regb_freq1_ch0_zqset1tmg0_t_zq_long_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_long_nop_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_long_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_long_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


         # Register ZQSET1TMG0 field t_zq_short_nop 
         set regb_freq1_ch0_zqset1tmg0_t_zq_short_nopBaseOffset 16
         set regb_freq1_ch0_zqset1tmg0_t_zq_short_nopWidth 10

            if {${regb_freq1_ch0_zqset1tmg0_t_zq_short_nopWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq1_ch0_zqset1tmg0_t_zq_short_nopWidth}} {incr bit} {
                  set regb_freq1_ch0_zqset1tmg0_t_zq_short_nopOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_short_nop_reg[${regb_freq1_ch0_zqset1tmg0_t_zq_short_nopOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_short_nop_reg[${regb_freq1_ch0_zqset1tmg0_t_zq_short_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_short_nop_reg[${regb_freq1_ch0_zqset1tmg0_t_zq_short_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_short_nop_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_short_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_t_zq_short_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }

            # Register TMGCFG field frequency_ratio 
            set regb_freq1_ch0_tmgcfg_frequency_ratioBaseOffset 0
            set regb_freq1_ch0_tmgcfg_frequency_ratioWidth 1

               if {${regb_freq1_ch0_tmgcfg_frequency_ratioWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq1_ch0_tmgcfg_frequency_ratioWidth}} {incr bit} {
                     set regb_freq1_ch0_tmgcfg_frequency_ratioOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_frequency_ratio_reg[${regb_freq1_ch0_tmgcfg_frequency_ratioOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_frequency_ratio_reg[${regb_freq1_ch0_tmgcfg_frequency_ratioOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_frequency_ratio_reg[${regb_freq1_ch0_tmgcfg_frequency_ratioOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_frequency_ratio_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_frequency_ratio_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_frequency_ratio_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register LNKECCCTL0 field wr_link_ecc_enable 
            set regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enableBaseOffset 0
            set regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enableWidth 1

               if {${regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enableWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enableWidth}} {incr bit} {
                     set regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enableOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_wr_link_ecc_enable_reg[${regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enableOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_wr_link_ecc_enable_reg[${regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_wr_link_ecc_enable_reg[${regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_wr_link_ecc_enable_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_wr_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_wr_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register LNKECCCTL0 field rd_link_ecc_enable 
            set regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enableBaseOffset 1
            set regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enableWidth 1

               if {${regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enableWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enableWidth}} {incr bit} {
                     set regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enableOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_rd_link_ecc_enable_reg[${regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enableOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_rd_link_ecc_enable_reg[${regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_rd_link_ecc_enable_reg[${regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_rd_link_ecc_enable_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_rd_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq1_ch0_rd_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
               # Register DRAMSET1TMG32 field ws_fs2wck_sus 
               set regb_freq2_ch0_dramset1tmg32_ws_fs2wck_susBaseOffset 0
               set regb_freq2_ch0_dramset1tmg32_ws_fs2wck_susWidth 4

                  if {${regb_freq2_ch0_dramset1tmg32_ws_fs2wck_susWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq2_ch0_dramset1tmg32_ws_fs2wck_susWidth}} {incr bit} {
                        set regb_freq2_ch0_dramset1tmg32_ws_fs2wck_susOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_fs2wck_sus_reg[${regb_freq2_ch0_dramset1tmg32_ws_fs2wck_susOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_fs2wck_sus_reg[${regb_freq2_ch0_dramset1tmg32_ws_fs2wck_susOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_fs2wck_sus_reg[${regb_freq2_ch0_dramset1tmg32_ws_fs2wck_susOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_fs2wck_sus_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_fs2wck_sus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_fs2wck_sus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               # Register DRAMSET1TMG32 field t_wcksus 
               set regb_freq2_ch0_dramset1tmg32_t_wcksusBaseOffset 8
               set regb_freq2_ch0_dramset1tmg32_t_wcksusWidth 4

                  if {${regb_freq2_ch0_dramset1tmg32_t_wcksusWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq2_ch0_dramset1tmg32_t_wcksusWidth}} {incr bit} {
                        set regb_freq2_ch0_dramset1tmg32_t_wcksusOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_wcksus_reg[${regb_freq2_ch0_dramset1tmg32_t_wcksusOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_wcksus_reg[${regb_freq2_ch0_dramset1tmg32_t_wcksusOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_wcksus_reg[${regb_freq2_ch0_dramset1tmg32_t_wcksusOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_wcksus_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_wcksus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_wcksus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               # Register DRAMSET1TMG32 field ws_off2ws_fs 
               set regb_freq2_ch0_dramset1tmg32_ws_off2ws_fsBaseOffset 16
               set regb_freq2_ch0_dramset1tmg32_ws_off2ws_fsWidth 4

                  if {${regb_freq2_ch0_dramset1tmg32_ws_off2ws_fsWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq2_ch0_dramset1tmg32_ws_off2ws_fsWidth}} {incr bit} {
                        set regb_freq2_ch0_dramset1tmg32_ws_off2ws_fsOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_off2ws_fs_reg[${regb_freq2_ch0_dramset1tmg32_ws_off2ws_fsOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_off2ws_fs_reg[${regb_freq2_ch0_dramset1tmg32_ws_off2ws_fsOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_off2ws_fs_reg[${regb_freq2_ch0_dramset1tmg32_ws_off2ws_fsOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_off2ws_fs_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_off2ws_fs_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ws_off2ws_fs_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
            # Register INITMR1 field emr3 
            set regb_freq2_ch0_initmr1_emr3BaseOffset 0
            set regb_freq2_ch0_initmr1_emr3Width 16

               if {${regb_freq2_ch0_initmr1_emr3Width} > 1} {
                  for {set bit 0} {$bit < ${regb_freq2_ch0_initmr1_emr3Width}} {incr bit} {
                     set regb_freq2_ch0_initmr1_emr3Offset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_emr3_reg[${regb_freq2_ch0_initmr1_emr3Offset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_emr3_reg[${regb_freq2_ch0_initmr1_emr3Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_emr3_reg[${regb_freq2_ch0_initmr1_emr3Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_emr3_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_emr3_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_emr3_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register DFIUPDTMG2 field ctrlupd_after_dqsosc 
            set regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsoscBaseOffset 27
            set regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth 1

               if {${regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth}} {incr bit} {
                     set regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ctrlupd_after_dqsosc_reg[${regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ctrlupd_after_dqsosc_reg[${regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ctrlupd_after_dqsosc_reg[${regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ctrlupd_after_dqsosc_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ctrlupd_after_dqsosc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ctrlupd_after_dqsosc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register DFIUPDTMG2 field ppt2_override 
            set regb_freq2_ch0_dfiupdtmg2_ppt2_overrideBaseOffset 28
            set regb_freq2_ch0_dfiupdtmg2_ppt2_overrideWidth 1

               if {${regb_freq2_ch0_dfiupdtmg2_ppt2_overrideWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq2_ch0_dfiupdtmg2_ppt2_overrideWidth}} {incr bit} {
                     set regb_freq2_ch0_dfiupdtmg2_ppt2_overrideOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ppt2_override_reg[${regb_freq2_ch0_dfiupdtmg2_ppt2_overrideOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ppt2_override_reg[${regb_freq2_ch0_dfiupdtmg2_ppt2_overrideOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ppt2_override_reg[${regb_freq2_ch0_dfiupdtmg2_ppt2_overrideOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ppt2_override_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ppt2_override_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_ppt2_override_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }

         # Register ZQSET1TMG0 field t_zq_long_nop 
         set regb_freq2_ch0_zqset1tmg0_t_zq_long_nopBaseOffset 0
         set regb_freq2_ch0_zqset1tmg0_t_zq_long_nopWidth 14

            if {${regb_freq2_ch0_zqset1tmg0_t_zq_long_nopWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq2_ch0_zqset1tmg0_t_zq_long_nopWidth}} {incr bit} {
                  set regb_freq2_ch0_zqset1tmg0_t_zq_long_nopOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_long_nop_reg[${regb_freq2_ch0_zqset1tmg0_t_zq_long_nopOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_long_nop_reg[${regb_freq2_ch0_zqset1tmg0_t_zq_long_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_long_nop_reg[${regb_freq2_ch0_zqset1tmg0_t_zq_long_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_long_nop_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_long_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_long_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


         # Register ZQSET1TMG0 field t_zq_short_nop 
         set regb_freq2_ch0_zqset1tmg0_t_zq_short_nopBaseOffset 16
         set regb_freq2_ch0_zqset1tmg0_t_zq_short_nopWidth 10

            if {${regb_freq2_ch0_zqset1tmg0_t_zq_short_nopWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq2_ch0_zqset1tmg0_t_zq_short_nopWidth}} {incr bit} {
                  set regb_freq2_ch0_zqset1tmg0_t_zq_short_nopOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_short_nop_reg[${regb_freq2_ch0_zqset1tmg0_t_zq_short_nopOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_short_nop_reg[${regb_freq2_ch0_zqset1tmg0_t_zq_short_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_short_nop_reg[${regb_freq2_ch0_zqset1tmg0_t_zq_short_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_short_nop_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_short_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_t_zq_short_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }

            # Register TMGCFG field frequency_ratio 
            set regb_freq2_ch0_tmgcfg_frequency_ratioBaseOffset 0
            set regb_freq2_ch0_tmgcfg_frequency_ratioWidth 1

               if {${regb_freq2_ch0_tmgcfg_frequency_ratioWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq2_ch0_tmgcfg_frequency_ratioWidth}} {incr bit} {
                     set regb_freq2_ch0_tmgcfg_frequency_ratioOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_frequency_ratio_reg[${regb_freq2_ch0_tmgcfg_frequency_ratioOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_frequency_ratio_reg[${regb_freq2_ch0_tmgcfg_frequency_ratioOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_frequency_ratio_reg[${regb_freq2_ch0_tmgcfg_frequency_ratioOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_frequency_ratio_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_frequency_ratio_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_frequency_ratio_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register LNKECCCTL0 field wr_link_ecc_enable 
            set regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enableBaseOffset 0
            set regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enableWidth 1

               if {${regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enableWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enableWidth}} {incr bit} {
                     set regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enableOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_wr_link_ecc_enable_reg[${regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enableOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_wr_link_ecc_enable_reg[${regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_wr_link_ecc_enable_reg[${regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_wr_link_ecc_enable_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_wr_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_wr_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register LNKECCCTL0 field rd_link_ecc_enable 
            set regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enableBaseOffset 1
            set regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enableWidth 1

               if {${regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enableWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enableWidth}} {incr bit} {
                     set regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enableOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_rd_link_ecc_enable_reg[${regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enableOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_rd_link_ecc_enable_reg[${regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_rd_link_ecc_enable_reg[${regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_rd_link_ecc_enable_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_rd_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq2_ch0_rd_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
               # Register DRAMSET1TMG32 field ws_fs2wck_sus 
               set regb_freq3_ch0_dramset1tmg32_ws_fs2wck_susBaseOffset 0
               set regb_freq3_ch0_dramset1tmg32_ws_fs2wck_susWidth 4

                  if {${regb_freq3_ch0_dramset1tmg32_ws_fs2wck_susWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq3_ch0_dramset1tmg32_ws_fs2wck_susWidth}} {incr bit} {
                        set regb_freq3_ch0_dramset1tmg32_ws_fs2wck_susOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_fs2wck_sus_reg[${regb_freq3_ch0_dramset1tmg32_ws_fs2wck_susOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_fs2wck_sus_reg[${regb_freq3_ch0_dramset1tmg32_ws_fs2wck_susOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_fs2wck_sus_reg[${regb_freq3_ch0_dramset1tmg32_ws_fs2wck_susOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_fs2wck_sus_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_fs2wck_sus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_fs2wck_sus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               # Register DRAMSET1TMG32 field t_wcksus 
               set regb_freq3_ch0_dramset1tmg32_t_wcksusBaseOffset 8
               set regb_freq3_ch0_dramset1tmg32_t_wcksusWidth 4

                  if {${regb_freq3_ch0_dramset1tmg32_t_wcksusWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq3_ch0_dramset1tmg32_t_wcksusWidth}} {incr bit} {
                        set regb_freq3_ch0_dramset1tmg32_t_wcksusOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_wcksus_reg[${regb_freq3_ch0_dramset1tmg32_t_wcksusOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_wcksus_reg[${regb_freq3_ch0_dramset1tmg32_t_wcksusOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_wcksus_reg[${regb_freq3_ch0_dramset1tmg32_t_wcksusOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_wcksus_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_wcksus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_wcksus_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               # Register DRAMSET1TMG32 field ws_off2ws_fs 
               set regb_freq3_ch0_dramset1tmg32_ws_off2ws_fsBaseOffset 16
               set regb_freq3_ch0_dramset1tmg32_ws_off2ws_fsWidth 4

                  if {${regb_freq3_ch0_dramset1tmg32_ws_off2ws_fsWidth} > 1} {
                     for {set bit 0} {$bit < ${regb_freq3_ch0_dramset1tmg32_ws_off2ws_fsWidth}} {incr bit} {
                        set regb_freq3_ch0_dramset1tmg32_ws_off2ws_fsOffset $bit
                        if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_off2ws_fs_reg[${regb_freq3_ch0_dramset1tmg32_ws_off2ws_fsOffset}]]] } {
                           set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_off2ws_fs_reg[${regb_freq3_ch0_dramset1tmg32_ws_off2ws_fsOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                           set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_off2ws_fs_reg[${regb_freq3_ch0_dramset1tmg32_ws_off2ws_fsOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        }
                     }
                  } else {
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_off2ws_fs_reg*]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_off2ws_fs_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ws_off2ws_fs_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
            # Register INITMR1 field emr3 
            set regb_freq3_ch0_initmr1_emr3BaseOffset 0
            set regb_freq3_ch0_initmr1_emr3Width 16

               if {${regb_freq3_ch0_initmr1_emr3Width} > 1} {
                  for {set bit 0} {$bit < ${regb_freq3_ch0_initmr1_emr3Width}} {incr bit} {
                     set regb_freq3_ch0_initmr1_emr3Offset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_emr3_reg[${regb_freq3_ch0_initmr1_emr3Offset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_emr3_reg[${regb_freq3_ch0_initmr1_emr3Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_emr3_reg[${regb_freq3_ch0_initmr1_emr3Offset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_emr3_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_emr3_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_emr3_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register DFIUPDTMG2 field ctrlupd_after_dqsosc 
            set regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsoscBaseOffset 27
            set regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth 1

               if {${regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsoscWidth}} {incr bit} {
                     set regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ctrlupd_after_dqsosc_reg[${regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ctrlupd_after_dqsosc_reg[${regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ctrlupd_after_dqsosc_reg[${regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsoscOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ctrlupd_after_dqsosc_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ctrlupd_after_dqsosc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ctrlupd_after_dqsosc_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register DFIUPDTMG2 field ppt2_override 
            set regb_freq3_ch0_dfiupdtmg2_ppt2_overrideBaseOffset 28
            set regb_freq3_ch0_dfiupdtmg2_ppt2_overrideWidth 1

               if {${regb_freq3_ch0_dfiupdtmg2_ppt2_overrideWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq3_ch0_dfiupdtmg2_ppt2_overrideWidth}} {incr bit} {
                     set regb_freq3_ch0_dfiupdtmg2_ppt2_overrideOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ppt2_override_reg[${regb_freq3_ch0_dfiupdtmg2_ppt2_overrideOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ppt2_override_reg[${regb_freq3_ch0_dfiupdtmg2_ppt2_overrideOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ppt2_override_reg[${regb_freq3_ch0_dfiupdtmg2_ppt2_overrideOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ppt2_override_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ppt2_override_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_ppt2_override_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }

         # Register ZQSET1TMG0 field t_zq_long_nop 
         set regb_freq3_ch0_zqset1tmg0_t_zq_long_nopBaseOffset 0
         set regb_freq3_ch0_zqset1tmg0_t_zq_long_nopWidth 14

            if {${regb_freq3_ch0_zqset1tmg0_t_zq_long_nopWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq3_ch0_zqset1tmg0_t_zq_long_nopWidth}} {incr bit} {
                  set regb_freq3_ch0_zqset1tmg0_t_zq_long_nopOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_long_nop_reg[${regb_freq3_ch0_zqset1tmg0_t_zq_long_nopOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_long_nop_reg[${regb_freq3_ch0_zqset1tmg0_t_zq_long_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_long_nop_reg[${regb_freq3_ch0_zqset1tmg0_t_zq_long_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_long_nop_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_long_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_long_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }


         # Register ZQSET1TMG0 field t_zq_short_nop 
         set regb_freq3_ch0_zqset1tmg0_t_zq_short_nopBaseOffset 16
         set regb_freq3_ch0_zqset1tmg0_t_zq_short_nopWidth 10

            if {${regb_freq3_ch0_zqset1tmg0_t_zq_short_nopWidth} > 1} {
               for {set bit 0} {$bit < ${regb_freq3_ch0_zqset1tmg0_t_zq_short_nopWidth}} {incr bit} {
                  set regb_freq3_ch0_zqset1tmg0_t_zq_short_nopOffset $bit
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_short_nop_reg[${regb_freq3_ch0_zqset1tmg0_t_zq_short_nopOffset}]]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_short_nop_reg[${regb_freq3_ch0_zqset1tmg0_t_zq_short_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_short_nop_reg[${regb_freq3_ch0_zqset1tmg0_t_zq_short_nopOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            } else {
               if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_short_nop_reg*]] } {
                  set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_short_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_t_zq_short_nop_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
               }
            }

            # Register TMGCFG field frequency_ratio 
            set regb_freq3_ch0_tmgcfg_frequency_ratioBaseOffset 0
            set regb_freq3_ch0_tmgcfg_frequency_ratioWidth 1

               if {${regb_freq3_ch0_tmgcfg_frequency_ratioWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq3_ch0_tmgcfg_frequency_ratioWidth}} {incr bit} {
                     set regb_freq3_ch0_tmgcfg_frequency_ratioOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_frequency_ratio_reg[${regb_freq3_ch0_tmgcfg_frequency_ratioOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_frequency_ratio_reg[${regb_freq3_ch0_tmgcfg_frequency_ratioOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_frequency_ratio_reg[${regb_freq3_ch0_tmgcfg_frequency_ratioOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_frequency_ratio_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_frequency_ratio_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_frequency_ratio_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register LNKECCCTL0 field wr_link_ecc_enable 
            set regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enableBaseOffset 0
            set regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enableWidth 1

               if {${regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enableWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enableWidth}} {incr bit} {
                     set regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enableOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_wr_link_ecc_enable_reg[${regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enableOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_wr_link_ecc_enable_reg[${regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_wr_link_ecc_enable_reg[${regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_wr_link_ecc_enable_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_wr_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_wr_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }
            # Register LNKECCCTL0 field rd_link_ecc_enable 
            set regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enableBaseOffset 1
            set regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enableWidth 1

               if {${regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enableWidth} > 1} {
                  for {set bit 0} {$bit < ${regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enableWidth}} {incr bit} {
                     set regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enableOffset $bit
                     if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_rd_link_ecc_enable_reg[${regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enableOffset}]]] } {
                        set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_rd_link_ecc_enable_reg[${regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                        set_multicycle_path 1 -hold   -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_rd_link_ecc_enable_reg[${regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enableOffset}] -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     }
                  }
               } else {
                  if { [sizeof_collection [get_cells -quiet ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_rd_link_ecc_enable_reg*]] } {
                     set_multicycle_path 2 -setup -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_rd_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                     set_multicycle_path 1 -hold -from ${_sDWC_ddrctl_hierarchy}U_apb_slvtop/slvif/ff_regb_freq3_ch0_rd_link_ecc_enable_reg* -comment {Specify multi-cycle path of control register output synchronous to PCLK}
                  }
               }



set _sDWC_ddrctl_hierarchy ""
if {[info exists ::env(sDWC_ddrctl_hierarchy)]} {
set _sDWC_ddrctl_hierarchy  $::env(sDWC_ddrctl_hierarchy)
}


