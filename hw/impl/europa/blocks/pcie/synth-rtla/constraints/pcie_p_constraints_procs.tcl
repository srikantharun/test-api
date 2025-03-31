############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_con_procs.tcl
#
# PIPE(UPCS+PHY) synthesis all procedure definitions
#
# ----------------------------------------------------------------------
# Copyright 2023 Synopsys, Inc.
#
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Read the Synopsys Statement on Inclusivity and Diversity at
# https://solvnetplus.synopsys.com/s/article/Synopsys-Statement-on-Inclusivity-and-Diversity
# ----------------------------------------------------------------------
#
#############################################################################################

####################################################
############ dwc_c20pcie4_upcs_x4_ns_con_procs.tcl ####################
##
## This file consists of the definitions of custom
## Tcl procedures that are used by upcs constraint tcl file
#####################################################
# Proc to convert frequency in period
proc freq2per {f} {
 global FREQ_MARGIN
 global TUNIT
 # default unit for TUNIT and per is ns, for freq is MHz. So with times 1000.
 return [expr {(1000.0*$TUNIT) /($f * $FREQ_MARGIN)}]
}

## Proc for prefixing Hierarchies
proc prefixing  { hiervar pinname } {
 set pinname $pinname
 set hiervar $hiervar
 set hierpinname ${hiervar}$pinname
 regsub ^/  $hierpinname "" hierpinname
 return $hierpinname
}

## max_pclk_int edges are set based on input max_pclk_div_ratio or pipe_width
if { $PMA_NAME == "c20" || $PMA_NAME == "c40" } {
 proc max_pclk_final_div {prot div_ratio pipe_width} {
  set prot $prot
  set div_ratio $div_ratio
  set pipe_width $pipe_width
  if {$prot == "usb4" || $prot == "dp20" || $prot == "pcie4_g4" || $prot =="usb4_g4" || $prot == "usb3_g2_nom" } {
   if {($pipe_width != 0)} {
    if {$div_ratio == 0 } {
     if {($pipe_width == 8) || ($pipe_width == 10)} {
      #return 1
      echo "Error MSG - Pipe Width 8b or 10b not supported for USB4, TBT3, DP20 data rates"
      exit
     } elseif {($pipe_width == 16) || ($pipe_width == 20)} {
      return 1
     } elseif {($pipe_width == 28)} {
      return 1
     } else {
      return 2
     }
    } else {
     return $div_ratio
    }
   } else {  ;#If pipe_width=0, max_pclk_div_ratio to be set internally zero
    return 0
   }
  } else {  ;#for other prots
   if {($pipe_width != 0)} {
    if { $div_ratio == 0 } {
     if {($pipe_width == 8) || ($pipe_width == 10)} {
      return 1
     } elseif {($pipe_width == 16) || ($pipe_width == 20)} {
      return 2
     } else {
      return 4
     }
    } else {
     return $div_ratio
    }
   } else {  ;#If pipe_width=0, max_pclk_div_ratio to be set internally zero
    return 0
   }
  }  ;#end of prot condition
 };#proc end
}


# proc is_port <obj>
#   Checks if a port(s) exists or not
#   Arguments:
#     <obj> - Name of the port
#
proc is_port {ports} {
 return [sizeof_collection [get_ports -quiet $ports]]
}
# End of is_port

# proc get_driver_cell_pin <hier_obj>
#   Returns the leaf cell pin that drives a particular hierarchical pin
#   Arguments:
#     <hier_obj> - Hierarchical pin of interest
#
proc get_driver_cell_pin {hier_obj} {
 set hier_pin [get_pins $hier_obj]
 if { [sizeof_collection $hier_pin] == 0} {
  puts "get_driver_cell_pin: Error: Hierarchical pin argument missing"
  return
 }
 set net [get_nets -of_objects $hier_pin]
 set driver_cell_pin [get_pins -of_objects $net -leaf -filter "pin_direction==out"]
 return $driver_cell_pin
}
# End of get_driver_cell_pin

# proc add_clock_group <clk_groups_var> <clk_objects>
#   Creates a new clock group with the <clk_objects> and appends the group
#   to the set_clock_groups command string <clk_groups_var>
#   Arguments:
#     <clk_groups_var> - set_clock_groups command string
#     <clk_objects>    - clocks that need to be included in the new group
#
proc add_clock_group {clk_groups_var clk_objects} {
 upvar 1 $clk_groups_var my_clk_grps
 set my_clk_grps "$my_clk_grps -group \[get_clocks \[list [get_object_name $clk_objects]\]\]"
}
# End of add_clock_group

# proc all_input_clock_ports
#   Returns a collection of input ports on which clocks are defined
#   Arguments: none
#
proc all_input_clock_ports {} {
 set clocks [all_clocks]
 set clock_sources [get_attribute $clocks sources]
 set input_clock_ports [filter_collection $clock_sources "object_class==port"]
 return $input_clock_ports
}
# End of all_input_clock_ports

# proc all_output_clock_ports
#   Returns a collection of output ports on which clocks are defined
#   Arguments: none
#
proc all_output_clock_ports {} {
 set port_dir_attr "pin_direction"
 set clocks [all_clocks]
 set clock_network_pins [get_attribute $clocks clock_network_pins]
 set output_clock_ports [filter_collection $clock_network_pins "object_class==port && ${port_dir_attr}==out"]
 return $output_clock_ports
}
# End of all_output_clock_ports

proc check_uncertainty_all_clock {} {
 set clocks [all_clocks]
 foreach_in_collection ck $clocks {
  set setup_unc [get_attribute [get_clocks $ck] setup_uncertainty]
  echo [get_object_name $ck] $setup_unc
 }
}
# End of all_input_clock_ports



# proc get_weak_buffer_cell
#   Returns the name of a weak buffer cell available in the libraries for
#   using it as the driving cell of input ports
#   Arguments: none
#
proc get_weak_buffer_cell {} {
 set buff_cells {}
 foreach_in_collection lib [remove_from_collection [get_libs] [get_libs -quiet "gtech standard.sldb"] ] {
  set libname    [get_object_name $lib]
  set buff_cells [add_to_collection $buff_cells \
                      [get_lib_cells $libname/* \
                           -filter "function_id==a1.0" \
                           -quiet ]]
 }
 # After sorting the list of buffers in ascending order, the first element
 # in the sorted list will be a weak buffer
 set buff_cells       [sort_collection -dictionary $buff_cells full_name]
 set driving_cell     [lindex [get_object_name $buff_cells] 0]
 if { $driving_cell != ""} {
  set driving_cell [lindex [split $driving_cell /] 1]
  return $driving_cell
 }
}
# End of get_weak_buffer_cell

# proc get_lib_cell_out_pin <lib_cell>
#   Returns the output pin of the library cell <lib_cell>
#   Arguments:
#     <lib_cell> - Name of the library cell
#
proc get_lib_cell_out_pin {lib_cell} {
 if { [llength [split $lib_cell /]] == 1 } {
  foreach_in_collection lib [remove_from_collection [get_libs] [get_libs -quiet "gtech standard.sldb"] ] {
   set libname    [get_object_name $lib]
   set cell       [get_object_name [get_lib_cells $libname/$lib_cell -quiet]]
   if { $cell != "" } {
    break
   }
  }
  if { $cell == "" } {
   puts "Error: get_lib_cell_out_pin: Lib cell $lib_cell not found."
   return
  }
  set lib_cell $cell
 }
 set name_attr name
 set cell_out_pin [get_attribute [get_lib_pins ${lib_cell}/* -filter "pin_direction==out"] $name_attr]
 return $cell_out_pin
}
# End of get_lib_cell_out_pin

# proc get_load <net_name>
#   Return the last input (the first indexes are further away from the net)
#   Arguments:
#     <net_name> - Name of the net
#
proc get_load {net} {
 global DC_SHELL
 global ICC_SHELL
 if { ($DC_SHELL || $ICC_SHELL) } {
  set outputs [filter_collection [all_fanout -levels 1 -flat -from $net] "pin_direction == in"]
  return [index_collection $outputs 0]
 } else {
  set outputs [filter_collection [all_fanout -levels 2 -flat -from $net] "pin_direction == in"]
  if { [sizeof_collection $outputs] > 1 } {
   return [index_collection $outputs 1]
  } else {
   return
  }
 }
}
# End of get_load

##Proc for clock uncertainity
## proc duty <cka> <ckb> <mar>
#   Set duty cycle uncertainty to between <cka> and <ckb>
#   Arguments:
#       <cka> - Name of clock A
#       <ckb> - Name of clock B
#       <mar> - Uncertainty margin. This margin will addup with gloab setup/hold uncertainty
#               UNC_SUP/HLD to get the final interclock duty cycle uncertainty.
#
proc duty {cka ckb mar} {
 global UNC_SUP
 global UNC_HLD
 set sm [expr {$UNC_SUP + $mar}]
 set hm [expr {$UNC_HLD + $mar}]
 set ca [get_clocks $cka]
 set cb [get_clocks $ckb]

 set_clock_uncertainty -setup $sm -rise_from $ca -fall_to $cb
 set_clock_uncertainty -setup $sm -fall_from $ca -rise_to $cb
 set_clock_uncertainty -hold  $hm -rise_from $ca -fall_to $cb
 set_clock_uncertainty -hold  $hm -fall_from $ca -rise_to $cb
}
# End of duty

################################
# Clock uncertainties
################################

# proc clock_uncertainty <nameCK> <uncSU> [<uncHD> [<uncDC>]]
#   SDS clock uncertainty setting proc.
#       - set clock uncertainty
#       - set duty cycle uncertainty
#   Arguments:
#       <nameCK> - name of clock
#       <uncSU>  - Setup uncertainty
#       <uncHD>  - Optional, Default: 0.000, Hold uncertainty
#       <uncDC>  - Optional, Default: 0.000, Duty cycle uncertainty increment. Total duty cycle
#                  uncertainty would be <uncDC> + <uncSU>/<uncHD>



#####################################################################################################################################################################
# proc set_clk_unc_phy_info <clkName> <freq> [<clock_jitter>] [<dcu_margin>] [<uncHD>]
# Calculate clock uncertainty and duty-cycle distortion, set clock uncertainty and dcu
#       -   set phy_clks_info and phy_clks information
#   Arguments:
#       <clkName>       -   name of clock
#       <freq>          -   clock frequency, unit: MHz
#       <clock_jitter>  -   clock jitter value, unit: ns , default value is 0 ns
#       <dcu_margin>    -   duty-cycle margin factor , default value is 0.10
#       <uncHD>         -   clock hold uncertainty, unit: ns , default value is 0.05 ns
#
proc safe_set { varName varTarget {default 0} } {
 uplevel \
     "if { \[info exists $varTarget\] } {
            set $varName \"$$varTarget\"
         } else {
            set $varName \"$default\"
         }"
}
proc set_clk_unc_info {clkName {clock_jitter 0.000} {dcu_margin 0.10} {uncHD 0.05}} {
    variable SUP_UNC_MARGIN
    variable SUP_UNC_MAX
    variable unc_set_clocks_info
    variable unc_set_name_clks
    variable dCDRDriftRXClocksTable
    global period
    global EXTRA_SETUP_UNC
    global EXTRA_HOLD_UNC
    set clk [get_object_name $clkName]
    set clk_period  $period($clk)
    set uncSU_Margin [expr { $SUP_UNC_MARGIN * $clk_period}]
    set uncSU [expr { $clock_jitter + (( $uncSU_Margin > $SUP_UNC_MAX) ? $SUP_UNC_MAX : $uncSU_Margin)}]
    set dcu   [expr { $dcu_margin * $clk_period}]
    if { [dict exists $dCDRDriftRXClocksTable $clk] } {
        set drift_margin [dict get $dCDRDriftRXClocksTable $clk]
        set uncSU [expr { $uncSU_Margin + ($clk_period * $drift_margin)}]
        puts " INFO : Add $drift_margin * $clk_period clock CDR Drift"
    } else {
        set drift_margin "NA"
    } 

    set uncSU [expr {$uncSU + $EXTRA_SETUP_UNC}]
    set uncHD [expr {$uncHD + $EXTRA_HOLD_UNC}]

    clock_uncertainty $clkName $uncSU $uncHD $dcu
    set unc_set_clocks_info($clkName) [list $clk_period $uncSU $uncHD $dcu]
    append_to_collection unc_set_name_clks [get_clocks $clkName]
    puts "INFO: [format "set clock uncertainty for %-50s setup: %10f hold: %10f \t dcu: %10f" $clk \
        $uncSU $uncHD $dcu]"
    puts "DATABOOK_INFO: [format "Uncertainity_Variables_Info_for --> %-50s Period: %10f Clock_Jitter: %10f  Uncertainity_Margin: %10f DCU_Margin_percentage: %10f dcu: %10f CDR: %10s Total_Setup_uncertainity: %10f hold: %10f" $clk \
           $clk_period $clock_jitter  $uncSU_Margin [expr {$dcu_margin*100}] $dcu $drift_margin $uncSU $uncHD]"

}

# proc clock_uncertainty <nameCK> <uncSU> [<uncHD> [<uncDC>]]
#   SDS_PHY clock uncertainty setting proc.
#       - set clock uncertainty
#       - set duty cycle uncertainty
#   Arguments:
#       <nameCK> - name of clock
#       <uncSU>  - Setup uncertainty
#       <uncHD>  - Optional, Default: 0.000, Hold uncertainty
#       <uncDC>  - Optional, Default: 0.000, Duty cycle uncertainty increment. Total duty cycle
#                  uncertainty would be <uncDC> + <uncSU>/<uncHD>
#
proc clock_uncertainty {nameCK uncSU {uncHD 0.000} {uncDC 0.000} } {
    variable TUNIT
    set cks [get_clocks $nameCK]
    # rise2rise only
    set sm [expr {$uncSU*$TUNIT}]
    set hm [expr {$uncHD*$TUNIT}]
    set_clock_uncertainty -setup $uncSU $cks
    set_clock_uncertainty -hold  $uncHD $cks

    # Skip duty cycle uncertainty if not required.
    if { $uncDC == 0 } {
        return 0
    }

    # Duty Cycle Uncertainty
    set sm [expr {($uncSU + $uncDC)*$TUNIT}]
    set hm [expr {($uncHD + $uncDC)*$TUNIT}]
    foreach_in_collection ck $cks {
        set_clock_uncertainty -setup $sm -rise_from $ck -fall_to $ck
        set_clock_uncertainty -setup $sm -fall_from $ck -rise_to $ck
        set_clock_uncertainty -hold  $hm -rise_from $ck -fall_to $ck
        set_clock_uncertainty -hold  $hm -fall_from $ck -rise_to $ck
    }
}
# End of clock_uncertainty
## proc to remove hierarchy from the name of pin/cell and
# proc remove_pin_hier <pin_name>
#   Return the last pin name (Removes the complete hierarchy)
#   Arguments:
#     <pin/port_name> - Name of the pin
#
proc remove_hier {pin} {
 set pin [get_object_name $pin]
 #puts "pin is : $pin"
 if {[regexp "/" $pin]} {
  return [string range $pin [expr [string last "/" $pin] + 1] [string length $pin]]
 } else {
  return $pin
 }
}
# End of remove_hier

## proc to get hierarchy cell from the name of pin/cell and
# proc get_pin_hier <pin_name>
#   Return the last pin name (Removes the complete hierarchy)
#   Arguments:
#     <pin/port_name> - Name of the pin
#
proc get_pin_hier {pin} {
 set pin [get_object_name $pin]
 #puts "pin is : $pin"
 if {[regexp "/" $pin]} {
  return \
      [string range $pin 0 [expr [string last "/" $pin] - 1]]
 } else {
  return $pin
 }
}
# End of get_pin_hier

## proc - Conversion from a collection to a list
#   Return the list
#   Arguments:
#     Collection to be passed
#
proc collection2list {a_collection} {
 set object_list {}
 foreach_in_collection a_object $a_collection {
  lappend object_list [get_attribute $a_object full_name]
 }
 return $object_list
}

proc get_bitblasted_signal {sig_name bit_blast_en} {
 if {$bit_blast_en} {
  set sig_name [string toupper $sig_name]
  regsub -all "_"  $sig_name "" sig_name
  return $sig_name
 } else {
  return $sig_name
 }
}

# check scan reset: in scan mode, all DFFs should be reset by scan_set_rst only
proc check_scan_reset {} {
 set_case_analysis 1 *_scan_mode
 set port_otm [filter_collection -regexp [all_inputs] \
                   {full_name =~ "bs_ce|test_burnin|scan_pma_occ_en"}]
 set_case_analysis 0 $port_otm
 set cellReg [all_registers -edge_triggered]
 set cellReg [filter_collection $cellReg "full_name !~ phy*/pma"]
 foreach_in_collection cr $cellReg {
  set nCr [get_object_name $cr]
  set pa [get_pins -of $cr -filter "is_async_pin==true"]
  set pr [filter_collection $pa "undefined(constant_value)"]
  if {![sizeof_collection $pr ]} {
   echo "*** Error: DFF $nCr without valid reset"
   continue
  }

  set fin [all_fanin -to $pr -startpoints_only -flat]
  append_to_collection -unique fin ""
  set resets [filter_collection $fin "full_name !~ *_scan_*rst"]
  if { [sizeof_collection $resets] > 0 } {
   set nPr [get_object_name $pr]
   set nFin [join [get_object_name $fin] ", "]
   echo "*** Error: Pin $nPr with non-scan reset source, all resets are: $nFin"
  }
  #echo [get_object_name $resets]
 }
 remove_case_analysis *_scan_mode
 remove_case_analysis $port_otm
}

# Clock checking procedure
proc check_clocks {rpt_file} {
 echo "# Clock Report" > $rpt_file
 set all_ckpins [all_registers -clock_pins]
 ## Remove RD/SD pins
 set all_ckpins [filter_collection $all_ckpins "is_async_pin != true && full_name !~ phy*/pma/*"]
 ## Added top output clock pins for checking
 append_to_collection all_ckpins [get_pins "*_clk" -filter "direction == out"]
 ### NOTE: pma/scan*clk are not checked, doesn't seem required

 redirect -tee -append $rpt_file {
  foreach_in_collection ckpin $all_ckpins {
   # Get the register name and clock pin
   set pin_name [get_object_name $ckpin]
   # Get the clocks on the pin
   set clks [get_attribute -quiet [get_pins $ckpin] clocks]

   # skip incoming scan clock inputs
   if {[regexp {phy.*_scan.*} $pin_name]} {
    continue
   }
   if {[regexp {phy.*/pma/scan.*} $pin_name]} {
    continue
   }

   # Check for at least 1 functional (non-scan) clock
   set func_clks [filter_collection $clks -regexp {name !~ "scan_.*"}]
   set func_clks [filter_collection $func_clks -regexp {name !~ ".*_scan_.*"}]
   set num_func_clks [sizeof_collection $func_clks]
   if { $num_func_clks == 0 } {
    echo "*** Warning: no functional clocks on $pin_name"
   } else {
    #echo "Pin : $pin_name Functional clocks : [get_object_name $func_clks]"
   }

   # skip BSCAN pins of pma for checking scan clock
   if {[regexp {pma/bs_.*} $pin_name]} {
    continue
   }
   # skip free running clock pins for checking scan clock
   if {[regexp {pma/.*_fr_clk} $pin_name]} {
    continue
   }

   # Check for exactly 1 scan shift clock
   set scan_shift_clks [filter_collection $clks -regexp {name =~ "(.*scan_.*shift.*_clk)"}]
   set num_scan_shift_clks [sizeof_collection $scan_shift_clks]
   if { $num_scan_shift_clks == 0 } {
    echo "*** Warning: no scan shift and stuck at clock on $pin_name"
   } elseif { $num_scan_shift_clks > 1 } {
    echo "*** Warning: More than 1 scan shift and stuck at clock on $pin_name"
    echo "*** [get_object_name $scan_shift_clks]"
   } else {
    #echo "Pin : $pin_name Scan shift and stuck at clock : [get_object_name $scan_shift_clks]"
   }

   # Check for exactly 1 scan clock
   set scan_clks [filter_collection $clks -regexp {name =~ ".*scan_.*"}]
   set scan_clks [remove_from_collection $scan_clks $scan_shift_clks]
   #set scan_clks [remove_from_collection $scan_clks $scan_sa_clks]
   set num_scan_clks [sizeof_collection $scan_clks]
   if { $num_scan_clks == 0 } {
    echo "*** Warning: no scan clock on $pin_name"
   } elseif { $num_scan_clks > 1 } {
    echo "*** Warning: More than 1 scan clock on $pin_name"
    echo "*** [get_object_name $scan_clks]"
   } else {
    #echo "Pin : $pin_name Scan clock : [get_object_name $scan_clks]"
   }
  }
 }
}; # check_clocks

proc check_asst_vs_func_clocks {rpt_file} {
 echo "# ASST vs FUNC clock Frequency Report" > $rpt_file
 set all_ckpins [all_registers -clock_pins]
 ## Remove RD/SD pins
 set all_ckpins [filter_collection $all_ckpins "is_async_pin != true && full_name !~ phy*/pma/*"]
 ## Added top output clock pins for checking
 append_to_collection all_ckpins [get_pins "*_clk" -filter "direction == out"]
 ### NOTE: pma/scan*clk are not checked, doesn't seem required

 foreach_in_collection reg_pins $all_ckpins {
  set pin [get_object_name $reg_pins]
  # skip BSCAN pins of pma for checking scan clock
  if {[regexp {pma/bs_.*} $pin]} {
   continue
  }
  # skip free running clock pins for checking scan clock
  if {[regexp {pma/.*_fr_clk} $pin]} {
   continue
  }

  set func_clks [get_object_name [get_clocks  [get_attribute -quiet [get_pins $pin] clocks] -filter "name !~ *scan*"]]
  set at_speed_scan_clks [get_object_name [get_clocks  [get_attribute -quiet [get_pins $pin] clocks] -filter "name =~ *scan* && name !~ *shift* && name !~ *sa*"]]
  if { $func_clks != "" && $at_speed_scan_clks != "" } {
   set func_clock_period [lindex [lsort -increasing [get_attribute [get_clocks  [get_attribute -quiet [get_pins $pin] clocks] -filter "name !~ *scan*"] period]] 0]
   set at_speed_scan_clks_period [lindex [lsort -increasing [get_attribute [get_clocks  [get_attribute -quiet [get_pins $pin] clocks] -filter "name =~ *scan* && name !~ *shift* && name !~ *sa*"] period]] 0]
   set clock_period_diff [expr $func_clock_period - $at_speed_scan_clks_period]
   if { $clock_period_diff < 0.0 } {
    #echo "$clock_period_diff\t$at_speed_scan_clks\t$func_clks\t$pin" >> reg_to_review_func_lessthan_scan.rpt
    echo "asst clock underconstrained for pin $pin " >>  $rpt_file
    echo "asst clock underconstrained by: $clock_period_diff, Scan Clk : $at_speed_scan_clks\t$at_speed_scan_clks_period, Func Clk: $func_clks\t$func_clock_period" >>  $rpt_file
   } elseif {$clock_period_diff > 0.0} {
    #echo "$clock_period_diff\t$at_speed_scan_clks\t$func_clks\t$pin" >> reg_to_review_func_greaterthan_scan.rpt
    echo "asst clock overconstrained for pin $pin " >> $rpt_file
    echo "asst clock overconstrained by: $clock_period_diff, Scan Clk : $at_speed_scan_clks\t$at_speed_scan_clks_period, Func Clk: $func_clks\t$func_clock_period" >> $rpt_file
   }
  } else {
   echo "Warning : either func or at-speed scan clocks missing for register $pin" >> ./reports/reg_with_clocks_missing.rpt
  }
 }
}; # check_asst_vs_func_clocks
###################################################################################################
# set max delay between clock lists
# and set false path -hold between clock lists
# Auguments:
#       <m_value>   max delay value
#       <ck_lst1>   clock list 1
#       <ck_lst2>   clock list 2

if {[string equal $synopsys_program_name "dc_shell"]} {
  alias set_max_delay_w_or_wo_ignore_clock_latency "set_max_delay"
  alias set_min_delay_w_or_wo_ignore_clock_latency "set_min_delay"
} elseif {[string equal $synopsys_program_name "pt_shell"]} {
  alias set_max_delay_w_or_wo_ignore_clock_latency "set_max_delay -ignore_clock_latency"
  alias set_min_delay_w_or_wo_ignore_clock_latency "set_min_delay -ignore_clock_latency"
} else {
  alias set_max_delay_w_or_wo_ignore_clock_latency "set_max_delay -ignore_clock_latency"
  alias set_min_delay_w_or_wo_ignore_clock_latency "set_min_delay -ignore_clock_latency"
}

proc set_max_delay_between_clock_lists {m_value ck_lst1 ck_lst2} {
    puts "set max delay between these clocks list:"
    puts "  clock_list1: [get_object_name $ck_lst1]"
    puts "  clock_list2: [get_object_name $ck_lst2]"
    
    set_max_delay_w_or_wo_ignore_clock_latency $m_value -from $ck_lst1 -to $ck_lst2
#    set_max_delay_w_or_wo_ignore_clock_latency $m_value -from $ck_lst2 -to $ck_lst1

    set_false_path -hold -from $ck_lst1 -to $ck_lst2
#    set_false_path -hold -from $ck_lst2 -to $ck_lst1

    return    
}
# End of set_max_delay_between_clock_lists

