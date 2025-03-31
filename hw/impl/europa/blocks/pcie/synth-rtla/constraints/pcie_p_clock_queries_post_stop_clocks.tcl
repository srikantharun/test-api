############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_clock_queries_post_stop_clocks.tcl
#
# PIPE(UPCS+PHY) synthesis 2nd implicit timing update required to query clocks reaching on bus sync cells after stop propagations
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

## 2nd implicit/explicit timing update
if { $DC_SHELL } {
 # clocks stop propagations and other exceptions are done now queries about clocks on gen bus sync to be used in set_data_check in upcs_exceptions
 update_timing
}


# PCS debug bus synchronizers are removed as the requirement to meet 80% skew between multi bits is not mandate for these debug instances(dbg_bus.*sync*)

set gen_bus_sync_cells [get_cells -hier -filter "ref_name=~*gen_bus_sync* && full_name!~*/dbg_bus*pclk_sync*"]
foreach_in_collection gen_bus_sync_cell $gen_bus_sync_cells {
 set gen_cell_name [get_object_name $gen_bus_sync_cell]
 #echo "\ngen cell $gen_cell_name."
 #echo "\ngen cell $gen_bus_sync_cell."
 set leaf_sync_d_pins ""
 set leaf_sync_d_pins [get_pins $gen_cell_name/gen_sync_cell_*/*bcm41_inst/*U_SYNC*/*$sync_3_stage_src_inst_name*/$sync_3_stage_src_data_s_pin]
 set leaf_sync_cell   [get_cells -of [lindex [lsort -dic [get_object_name $leaf_sync_d_pins]] 0]]
 set clk_pin          [get_pins -of_objects  $leaf_sync_cell -filter "pin_direction==in && defined(clocks)"]
 set sync_clks        [get_attribute $clk_pin clocks]
 if { !$remove_upcs_scan_constraints } {
  set sync_clks        [remove_from_collection $sync_clks [get_clocks *scan*clk*]]
 }

 set min_clk ""
 set min_per [expr {100 * $TUNIT}]
 foreach_in_collection clk $sync_clks {
  set clk_name [get_attribute [get_clocks $clk] full_name]
  set clk_per $period($clk_name)

  if { $clk_per < $min_per} {
   set min_clk $clk
   set min_per $clk_per
  }
  puts "\[Constraints Debug\] Info: [file tail [info script]] 2 analysing gen bus sync cell $gen_cell_name and their minimum clock period $min_per to use in set_data_check constraints"
 }

 # Constraint max skew to 80% of destination clock period
 set max_skew [expr {$min_per * 0.8}]
 set t_setup  [expr {-1.0 * $max_skew}]
 set max_skew_val($gen_cell_name) $max_skew
 set t_setup_val($gen_cell_name) $t_setup
 set min_clk_name($gen_cell_name) [get_object_name $min_clk]
 set leaf_sync_d_pins_col($gen_cell_name) $leaf_sync_d_pins
}

set dtb_out_scan_mux_d0_pins [get_pins -quiet -hierarchical -filter "full_name =~ [prefixing $hiervar phy*/pcs_raw*dtb_out_scan_mux*$mx_src_inst_name/$mx_src_a0_pin]"]
set raw_pcs_clk_mux_d0_pins  [get_pins -quiet -hierarchical -filter "full_name =~ [prefixing $hiervar phy*/pcs_raw*raw_pcs_clk_mux*$mx_src_inst_name/$mx_src_a0_pin]"]
set dtb_out_reg_list [get_cells -quiet [prefixing $hiervar phy*/pcs_raw/aon/aon_cmn/dtb_out_r_reg*]]
set dtb_out_reg_in_pins [get_pins -quiet -of_objects $dtb_out_reg_list -filter "direction == in && is_data_pin"]

if { !$tx_only_supported } {
 set lane_mode_8b10b_reg [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/lane_mode_8b10b*reg*/*] -filter "is_clock_pin==true && pin_direction==in"]
 if { !$remove_upcs_scan_constraints } {
  set func_at_speed_clks  [remove_from_collection [get_attribute [get_pins [get_object_name $lane_mode_8b10b_reg]] clocks] [get_clocks -quiet [concat *scan*shift*clk* *scan*sa*clk*]]]
 } else {
  set func_at_speed_clks  [get_attribute [get_pins [get_object_name $lane_mode_8b10b_reg]] clocks]
 }
}

