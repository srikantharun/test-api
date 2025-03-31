//---------------------------------------------------------------------------
// Project    : Axelera LPDDR Subsystem
// File name  : lpddr_subsystem_coverage_lib.svh
//---------------------------------------------------------------------------
//Description :
//---------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_COVERAGE_LIB_SVH
`define LPDDR_SUBSYSTEM_COVERAGE_LIB_SVH

`include "lpddr_subsystem_initialization_covergroups.sv"
`include "lpddr_subsystem_traffic_flow_and_addr_traslataion_covergroups.sv"
`include "lpddr_subsystem_command_scheduling_covergroups.sv"
`include "lpddr_subsystem_ecc_and_ras_covergroups.sv"
`include "lpddr5_subsystem_dfi_updates_covergroups.sv"
`include "lpddr5_subsystem_low_power_and_power_saving_features_covergroups.sv"
`include "lpddr5_subsystem_periodic_memory_and_phy_maintenance_covergroups.sv"
`include "lpddr5_subsystem_refresh_control_and_management_covergroups.sv"
`include "lpddr_subsystem_perf_signals_covergroup.sv"
`include "lpddr_subsystem_coverage_collector.sv"
`endif //LPDDR_SUBSYSTEM_COVERAGE_LIB_SVH
