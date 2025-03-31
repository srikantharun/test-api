//
// File: top_test_pkg.sv
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
// ## The following code is used to add this qvip_configurator generated output into an
// ## encapsulating UVMF Generated environment.  The addQvipSubEnv function is added to 
// ## the python configuration file used by the UVMF environment generator.
// env.addQvipSubEnv('sub_env_instance_name', 'top', ['apb_master_0', 'axi4_master_0'])
//
// ## The following code is used to add this qvip_configurator generated output into an
// ## encapsulating UVMF Generated test bench.  The addQvipBfm function is added to 
// ## the python configuration file used by the UVMF bench generator.
// ben.addQvipBfm('apb_master_0', 'top', 'ACTIVE')
// ben.addQvipBfm('axi4_master_0', 'top', 'ACTIVE')
package lpddr_subsystem_test_pkg;
    import uvm_pkg::*;
    
    `include "uvm_macros.svh"
    
    import addr_map_pkg::*;
    
    import uvmf_base_pkg::*;
    import lpddr_subsystem_params_pkg::*;
    import mvc_pkg::*;
    import mgc_apb_seq_pkg::*;
    import mgc_apb3_v1_0_pkg::*;
    import mgc_axi4_seq_pkg::*;
    import mgc_axi4_v1_0_pkg::*;
    import lpddr_subsystem_pkg::*;
    
    `include "top_vseq_base.svh"
    `include "lpddr_subsystem_base_test.svh"
    `include "top_example_vseq.svh"
    `include "lpddr_subsystem_sanity_test.sv"
    `include "lpddr_subsystem_mode_reg_rd_wr_test.sv"
		`include "lpddr_subsystem_axi_input_traffic_handling_test.sv"
    `include "lpddr_low_power_test.sv"
    `include "lpddr_subsystem_error_handling_test.sv"
    `include "lpddr_subsystem_link_ecc_inline_ecc_test.sv"
    `include "lpddr_subsystem_data_bus_inversion_wck_clocking_test.sv"
		`include "lpddr_subsystem_addr_collision_handling_and_write_combine_test.sv"
		`include "lpddr_subsystem_page_policy_test.sv"
		`include "lpddr_subsystem_page_match_test.sv"
		`include "lpddr_subsystem_write_to_read_switching_test.sv"
		`include "lpddr_subsystem_lpddr5_masked_write_test.sv"
		`include "lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test.sv"
		`include "lpddr_management_test.sv"
		`include "lpddr_subsystem_addr_translation_test.sv"
		//`include "lpddr_performance_test.sv"
endpackage: lpddr_subsystem_test_pkg
