//
// File: lpddr_subsystem_pkg.sv
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
`include "RAL/lpddr_subsystem_ral_chip_pkg.sv"

package lpddr_subsystem_pkg;
    import uvm_pkg::*;
    
    `include "uvm_macros.svh"
    
    import addr_map_pkg::*;
    
    import uvmf_base_pkg::*;
    import lpddr_subsystem_params_pkg::*;
    import lpddr_subsystem_typedef_pkg::*;
    import mvc_pkg::*;
    import mgc_apb_seq_pkg::*;
    import mgc_apb3_v1_0_pkg::*;
    import mgc_axi4_seq_pkg::*;
    import mgc_axi4_v1_0_pkg::*;
    import amem_pkg::*;
    import lpddr_subsystem_ral_chip_pkg::*;


		//`include "axi_lpddr_scheduler_seq.sv"
		`include "lpddr_subsystem_env_configuration.sv"
		`include "lpddr_subsystem_seq_lib.svh"
		`include "lpddr_subsystem_virtual_sequencer.sv"
    `include "lpddr_subsystem_coverage_lib.svh"
    `include "axi4_master_rw_extended_transaction.sv"
    `include "lpddr_subsystem_reference_model.sv"
    `include "lpddr_subsystem_scoreboard.sv"
    `include "lpddr_subsystem_environment.sv"
endpackage: lpddr_subsystem_pkg
