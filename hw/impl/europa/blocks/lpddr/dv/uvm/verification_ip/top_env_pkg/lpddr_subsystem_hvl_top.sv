//
// File: hvl_top.sv
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//

`include "lpddr_subsystem_params_pkg.sv"
`include "lpddr_subsystem_typedef_pkg.sv"
`include "lpddr_subsystem_pkg.sv"
`include "lpddr_subsystem_test_pkg.sv"
`include "subsystem_signal_intf.sv"

module hvl_top;
    import uvm_pkg::*;
    
    `include "test_packages.svh"

    initial
    begin
        run_test();
    end

endmodule: hvl_top
