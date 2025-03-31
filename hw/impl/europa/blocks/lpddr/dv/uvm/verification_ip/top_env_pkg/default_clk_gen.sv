//
// File: default_clk_gen.sv
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
module default_clk_gen
(
    output reg  CLK
);
    
    timeunit 1ps;
    timeprecision 1ps;
    
    initial
    begin
        CLK = 0;
        forever
        begin
            #625 CLK = ~CLK;
        end
    end

endmodule: default_clk_gen
