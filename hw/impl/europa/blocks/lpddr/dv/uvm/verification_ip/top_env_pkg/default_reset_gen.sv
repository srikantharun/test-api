//
// File: default_reset_gen.sv
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
module default_reset_gen
(
    output reg  RESET,
    input  reg  CLK_IN
);
    
    initial
    begin
        RESET = 1;
        
        repeat ( 2 )
        begin
            @(negedge CLK_IN);
        end
        
        RESET = ~RESET;
        
        repeat ( 16 )
        begin
            @(negedge CLK_IN);
        end
        
        RESET = ~RESET;
    end

endmodule: default_reset_gen
