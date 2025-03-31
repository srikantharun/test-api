// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Common Reset generator
// Owner: abond

module axe_rst_generator
#(
    parameter bit INITIAL_RST = 1
) (
    input wire i_clk,
    output logic o_rst
);

    // Time unit and precision
    timeunit      1ps;
    timeprecision 1ps;

    /* Task: async_rst
      Generate async reset of set length

      Parameters:
        duration_ns - Duration of reset (ns)
    */
    task automatic async_rst(input int duration_ns, input int start_delay_ns = 0);
        $display("%t: %m: sync_rst: waiting %0d ns before Asserting Reset", $time, start_delay_ns);
        #(1000*start_delay_ns);
        $display("%t: %m: async_rst: Asserting Reset for %0dns", $time, duration_ns);
        o_rst <= 1'b1;
        #(1000*duration_ns);
        o_rst <= 1'b0;
        $display("%t: %m: async_rst: Deasserting Reset after %0dns", $time, duration_ns);
    endtask

    /* Task: sync_rst
      Generate sync reset of set length

      Parameters:
        duration_cyles - Duration of reset (cycles)
    */
    task automatic sync_rst(input int duration_cycles, input int start_delay_cycles = 1);
        $display("%t: %m: sync_rst: waiting %0d cycles before Asserting Reset", $time, start_delay_cycles);
        for (int i = 0; i < start_delay_cycles; i++) @(posedge i_clk);
        $display("%t: %m: sync_rst: Asserting Reset for %0d cycles", $time, duration_cycles);
        o_rst <= 1'b1;
        for (int i = 0; i < duration_cycles; i++) @(posedge i_clk);
        o_rst <= 1'b0;
        $display("%t: %m: sync_rst: Deasserting Reset after %0d cycles", $time, duration_cycles);
    endtask

    if (INITIAL_RST) begin
        initial begin
            o_rst <= 1'b1;
        end
    end


endmodule // axe_rst_generator
