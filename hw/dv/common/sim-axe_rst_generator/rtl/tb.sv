// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

module tb();

    logic clk_en, clk, rst;

    axe_clk_generator u_axe_clk_generator(
                                            .i_enable(clk_en),
                                            .o_clk(clk)
                                         );

                            
    axe_rst_generator u_axe_rst_generator(
                                            .i_clk(clk),
                                            .o_rst(rst)
                                         );

    initial begin
        clk_en <= 1'b1;

        u_axe_clk_generator.set_clock(.freq_mhz(800), .duty(50));

        #345ps;
        u_axe_rst_generator.async_rst(.duration_ns(1000));
        #1us;
        u_axe_rst_generator.sync_rst(.duration_cycles(10));

        #1us $finish;
    end

endmodule // tb
