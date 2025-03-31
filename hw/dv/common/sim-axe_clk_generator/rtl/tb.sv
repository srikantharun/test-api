// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

module tb();

    logic clk_en, clk;

    axe_clk_generator u_axe_clk_generator(
                                            .i_enable(clk_en),
                                            .o_clk(clk)
                                         );

    initial begin
        clk_en <= 1'b1;

        u_axe_clk_generator.set_clock(.freq_mhz(800), .duty(50));

        #1ms;
        u_axe_clk_generator.set_clock(.freq_mhz(1000), .duty(20));

        #1ms;
        #133ps;
        clk_en <= 1'b0;

        #1us;
        clk_en <= 1'b1;

        #1ms;
        u_axe_clk_generator.set_clock(.freq_mhz(333), .duty(60));

        #1ms $finish;
    end

endmodule // tb
