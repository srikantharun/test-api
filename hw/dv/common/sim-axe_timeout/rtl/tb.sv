// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Example of using timeout module
// Owner: abond

module tb();

    logic clk_en, clk, rst;

    axe_clk_generator u_axe_clk_generator(
                                            .i_enable(clk_en),
                                            .o_clk(clk)
                                         );

    axe_timeout u_axe_timeout();

    initial begin
        clk_en <= 1'b1;
        u_axe_timeout.timeout(1000, 2000);
        u_axe_timeout.ticker(200);
        u_axe_timeout.ticker(300, "User defined message");
        u_axe_clk_generator.set_clock(.freq_mhz(800), .duty(50));

        #1900ns $finish();
    end

endmodule // tb
