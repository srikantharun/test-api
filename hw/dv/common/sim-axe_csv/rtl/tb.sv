// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

module tb();
    import axe_csv_pkg::*;

    initial begin
        automatic chandle h;
        h = open_csv("test_data.csv", "column1,column2,column3");
        for (int i = 0; i < 10; i++) begin
            write_csv(h, '{$psprintf("%0d", i), "HELLO WORLD", $psprintf("%0.2f", (real'(i)/100.00))});
        end
    end


    initial begin
        automatic chandle h;
        #100;
        h = open_csv("test_data.csv", "a,b,c");
        for (int i = 100; i < 110; i++) begin
            write_csv(h, '{$psprintf("%0d", i), "GOODBYE WORLD", $psprintf("%0.2f", (real'(i)/100.00))});
        end
    end

    initial begin
        automatic chandle h;
        h = open_csv("test_data2.csv", "a,b,c");
        for (int i = 200; i < 210; i++) begin
            write_csv(h, '{$psprintf("%0d", i), "OTHER WORLD", $psprintf("%0.2f", (real'(i)/100.00))});
        end
    end

    final close_csv(null);

endmodule // tb
