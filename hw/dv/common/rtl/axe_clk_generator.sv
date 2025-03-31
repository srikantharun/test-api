// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

module axe_clk_generator(input  wire  i_enable,
                         output logic o_clk);

    // Time unit and precision
    timeunit      1ps;
    timeprecision 1ps;

    int pd, hi, lo;
    int pd_r, hi_r, lo_r;
    bit en;

    /* Function: set_clock

      Set clock frequency and duty cylce
      Takes effect next rising edge clock

      Parameters:

         freq_mhz - required clock frequency in mHz
             duty     - Duty cycle (% of period high)
    */
    function automatic set_clock(input real freq_mhz, input int duty);
        pd_r = 1e6 / freq_mhz;
        hi_r = (pd_r * duty) /100;
        lo_r = pd_r - hi_r;

        $display("%t: %m: set_clock %0dmHz Duty Cycle %0d/%0d", $time, freq_mhz, duty, (100-duty));
    endfunction

   initial begin
        en    <= 1'b0;
        o_clk <= 1'b0;
    end

    always @(i_enable) begin
        if (i_enable) begin
            assert(pd_r);
            en <= 1'b1;
        end
        else begin
            en <= 1'b0;
        end
    end

    always @(posedge en) begin
        if (en) begin
            pd    = pd_r;
            hi    = hi_r;
            lo    = lo_r; 
            o_clk = 1'b0;
            while(en) begin
                #(lo) o_clk <= en;
                #(hi) o_clk <= 1'b0;
                pd = pd_r;
                hi = hi_r;
                lo = lo_r;
            end
        end
    end
 
endmodule // axe_clk_generator
