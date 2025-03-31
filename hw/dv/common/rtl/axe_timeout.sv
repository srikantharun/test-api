// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Common Timeout Module
// Provide regular messages to allow user to know we're not in a delta cycle loop
// Provide timeouts to prevent long simulations
// Owner: abond

module axe_timeout();

    // Time unit and precision
    timeunit      1ps;
    timeprecision 1ps;

    /* Task: timeout 
      Set soft (warning) and hard (fatal) timeouts

      Start immediately, but are non-blocking

      Parameters:
        soft_timeout_ns - Duration of soft timeout (ns)
        hard_timeout_ns - Duration of hard timeout (ns) 

    */
    task automatic timeout(input int soft_timeout_ns, input int hard_timeout_ns);
        $display("%t: %m: timeout: Setting Soft Timeout %0dns, Hard Timeout %0dns", $time, soft_timeout_ns, hard_timeout_ns);

        fork
          begin
            #(1000*soft_timeout_ns);
            $warning("%t: %m: timeout: Soft Timeout Expired", $time);
          end
          begin
            #(1000*hard_timeout_ns);
            $fatal(1, "%t: %m: timeout: Hard Timeout Expired", $time);
          end
        join_none
    endtask : timeout

    /* Task: ticker 
      Generate regular ticker message  

      Parameters:
        period_ns - Period of ticker (ns)
        message   - Custom message
    */
    task automatic ticker(input int period_ns, input string message="");

        fork
            forever begin
              #(1000*period_ns);
              if (message == "")
                  $display("%t: %m: ticker: Tempus Fugit", $time);
              else
                  $display("%t: %m: ticker: %s", $time, message);
            end
        join_none
    endtask : ticker

endmodule // axe_rst_generator
