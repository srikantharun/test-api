// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
// APB-related properties

package apb_properties_pkg;

  // PENABLE shall always rise on the second cycle of a transaction.
  // A transaction starts on either:
  //  - PSEL   0 to 1 transition
  //  - PREADY 1 to 0 transition with PSEL = 1 (back to back transactions)
  property p_penable_rise(clk, rst_n, psel, penable, pready);
    @(posedge clk)
    disable iff (!rst_n)
    $rose(psel) || (psel && $fell(pready)) |-> ##1 $rose(penable);
  endproperty : p_penable_rise

  property p_ctl_sig_stable(clk, rst_n, req_ongoing, signal);
    @(posedge clk)
    disable iff (!rst_n)
    req_ongoing |-> $stable(signal);
  endproperty : p_ctl_sig_stable

endpackage
