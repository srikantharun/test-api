// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Common properties
// Owner: abond

package axe_dv_properties_pkg;
    /*
        Valid / Ready handshake
    */
    property p_valid_ready_handshake(clk, rst_n, valid, ready);
        @(posedge clk)
        disable iff (!rst_n)
        (valid && !ready) |-> ##1 valid;
    endproperty : p_valid_ready_handshake

    property p_valid_ready_deassert(clk, rst_n, valid, ready);
        @(posedge clk)
        disable iff (!rst_n)
        $fell(valid) |-> $past(ready);
    endproperty : p_valid_ready_deassert

    property p_valid_ready_stable(clk, rst_n, valid, ready, signal);
        @(posedge clk)
        disable iff (!rst_n)
        (valid && !ready) |-> ##1 $stable(signal);
    endproperty : p_valid_ready_stable

endpackage : axe_dv_properties_pkg
