// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// CSV File generator package
// Owner: abond

// Package: axe_uvm_incrementor_pkg
package axe_csv_pkg;
    import "DPI-C" function chandle open_csv(string filename, input string hdr);
    import "DPI-C" function void close_csv(chandle h);
    import "DPI-C" function void write_csv(chandle h, input string args[]);
endpackage : axe_csv_pkg
