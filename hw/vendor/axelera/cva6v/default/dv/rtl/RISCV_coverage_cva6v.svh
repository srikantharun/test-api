//
// Copyright (c) 2005-2024 Imperas Software Ltd. All Rights Reserved.
//
// THIS SOFTWARE CONTAINS CONFIDENTIAL INFORMATION AND TRADE SECRETS
// OF IMPERAS SOFTWARE LTD. USE, DISCLOSURE, OR REPRODUCTION IS PROHIBITED
// EXCEPT AS MAY BE PROVIDED FOR IN A WRITTEN AGREEMENT WITH IMPERAS SOFTWARE LTD.
//
//

`include "default_config/RISCV_coverage_config.svh"
`include "default_config/RISCV_csr_config.svh"
`include "RISCV_coverage_pkg_cva6v.svh"


import RISCV_coverage_pkg_cva6v::*;

class coverage_cva6v #(
        parameter int ILEN   = 32,  // Instruction length in bits
        parameter int XLEN   = 64,  // GPR length in bits
        parameter int FLEN   = 32,  // FPR length in bits
        parameter int VLEN   = 4096, // Vector register size in bits
        parameter int NHART  = 1,   // Number of harts reported
        parameter int RETIRE = 1    // Number of instructions that can retire during valid event
) extends RISCV_coverage_cva6v #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE);

    function new(virtual rvviTrace #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE) rvvi);
        super.new(rvvi);

        // Initialize custom covergroups here

    endfunction

    function void sample(bit trap, int hart, int issue, string disass);
        save_rvvi_data(trap, hart, issue, disass);

        sample_extensions(hart, issue);
        super.sample_idv_metrics();
        if (csrs_written(hart, issue)) begin
            sample_csrs(hart, issue);
        end

        // Sample custom covergroups here

    endfunction

endclass

