// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Test
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>

`ifndef GUARD_TKN_MNG_BASE_TEST_SV
`define GUARD_TKN_MNG_BASE_TEST_SV


class tkn_mng_base_test extends uvm_test;

    /** UVM Component Utility macro */
    `uvm_component_utils(tkn_mng_base_test)

    /** Instance of the environment */
    tkn_mng_env env;

    /** Class Constructor */
    function new(string name = "tkn_mng_base_test", uvm_component parent=null);
        super.new(name,parent);
    endfunction: new



    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);

        /** Create the environment */
        env = tkn_mng_env::type_id::create("env", this);

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction: build_phase




    /**
    * Calculate the pass or fail status for the test in the final phase method of the
    * test. If a UVM_FATAL, UVM_ERROR, or a UVM_WARNING message has been generated the
    * test will fail.
    */
    function void final_phase(uvm_phase phase);
        uvm_report_server svr;
        `uvm_info("final_phase", "Entered...",UVM_LOW)

        super.final_phase(phase);

        svr = uvm_report_server::get_server();

        if (svr.get_severity_count(UVM_FATAL) +
            svr.get_severity_count(UVM_ERROR) +
            svr.get_severity_count(UVM_WARNING) > 0)
        `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
        else
        `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

        `uvm_info("final_phase", "Exiting...", UVM_LOW)
    endfunction: final_phase

endclass

`endif // GUARD_TKN_MNG_BASE_TEST_SV
