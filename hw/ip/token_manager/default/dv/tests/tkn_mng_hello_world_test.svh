`ifndef GUARD_TKN_MNG_HELLO_WORLD_TEST_SV
`define GUARD_TKN_MNG_HELLO_WORLD_TEST_SV


class tkn_mng_hello_world_test extends tkn_mng_base_test;

    /** UVM Component Utility macro */
    `uvm_component_utils(tkn_mng_hello_world_test)


    /** Class Constructor */
    function new(string name = "tkn_mng_hello_world_test", uvm_component parent=null);
        super.new(name,parent);
    endfunction: new



    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);
        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction: build_phase



    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("run_phase", "Entered...", UVM_LOW)

        super.run_phase(phase);


        #100us;

        `uvm_info(get_full_name(), "HELLO WORLD! TKN MNG TB compiles!!", UVM_NONE)

        `uvm_info("run_phase", "Exiting...", UVM_LOW)
        phase.drop_objection(this);
    endtask: run_phase



endclass

`endif // GUARD_TKN_MNG_HELLO_WORLD_TEST_SV
