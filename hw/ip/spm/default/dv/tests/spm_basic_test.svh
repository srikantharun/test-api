`ifndef GUARD_SPM_BASIC_TEST_SV
`define GUARD_SPM_BASIC_TEST_SV

class spm_basic_test extends spm_base_test;

    axi_basic_sequence basic_seq;
    bit [64-1:0] reg_read_data;

    cust_svt_axi_master_transaction base_xact;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_basic_test)

    /** Class Constructor */
    function new(string name = "spm_basic_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);

        basic_seq = axi_basic_sequence::type_id::create("basic_seq");

        /**
            * Apply the null sequence to the System ENV virtual sequencer to override the
            * default sequence.
            */
            //uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.sequencer.main_phase", "default_sequence", axi_null_virtual_sequence::type_id::get());

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase

    virtual task run_phase(uvm_phase phase);
        uvm_status_e status;
        phase.raise_objection(this);

        #500

       // Start the sequence on the respective sequencer
        basic_seq.start(env.m_axi_system_env.master[0].sequencer);

        phase.drop_objection(this);
    endtask

endclass

`endif // GUARD_SPM_BASIC_TEST_SV
