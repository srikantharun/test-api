`ifndef GUARD_SPM_ONE_TRANSACTION_TEST_SV
`define GUARD_SPM_ONE_TRANSACTION_TEST_SV


class spm_one_transaction_test extends spm_base_test;

    axi_wr_rd_sequence wr_seq;

    spm_illegal_axi_txn_demoter m_axi_demoter;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_one_transaction_test)

    /** Class Constructor */
    function new(string name = "spm_one_transaction_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);
        m_axi_demoter = new();
        uvm_report_cb::add(null, m_axi_demoter);
        wr_seq = axi_wr_rd_sequence::type_id::create("wr_seq");


        wr_seq.randomize() with {
            sequence_length == 1;
        };
        foreach(wr_seq.wburst_length[i]) begin
            wr_seq.wburst_length[i] = 1;
            wr_seq.rburst_length[i] = 1;
            wr_seq.burst_type[i] = svt_axi_transaction::INCR;
        end
        wr_seq.custom_burst_length = 1;
        wr_seq.custom_burst_type = 1;

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase

    virtual task run_phase(uvm_phase phase);
        uvm_status_e status;
        phase.raise_objection(this);

        #100
       // Start the sequence on the respective sequencer
        wr_seq.start(env.m_axi_system_env.master[0].sequencer);

        #300

        phase.drop_objection(this);
    endtask

endclass

`endif // GUARD_SPM_ONE_TRANSACTION_TEST_SV
