`ifndef GUARD_SPM_BACK_PRESSURE_TEST_SV
`define GUARD_SPM_BACK_PRESSURE_TEST_SV


class spm_back_pressure_test extends spm_base_test;

    axi_wr_rd_sequencial_sequence wr_seq;

    spm_illegal_axi_txn_demoter m_axi_demoter;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_back_pressure_test)

    /** Class Constructor */
    function new(string name = "spm_back_pressure_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);
        m_axi_demoter = new();
        uvm_report_cb::add(null, m_axi_demoter);
        wr_seq = axi_wr_rd_sequencial_sequence::type_id::create("wr_seq");


        wr_seq.randomize();
        wr_seq.enable_checks = 0;

        foreach(wr_seq.wburst_length[i]) begin
            // burst props
            wr_seq.wburst_length[i] = 1;
            wr_seq.rburst_length[i] = 1;
            wr_seq.burst_type[i] = svt_axi_transaction::INCR;
        end
        wr_seq.custom_burst_type = 1;
        wr_seq.custom_burst_length = 1;

        //valid delays to 0
        wr_seq.max_addr_valid_delay = 0;
        wr_seq.max_wvalid_delay = 0;

        //backpressure
        wr_seq.max_rready_delay = 50;
        wr_seq.min_rready_delay = 30;

        wr_seq.max_bready_delay = 50;
        wr_seq.min_bready_delay = 30;

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

`endif // GUARD_SPM_BACK_PRESSURE_TEST_SV
