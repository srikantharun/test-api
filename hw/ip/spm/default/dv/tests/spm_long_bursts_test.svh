`ifndef GUARD_SPM_LONG_BURSTS_TEST_SV
`define GUARD_SPM_LONG_BURSTS_TEST_SV


class spm_long_bursts_test extends spm_base_test;

    axi_wr_rd_sequence wr_seq;
    bit [64-1:0] reg_read_data;

    cust_svt_axi_master_transaction base_xact;

    spm_illegal_axi_txn_demoter m_axi_demoter;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_long_bursts_test)

    /** Class Constructor */
    function new(string name = "spm_long_bursts_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);
        m_axi_demoter = new();
        uvm_report_cb::add(null, m_axi_demoter);
        wr_seq = axi_wr_rd_sequence::type_id::create("wr_seq");


        wr_seq.randomize();

        foreach(wr_seq.wburst_length[i]) begin
            wr_seq.wburst_length[i] = 16;
            wr_seq.rburst_length[i] = 16;
        end
        // long delay
        wr_seq.max_delay_between_wr_rd = 50;
        wr_seq.min_delay_between_wr_rd = 30;

        wr_seq.custom_burst_length = 1;
        wr_seq.enable_checks = 0;
        //delays to 0
        wr_seq.max_addr_valid_delay = 0;
        wr_seq.max_rready_delay = 0;
        wr_seq.max_wvalid_delay = 0;

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase

    virtual task run_phase(uvm_phase phase);
        uvm_status_e status;
        phase.raise_objection(this);

        #100
       // Start the sequence on the respective sequencer
        wr_seq.start(env.m_axi_system_env.master[0].sequencer);


        #500

        phase.drop_objection(this);
    endtask

endclass

`endif // GUARD_SPM_LONG_BURSTS_TEST_SV
