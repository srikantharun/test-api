`ifndef GUARD_SPM_PARTIALS_WR_TEST_SV
`define GUARD_SPM_PARTIALS_WR_TEST_SV


class spm_partials_wr_test extends spm_base_test;

    axi_wr_rd_sequence wr_seq;

    cust_svt_axi_master_transaction base_xact;

    spm_illegal_axi_txn_demoter m_axi_demoter;

    rand int rand_burst;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_partials_wr_test)

    /** Class Constructor */
    function new(string name = "spm_partials_wr_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        if (cfg == null) begin
            cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
        end
        cfg.master_cfg[0].wysiwyg_enable = 0;

        super.build_phase(phase);
        m_axi_demoter = new();
        uvm_report_cb::add(null, m_axi_demoter);



        wr_seq = axi_wr_rd_sequence::type_id::create("wr_seq");


        wr_seq = axi_wr_rd_sequence::type_id::create($sformatf("wr_seq"));
        //wr_seq.allowed_burst_length.constraint_mode(0);
        wr_seq.enable_checks = 0;
        wr_seq.allow_partials = 1;
        wr_seq.full_wstrb = 0;
        wr_seq.randomize();

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase



    virtual function void end_of_elaboration_phase(uvm_phase phase);
        `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)

        super.end_of_elaboration_phase(phase);

        env.cfg.master_cfg[0].wysiwyg_enable = 0;

        `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
    endfunction : end_of_elaboration_phase



    virtual task run_phase(uvm_phase phase);
        uvm_status_e status;
        phase.raise_objection(this);

        #100

        wr_seq.start(env.m_axi_system_env.master[0].sequencer);

        #500

        phase.drop_objection(this);
    endtask

endclass

`endif // GUARD_SPM_PARTIALS_WR_TEST_SV
