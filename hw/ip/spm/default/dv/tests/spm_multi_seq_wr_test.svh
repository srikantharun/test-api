`ifndef GUARD_SPM_MULTI_SEQ_WR_TEST_SV
`define GUARD_SPM_MULTI_SEQ_WR_TEST_SV


class spm_multi_seq_wr_test extends spm_base_test;

    axi_wr_rd_sequence wr_seq [];
    bit [64-1:0] reg_read_data;

    cust_svt_axi_master_transaction base_xact;

    spm_illegal_axi_txn_demoter m_axi_demoter;

    int number_of_srams = 0;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_multi_seq_wr_test)

    /** Class Constructor */
    function new(string name = "spm_multi_seq_wr_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);
        m_axi_demoter = new();
        uvm_report_cb::add(null, m_axi_demoter);


        number_of_srams = spm_config.spm_nb_banks * spm_config.spm_nb_sub_banks * spm_config.spm_nb_mini_banks * spm_config.spm_nb_srams_per_mini_bank;


        wr_seq = new[number_of_srams];

        spm_memory_allocator.policy = ALLOCATE_FRONT;

        for (int i = 0; i < number_of_srams; i++) begin
            wr_seq[i] = axi_wr_rd_sequence::type_id::create($sformatf("wr_seq_%0d", i));
            wr_seq[i].randomize() with {
                sequence_length <= 10;
            };
            wr_seq[i].enable_checks = 0;
        end

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase

    virtual task run_phase(uvm_phase phase);
        uvm_status_e status;
        phase.raise_objection(this);

        foreach(wr_seq[i]) begin
            wr_seq[i].spm_memory_range = spm_memory_allocator.allocate();
        end

        #100

        for(int index = 0; index < number_of_srams; index++) begin
            // Start the sequence on the respective sequencer
            wr_seq[index].start(env.m_axi_system_env.master[0].sequencer);
        end


        #500

        phase.drop_objection(this);
    endtask

endclass

`endif // GUARD_SPM_MULTI_SEQ_WR_TEST_SV
