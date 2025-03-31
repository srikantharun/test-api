`ifndef GUARD_SPM_ECC_FULL_TEST_SV
`define GUARD_SPM_ECC_FULL_TEST_SV



class spm_ecc_full_test extends spm_base_test;

    axi_wr_rd_ecc_sequence wr_seq;
    bit [64-1:0] reg_read_data;

    cust_svt_axi_master_transaction base_xact;

    spm_illegal_axi_txn_demoter m_axi_demoter;

    int number_of_srams = 0;

    longint starting_address;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_ecc_full_test)

    /** Class Constructor */
    function new(string name = "spm_ecc_full_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);
        m_axi_demoter = new();
        uvm_report_cb::add(null, m_axi_demoter);
        wr_seq = axi_wr_rd_ecc_sequence::type_id::create("wr_seq");


        if(!uvm_config_db #(longint)::get(uvm_root::get(), "", "starting_address", starting_address))
            `uvm_fatal(get_full_name(), "no ecc sequence starting address found");


        number_of_srams = spm_config.spm_nb_banks * spm_config.spm_nb_sub_banks * spm_config.spm_nb_mini_banks * spm_config.spm_nb_srams_per_mini_bank;

        wr_seq.randomize() with {
            sequence_length == number_of_srams;

        };

        foreach(wr_seq.wburst_length[i]) begin
            wr_seq.wburst_length[i] = 1;
            wr_seq.rburst_length[i] = 1;
            wr_seq.burst_type[i] = svt_axi_transaction::INCR;
        end
        wr_seq.custom_burst_length = 1;
        wr_seq.custom_burst_type = 1;
        wr_seq.stride_addr = (spm_config.spm_mem_size_kb/number_of_srams)*1024;
        wr_seq.strided_address = 1;
        wr_seq.starting_address = starting_address;

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

`endif // GUARD_SPM_BASIC_TEST_SV
