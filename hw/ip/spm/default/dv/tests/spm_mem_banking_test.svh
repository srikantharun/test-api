`ifndef GUARD_SPM_MEM_BANKING_TEST_SV
`define GUARD_SPM_MEM_BANKING_TEST_SV


class spm_mem_banking_test extends spm_base_test;

    axi_wr_rd_sequencial_sequence wr_seq;
    bit [64-1:0] reg_read_data;

    cust_svt_axi_master_transaction base_xact;

    spm_illegal_axi_txn_demoter m_axi_demoter;

    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0]             starting_address = 0;
    int number_of_srams = 0;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_mem_banking_test)

    /** Class Constructor */
    function new(string name = "spm_mem_banking_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);
        m_axi_demoter = new();
        uvm_report_cb::add(null, m_axi_demoter);



        number_of_srams = spm_config.spm_nb_banks * spm_config.spm_nb_sub_banks * spm_config.spm_nb_mini_banks * spm_config.spm_nb_srams_per_mini_bank;


        wr_seq = axi_wr_rd_sequencial_sequence::type_id::create("wr_seq");

        wr_seq.randomize() with {
            sequence_length == number_of_srams;
        };
        foreach(wr_seq.wburst_length[i]) begin
            wr_seq.wburst_length[i] = 1;
            wr_seq.rburst_length[i] = 1;
            wr_seq.burst_type[i] = svt_axi_transaction::INCR;
        end
        wr_seq.custom_burst_type = 1;
        wr_seq.custom_burst_length = 1;
        wr_seq.stride_addr = (spm_config.spm_mem_size_kb/number_of_srams)*1024;
        wr_seq.strided_address = 1;


        std::randomize (starting_address) with {
            starting_address >= 0;
            starting_address <= 1000;
            starting_address%8 == 0; //only line aligned
        };

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

`endif // GUARD_SPM_MEM_BANKING_TEST_SV
