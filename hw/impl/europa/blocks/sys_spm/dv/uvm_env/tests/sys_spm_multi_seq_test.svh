`ifndef GUARD_SYS_SPM_MULTI_SEQ_TEST_SV
`define GUARD_SYS_SPM_MULTI_SEQ_TEST_SV


class sys_spm_multi_seq_test extends sys_spm_base_test;

    axi_wr_rd_sequence wr_seq [];

    int number_of_srams = 0;

    /** UVM Component Utility macro */
    `uvm_component_utils(sys_spm_multi_seq_test)

    /** Class Constructor */
    function new(string name = "sys_spm_multi_seq_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);

        number_of_srams = spm_config.spm_nb_banks * spm_config.spm_nb_sub_banks * spm_config.spm_nb_mini_banks * spm_config.spm_nb_srams_per_mini_bank;


        wr_seq = new[number_of_srams];

        spm_memory_allocator.policy = ALLOCATE_FRONT;

        for (int i = 0; i < number_of_srams; i++) begin
            wr_seq[i] = axi_wr_rd_sequence::type_id::create($sformatf("wr_seq_%0d", i));
            wr_seq[i].randomize() with {
                sequence_length  == 1;
            };
            wr_seq[i].enable_checks = 0;
            wr_seq[i].spm_memory_range = spm_memory_allocator.allocate();
            foreach(wr_seq[i].wburst_length[i]) begin
                wr_seq[i].wburst_length[i] = $urandom_range(100, 5);
                wr_seq[i].rburst_length[i] = wr_seq[i].wburst_length[i];
                wr_seq[i].burst_type[i] = svt_axi_transaction::INCR;
            end
            wr_seq[i].custom_burst_type = 1;
            wr_seq[i].custom_burst_length = 1;
        end

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase

    virtual task run_phase(uvm_phase phase);
        uvm_status_e status;
        phase.raise_objection(this);

        #100



        for(int index = 0; index < number_of_srams; index++) begin
            // Start the sequence on the respective sequencer
            wr_seq[index].start(env.spm_ip_env.m_axi_system_env.master[0].sequencer);
        end


        #500

        phase.drop_objection(this);
    endtask

endclass

`endif // GUARD_SYS_SPM_MULTI_SEQ_TEST_SV
