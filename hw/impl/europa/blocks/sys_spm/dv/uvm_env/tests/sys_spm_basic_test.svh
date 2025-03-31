`ifndef GUARD_SYS_SPM_BASIC_TEST_SV
`define GUARD_SYS_SPM_BASIC_TEST_SV

class sys_spm_basic_test extends sys_spm_base_test;

    spm_seq_pkg::axi_wr_rd_sequence basic_seq;
    bit [64-1:0] reg_read_data;

    /** UVM Component Utility macro */
    `uvm_component_utils(sys_spm_basic_test)

    /** Class Constructor */
    function new(string name = "sys_spm_basic_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);

        basic_seq = spm_seq_pkg::axi_wr_rd_sequence::type_id::create("basic_seq");

        basic_seq.randomize();
        foreach(basic_seq.wburst_length[i]) begin
            basic_seq.wburst_length[i] = 1;
            basic_seq.rburst_length[i] = 1;
            basic_seq.burst_type[i] = svt_axi_transaction::INCR;
        end
        basic_seq.custom_burst_type = 1;
        basic_seq.custom_burst_length = 1;
        basic_seq.enable_checks = 0;

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase

    virtual task run_phase(uvm_phase phase);
        uvm_status_e status;
        phase.raise_objection(this);

        #100

       // Start the sequence on the respective sequencer
        basic_seq.start(env.spm_ip_env.m_axi_system_env.master[0].sequencer);


        #500

        phase.drop_objection(this);
    endtask

endclass

`endif // GUARD_SYS_SPM_BASIC_TEST_SV
