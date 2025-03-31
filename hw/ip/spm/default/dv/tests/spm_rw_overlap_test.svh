/**
 * Abstract:
 * This testcase is starting multiple write and reads at the same time.
 * The goal is to stress the req/rsp conditions in the spm_control when both a write and a read are available.
 * To achieve this, the ready/valid delays are rnadomized in a small rnage (0 to 2) and there is no delay between write and read from the mst.
 *
 */

`ifndef GUARD_SPM_RW_OVERLAP_TEST_SV
`define GUARD_SPM_RW_OVERLAP_TEST_SV


class spm_rw_overlap_test extends spm_base_test;

    axi_wr_rd_sequence wr_seq [];

    spm_illegal_axi_txn_demoter m_axi_demoter;

    int num_sequences;

    /** UVM Component Utility macro */
    `uvm_component_utils(spm_rw_overlap_test)

    /** Class Constructor */
    function new(string name = "spm_rw_overlap_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);
        m_axi_demoter = new();
        uvm_report_cb::add(null, m_axi_demoter);

        num_sequences = 100;

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase

    virtual task run_phase(uvm_phase phase);
        uvm_status_e status;
        phase.raise_objection(this);

        wr_seq = new[num_sequences];

        for(int i = 0; i < num_sequences; i++)
            wr_seq[i] = axi_wr_rd_sequence::type_id::create($sformatf("wr_seq_%0d", i));
        #100
        for(int j = 0; j < num_sequences; j++) begin
            fork
                automatic int k = j;
                begin

                    wr_seq[k].unique_random_address = 1;
                    wr_seq[k].max_id = 2;
                    wr_seq[k].allow_partials = 1;
                    wr_seq[k].enable_checks = 0;
                    wr_seq[k].randomize() with {
                        sequence_length == 1;
                    };
                    foreach(wr_seq[k].wburst_length[i]) begin
                        wr_seq[k].wburst_length[i] = 1;
                        wr_seq[k].rburst_length[i] = 1;
                        wr_seq[k].burst_type[i] = svt_axi_transaction::INCR;
                    end

                    // no delay between trans
                    wr_seq[k].max_delay_between_wr_rd = 0;

                    wr_seq[k].custom_burst_length = 1;
                    wr_seq[k].custom_burst_type = 1;
                    //delays from 0 to 2
                    wr_seq[k].max_addr_valid_delay = 2;
                    wr_seq[k].max_rready_delay = 2;
                    wr_seq[k].max_wvalid_delay = 2;
                    // Start the sequence on the respective sequencer
                    wr_seq[k].start(env.m_axi_system_env.master[0].sequencer);
                end
            join_none
        end

        wait fork;
        #300

        phase.drop_objection(this);
    endtask

endclass

`endif // GUARD_SPM_RW_OVERLAP_TEST_SV
