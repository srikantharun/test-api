`ifndef APB_SEQ_LIB
`define APB_SEQ_LIB


//===================== SNPS SEQS =========================================//
typedef class apb_master_random_discrete_sequence;

class apb_master_random_discrete_virtual_sequence extends svt_apb_system_base_sequence;

    rand int unsigned sequence_length = 32;

    constraint reasonable_sequence_length {
        sequence_length <= `P_APB_TRANSACTION_MAX;
    }

  `uvm_object_utils(apb_master_random_discrete_virtual_sequence)

    function new (string name = "apb_master_random_discrete_virtual_sequence");
        super.new(name);
    endfunction : new

    virtual task pre_body();
        uvm_phase starting_phase_for_curr_seq;
        super.pre_body();
        `ifdef SVT_UVM_12_OR_HIGHER
            starting_phase_for_curr_seq = get_starting_phase();
        `else
            starting_phase_for_curr_seq = starting_phase;
        `endif
        if (starting_phase_for_curr_seq!=null) begin
            starting_phase_for_curr_seq.raise_objection(this);
        end
    endtask: pre_body

    virtual task post_body();
        uvm_phase starting_phase_for_curr_seq;
        super.post_body();
        `ifdef SVT_UVM_12_OR_HIGHER
            starting_phase_for_curr_seq = get_starting_phase();
        `else
            starting_phase_for_curr_seq = starting_phase;
        `endif
        if (starting_phase_for_curr_seq!=null) begin
            starting_phase_for_curr_seq.drop_objection(this);
        end
    endtask: post_body

    virtual task body();
        bit status;
        int local_sequence_length;
        apb_master_random_discrete_sequence master_seq;

        `uvm_info("body", "Entered...", UVM_LOW)

        status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
        `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_LOW);

        local_sequence_length = sequence_length;

        master_seq = new("master_seq");
        `ifndef SVT_UVM_1800_2_2017_OR_HIGHER
            `uvm_do_on_with(master_seq, p_sequencer.master_sequencer, {sequence_length == local_sequence_length;})
        `else
            `uvm_do(master_seq, p_sequencer.master_sequencer,, {sequence_length == local_sequence_length;})
        `endif

        `uvm_info("body", "Exiting...", UVM_LOW)
    endtask: body

endclass: apb_master_random_discrete_virtual_sequence

class apb_master_random_discrete_sequence extends svt_apb_master_base_sequence;

    rand int unsigned sequence_length = 32;

    `uvm_object_utils(apb_master_random_discrete_sequence)

    constraint reasonable_sequence_length {
        sequence_length <= `P_APB_TRANSACTION_MAX;
    }

    function new (string name = "apb_master_random_discrete_sequence");
        super.new(name);
    endfunction : new

    virtual task body();
        bit status;

        `uvm_info("body", "Entered ...", UVM_LOW)
        super.body();

        status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
        `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_LOW);

        for(int i = 0; i < sequence_length; i++) begin
          //`uvm_do(req);
          `uvm_create(req);
          assert(req.randomize());
          req.address[1:0] = $urandom_range(0,3);
          `uvm_send(req);
          `uvm_info("body", $sformatf("sent item: %s", req.sprint()), UVM_LOW);
        end

        `uvm_info("body", "Exiting...", UVM_LOW);
    endtask: body

endclass: apb_master_random_discrete_sequence

class apb_mst_rd_wr_seq extends svt_apb_master_base_sequence;

    rand int unsigned sequence_length = 32;

    constraint reasonable_sequence_length {
        sequence_length <= `P_APB_TRANSACTION_MAX;
    }

    `uvm_object_utils(apb_mst_rd_wr_seq)

    function new(string name="apb_mst_rd_wr_seq");
        super.new(name);
    endfunction

    virtual task body();
        bit status;

        `uvm_info("body", "Entered ...", UVM_LOW);
        super.body();

        status = uvm_config_db #(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
        `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_LOW);

        repeat (sequence_length) begin
            `ifndef SVT_UVM_1800_2_2017_OR_HIGHER
            `uvm_do_with(req, { xact_type == svt_apb_transaction::WRITE; });
            `else
            `uvm_do(req,,, { xact_type == svt_apb_transaction::WRITE; });
            `endif
            // Turn off rand_mode of the address so that we read from the same location
            req.address.rand_mode(0);
            `ifndef SVT_UVM_1800_2_2017_OR_HIGHER
            `uvm_rand_send_with(req, { xact_type == svt_apb_transaction::READ; });
            `else
            `uvm_rand_send(req,, { xact_type == svt_apb_transaction::READ; });
            `endif
        end

        `uvm_info("body", "Exiting...", UVM_LOW);
    endtask: body

endclass: apb_mst_rd_wr_seq

class apb_slave_random_response_sequence extends svt_apb_slave_random_response_sequence;

    `uvm_object_utils(apb_slave_random_response_sequence)

    function new(string name="apb_slave_random_response_sequence");
        super.new(name);
    endfunction

endclass: apb_slave_random_response_sequence


`endif
