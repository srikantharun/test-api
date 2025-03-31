// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Test
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>

`ifndef GUARD_TKN_MNG_LOC_DEV_TEST_SV
`define GUARD_TKN_MNG_LOC_DEV_TEST_SV


class tkn_mng_loc_dev_test extends tkn_mng_base_test;

    /** UVM Component Utility macro */
    `uvm_component_utils(tkn_mng_loc_dev_test)

    tkn_mng_aic_prod_sequence               aic_prod_seq;
    tkn_mng_aic_cons_sequence               aic_cons_seq;

    /** Class Constructor */
    function new(string name = "tkn_mng_loc_dev_test", uvm_component parent=null);
        super.new(name,parent);
    endfunction: new



    virtual function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)

        super.build_phase(phase);

        aic_prod_seq = tkn_mng_aic_prod_sequence::type_id::create("aic_prod_seq");
        aic_cons_seq = tkn_mng_aic_cons_sequence::type_id::create("aic_cons_seq");

        aic_prod_seq.randomize();
        aic_cons_seq.randomize() with {
            num_of_cons == aic_prod_seq.num_of_prod;
        };
        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction: build_phase



    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("run_phase", "Entered...", UVM_LOW)

        super.run_phase(phase);

        env.aic_agent.m_tkn_mng_aic_ref_model_cfg.cosume_all_tokens = 1;

        //assign agent handles for ap write into the the refmodel
        aic_prod_seq.aic_agent = env.aic_agent;
        aic_cons_seq.aic_agent = env.aic_agent;

        #10us;

        aic_prod_seq.start(null);

        #50us;

        // check
        env.aic_agent.m_tkn_mng_aic_ref_model.compare_expected_and_observed();

        #20us;

        aic_cons_seq.start(null);

        #10us;
        `uvm_info("run_phase", "Exiting...", UVM_LOW)
        phase.drop_objection(this);
    endtask: run_phase


endclass

`endif // GUARD_TKN_MNG_LOC_DEV_TEST_SV
