// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: prod sequence for debug, it only set drive prod to 1
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>

`ifndef GUARD_TKN_MNG_AIC_PROD_SEQUENCE_SVH
`define GUARD_TKN_MNG_AIC_PROD_SEQUENCE_SVH

class tkn_mng_aic_prod_sequence extends uvm_sequence;

    `uvm_object_utils(tkn_mng_aic_prod_sequence)

    tkn_mng_aic_agent               aic_agent;

    token_agent_prod_sequence       tok_prod_seq[];

    string                          tok_connections[$];
    string                          tok_prod_connections[$];

    rand int                        num_of_prod;

    token_agent_seq_item            tmp_item;



    constraint c_reasonable_num_of_prod {
        num_of_prod > 1;
        num_of_prod < 100;
    }

    function new(string name = "");
        super.new(name);
    endfunction : new

    task pre_body();
        // raise objection if started as a root sequence
        if(starting_phase != null)
            starting_phase.raise_objection(this);


        tok_prod_seq = new[num_of_prod];
        foreach(tok_prod_seq[i]) begin
            tok_prod_seq[i]  = token_agent_prod_sequence::type_id::create($sformatf("tok_prod_seq_%0d", i));
        end

    endtask

    task post_body();
        // drop objection if started as a root sequence
        if(starting_phase != null)
        starting_phase.drop_objection(this);
    endtask

    task body();
        string tok_connection_selected;

        tok_connections = aic_agent.get_token_agents_connections;

        foreach(tok_prod_seq[i]) begin
            tmp_item = token_agent_seq_item::type_id::create("tmp_item");
            tok_connection_selected = tok_connections[$urandom_range(tok_connections.size()-1, 0)];
            tok_prod_connections.push_back(tok_connection_selected);

            tmp_item.m_bv_delay = 0;
            tmp_item.m_tok_value = 0;
            tmp_item.m_type_enm = TOK_PROD_MON;
            tmp_item.m_tok_path_name = tok_connection_selected;
            aic_agent.m_tkn_mng_aic_seqr.expected_aport.write(tmp_item);


            `uvm_info(get_full_name(), $sformatf("PROD SEQ: selected connection: %s , on seq #%0d with tok_connections size %0d", tok_connection_selected, i, tok_connections.size()), UVM_DEBUG)
            tok_prod_seq[i].start(aic_agent.m_token_agents[tok_connection_selected].m_tok_seqr);
        end


        `uvm_info(get_full_name(), $sformatf("PROD SEQ: used connection: %p", tok_prod_connections), UVM_DEBUG)

    endtask : body

endclass : tkn_mng_aic_prod_sequence

`endif // GUARD_TKN_MNG_AIC_PROD_SEQUENCE_SVH
