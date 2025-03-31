// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Sequencer, no special configurations for now
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>
`ifndef GUARD_TKN_MNG_AIC_SEQUENCER_SV
`define GUARD_TKN_MNG_AIC_SEQUENCER_SV

class tkn_mng_aic_sequencer extends uvm_sequencer#(token_agent_seq_item);


    `uvm_component_utils(tkn_mng_aic_sequencer)

    uvm_analysis_port #(token_agent_seq_item) expected_aport;

    function new (string name, uvm_component parent);
        super.new (name, parent);
        expected_aport = new("expected_aport", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

endclass : tkn_mng_aic_sequencer

`endif // GUARD_TKN_MNG_AIC_SEQUENCER_SV
