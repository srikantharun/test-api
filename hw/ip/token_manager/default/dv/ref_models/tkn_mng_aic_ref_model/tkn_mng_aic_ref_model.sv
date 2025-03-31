// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token Manager Reference Model
//              Implementation.
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>
// Author: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef GUARD_TKN_MNG_AIC_REF_MODEL_SV
`define GUARD_TKN_MNG_AIC_REF_MODEL_SV

`uvm_analysis_imp_decl(_expected_aimp)

class tkn_mng_aic_ref_model extends uvm_monitor;
    `uvm_component_utils(tkn_mng_aic_ref_model)

    uvm_tlm_analysis_fifo#(token_agent_seq_item) token_fifos[string];

    uvm_analysis_imp_expected_aimp#(token_agent_seq_item, tkn_mng_aic_ref_model) expected_aimp;

    tkn_mng_aic_ref_model_cfg m_cfg_h;


    protected semaphore     observed_counter_sem;

    // this has a weird logic, when something is produced, the cons direction is increased!!!
    int observed_counter[string];
    int expected_counter[string];
    bit m_refmodel_en =  1; // only disable in non-functional tests like random axi txns

    function new (string name, uvm_component parent);
        super.new (name, parent);
        observed_counter_sem = new(1);
        expected_aimp = new("expected_aimp", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        if(!uvm_config_db#(tkn_mng_aic_ref_model_cfg)::get(this, "", "cfg", m_cfg_h)) begin
            `uvm_fatal(get_full_name(), "Failed to get cfg from config_db")
        end else begin
            foreach (m_cfg_h.m_connections[i]) begin
                token_fifos[m_cfg_h.m_connections[i]] = new ($sformatf("token_fifo_%0d", i), this);
            end
        end

    endfunction

    // set the observed and expected counters to 0
    function void reset_model();
        foreach(observed_counter[i]) begin
            observed_counter[i] = 0;
        end
        foreach(expected_counter[i]) begin
            expected_counter[i] = 0;
        end
    endfunction

    // set the observed and expected counters to a specific value
    function void set_counter(string connection, bit[7:0] val);
        string token_source;
        string token_destination;

        token_source = m_cfg_h.get_token_source(connection);
        token_destination = m_cfg_h.get_token_destination(connection);
        observed_counter[$sformatf("%s_to_%s", token_source, token_destination)] = val;
        expected_counter[$sformatf("%s_to_%s", token_source, token_destination)] = val;
        `uvm_info(get_name(), $sformatf("Setting counter for observed_counter[%s_to_%s] to %0d done", token_source, token_destination, val), UVM_DEBUG)
    endfunction

    // count the token for prod and consumed based on the OBSERVED tokens
    task check_observed_token_generation(bit is_producer, string src, string dst);
        observed_counter_sem.get();
        if (is_producer) begin
            // token prod count tracking
            if (observed_counter[$sformatf("%s_to_%s", dst, src)] + 1 > TOKEN_MGR_COUNTER_SATURATION_VALUE) begin
                `uvm_error(get_name(), $sformatf("Producer count overflow! %s_to_%s: %0d", src, dst, observed_counter[$sformatf("%s_to_%s", src, dst)]))
            end else begin
                observed_counter[$sformatf("%s_to_%s", dst, src)] += 1;
                `uvm_info(get_name(), $sformatf("Producer count went up! %s_to_%s: %0d", dst, src, observed_counter[$sformatf("%s_to_%s", dst, src)]), UVM_LOW)
            end
        end else begin
            // token cons count tracking
            if (observed_counter[$sformatf("%s_to_%s", src, dst)] < 0) begin
                `uvm_error(get_name(), $sformatf("Producer count went negative! %s_to_%s: %0d", src, dst, observed_counter[$sformatf("%s_to_%s", src, dst)]))
            end else begin
                observed_counter[$sformatf("%s_to_%s", src, dst)] -= 1;
                `uvm_info(get_name(), $sformatf("Producer count went down! %s_to_%s: %0d", src, dst, observed_counter[$sformatf("%s_to_%s", src, dst)]), UVM_LOW)
            end
        end
        observed_counter_sem.put();
    endtask

    // count the token for prod and consumed based on the EXPECTED tokens
    function void check_expected_token_generation(bit is_producer, string src, string dst);
        if (is_producer) begin
            // token prod count tracking
            if (expected_counter[$sformatf("%s_to_%s", dst, src)] + 1 > TOKEN_MGR_COUNTER_SATURATION_VALUE) begin
                `uvm_info(get_name(), $sformatf("TB is issuing producer count overflow! Expect an IRQ %s_to_%s: %0d", src, dst, expected_counter[$sformatf("%s_to_%s", src, dst)]), UVM_LOW)
            end else begin
                expected_counter[$sformatf("%s_to_%s", dst, src)] += 1;
            end
            `uvm_info(get_name(), $sformatf("EXPECTED LOG: Producer Count Up! %s_to_%s: %0d", dst, src, expected_counter[$sformatf("%s_to_%s", dst, src)]), UVM_DEBUG)
        end else begin
            // token cons count tracking
            if (expected_counter[$sformatf("%s_to_%s", src, dst)] + 1 < 0) begin
                `uvm_info(get_name(), $sformatf("TB is issuing negative producer count! %s_to_%s: %0d", src, dst, expected_counter[$sformatf("%s_to_%s", src, dst)]), UVM_LOW)
            end else begin
                expected_counter[$sformatf("%s_to_%s", src, dst)] -= 1;
            end
            `uvm_info(get_name(), $sformatf("EXPECTED LOG: Producer Count Down! %s_to_%s: %0d", src, dst, expected_counter[$sformatf("%s_to_%s", src, dst)]), UVM_DEBUG)
        end
    endfunction

    // return the expected tokens, used to calculate if a consumed sequence can be issued on that path
    // we use the expected token here because there might be delay between expected and observed, meaning the decision made on observed might be wrong
    function int check_token_balance(string connection);
        string token_source;
        string token_destination;
        token_source = m_cfg_h.get_token_source(connection);
        token_destination = m_cfg_h.get_token_destination(connection);


        `uvm_info(get_name(), $sformatf("Checking balance: balance[%s_to_%s] = %0d", token_source, token_destination, expected_counter[$sformatf("%s_to_%s", token_source, token_destination)]), UVM_DEBUG)
        return expected_counter[$sformatf("%s_to_%s", token_source, token_destination)];

    endfunction

    // check that the observed and expected counter match!!!!
    virtual function void check_phase(uvm_phase phase);
        super.check_phase(phase);

        if(!compare_expected_and_observed())
            `uvm_error(get_name(), $sformatf("Final check: TB issue, not checks performed!"))


        // check that the observed counter reached 0 is wanted
        if(m_cfg_h.cosume_all_tokens) begin
            foreach (observed_counter[path]) begin
                if(observed_counter[path] == 0) begin
                    `uvm_info(get_name(), $sformatf("Final check: observed counter is 0!\n on path: %0s observed: %0d expected: %0d", path, observed_counter[path], expected_counter[path]), UVM_DEBUG)
                end else begin
                    `uvm_error(get_name(), $sformatf("Final check: observed counter is not 0!\n on path: %0s observed: %0d expected: %0d", path, observed_counter[path], expected_counter[path]))
                end
            end
        end
    endfunction

    // check if observed and expected are equal, return 1 if at least 1 check was performed
    function bit compare_expected_and_observed();
        bit checked = 0;
        foreach (observed_counter[path]) begin
            if(observed_counter[path] == expected_counter[path]) begin
                `uvm_info(get_name(), $sformatf("Check: observed counter matches the expected one!\n on path: %0s observed: %0d expected: %0d", path, observed_counter[path], expected_counter[path]), UVM_DEBUG)
                checked = 1;
            end else begin
                `uvm_error(get_name(), $sformatf("Check: observed counter doesn't match the expected one!\n on path: %0s observed: %0d expected: %0d", path, observed_counter[path], expected_counter[path]))
            end
        end
        return checked;
    endfunction

    // this func calls the check_observed_token_generation for every connection when the fifo has an element
    virtual task sample_tokens(string connection);
        token_agent_seq_item token_item;
        string token_source;
        string token_destination;
        bit is_producer;
        forever begin
            token_fifos[connection].get(token_item);
            token_source = m_cfg_h.get_token_source(token_item.m_tok_path_name);
            token_destination = m_cfg_h.get_token_destination(token_item.m_tok_path_name);
            is_producer = (token_item.m_type_enm == TOK_PROD_MON)? 1: 0;
            check_observed_token_generation(is_producer, token_source, token_destination);
            `uvm_info(get_name(), $sformatf("Got token[%s] from %s to %s item: %s", connection, token_source, token_destination, token_item.convert2string()), UVM_DEBUG)
        end
    endtask


    // run phase, forks on the sample
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        if (m_refmodel_en) begin
        fork
            begin
            foreach (token_fifos[conn]) begin
                automatic string a_conn = conn;
                fork
                sample_tokens(a_conn);
                join_none
            end
            end
        join
        end
    endtask


    // ap write func for expected tokens, it's called by the sequence
    virtual function void write_expected_aimp(token_agent_seq_item item);
        string token_source;
        string token_destination;
        bit is_producer;

        token_source = m_cfg_h.get_token_source(item.m_tok_path_name);
        token_destination = m_cfg_h.get_token_destination(item.m_tok_path_name);
        is_producer = (item.m_type_enm == TOK_PROD_MON)? 1: 0;
        check_expected_token_generation(is_producer, token_source, token_destination);

        `uvm_info(get_name(), $sformatf("write_expected_aimp:"), UVM_DEBUG)
        `uvm_info(get_name(), $sformatf("from %s to %s item: %s", token_source, token_destination, item.convert2string()), UVM_DEBUG)
    endfunction


endclass

`endif //GUARD_TKN_MNG_AIC_REF_MODEL_SV

