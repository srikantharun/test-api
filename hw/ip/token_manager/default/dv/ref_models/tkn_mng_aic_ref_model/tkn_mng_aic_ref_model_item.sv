// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token Manager Reference Model
//              Implementation.
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>
// Author: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef TKN_MNG_AIC_REF_MODEL_ITEM_SV
`define TKN_MNG_AIC_REF_MODEL_ITEM_SV

class tkn_mng_aic_ref_model_item extends uvm_sequence_item;
    `uvm_object_utils(tkn_mng_aic_ref_model_item)

    typedef tkn_mng_aic_ref_model_cfg tkn_mgr_aic_ref_model_cfg_t;

    tkn_mgr_aic_ref_model_cfg_t m_cfg_h;
    rand token_mgr_prod_action_t m_prod_actions[$];
    rand token_mgr_cons_action_t m_cons_actions[$];
    rand bit m_use_swep;

    protected int unsigned m_reverse_connection_index_q[$];

    // for debug
    string m_prod_list[string][$];
    string m_cons_list[string][$];
    protected string m_cons_chain[$];

    constraint C_USE_SWEP_DEFAULT {
        soft m_use_swep == 0; // do not use by default
    }

    constraint C_ACTION_SIZE {
        soft m_prod_actions.size() == m_cfg_h.m_connections.size();
        soft m_cons_actions.size() == m_cfg_h.m_connections.size();
    }

    constraint C_DEVICE_ACTION {
        foreach (m_prod_actions[i]) {
            (m_reverse_connection_index_q[i] != -1 && m_prod_actions[i] == PRODUCE) -> soft  (m_cons_actions[m_reverse_connection_index_q[i]] inside {CONSUME, CONS_NONE});
            (m_reverse_connection_index_q[i] != -1 && m_prod_actions[i] == PROD_NONE) -> soft  (m_cons_actions[m_reverse_connection_index_q[i]] == CONS_NONE);
            (m_prod_actions[i]== PRODUCE) -> soft (m_cons_actions[i] == CONS_NONE); // do not consume when same line/connection when you are the producer!
        }
    }

    constraint C_SWEP_ACTION {
        foreach (m_prod_actions[i]) {
            // SWEP Disable
            (m_reverse_connection_index_q[i] == -1 && m_use_swep == 0) -> soft m_prod_actions[i] == PROD_NONE;
            (m_reverse_connection_index_q[i] == -1 && m_use_swep == 0) -> soft m_cons_actions[i] == CONS_NONE;
            // SWEP Enable
            (m_reverse_connection_index_q[i] == -1 && m_use_swep == 1) -> soft m_prod_actions[i] dist { PRODUCE:= 80, PROD_NONE:=20};
            (m_reverse_connection_index_q[i] == -1 && m_use_swep == 1) -> soft m_cons_actions[i] dist { CONSUME:= 80, CONS_NONE:=20};
            (m_reverse_connection_index_q[i] != -1 && m_use_swep == 1) -> soft m_prod_actions[i] == PROD_NONE; // Do not use other token by default
            (m_reverse_connection_index_q[i] != -1 && m_use_swep == 1) -> soft m_cons_actions[i] == CONS_NONE; // Do not use other token by default
        }
    }

    constraint C_SOLVER {
        solve m_prod_actions before m_cons_actions;
        solve m_use_swep before m_prod_actions;
    }

    function new (string name = "tkn_mng_aic_ref_model_item");
        super.new (name);
    endfunction

    virtual function tkn_mng_aic_ref_model_item do_clone();
        tkn_mng_aic_ref_model_item item;
        if(!$cast(item, this.clone()))
            `uvm_fatal(get_full_name(), "Clone failed")
        return item;
    endfunction

    virtual function void do_copy(uvm_object rhs);
        tkn_mng_aic_ref_model_item seq_rhs;
        if(rhs == null) begin
            `uvm_fatal(get_full_name(), "do_copy from null ptr");
        end

        if(!$cast(seq_rhs, rhs)) begin
            `uvm_fatal(get_full_name(), "do_copy cast failed");
        end

        super.do_copy(rhs);
        foreach (seq_rhs.m_prod_actions[i]) begin
            this.m_prod_actions[i] = seq_rhs.m_prod_actions[i] ;
        end
    endfunction : do_copy

    function void pre_randomize();
        string src, dst;
        int reversed_indx;
        if (!uvm_config_db #(tkn_mgr_aic_ref_model_cfg_t)::get(null, "", "AI_CORE_LS_TKN_MGR_CFG", m_cfg_h)) begin
            `uvm_fatal(get_name(), "Unable to get AI_CORE_LS_ENV")
        end
        foreach (m_cfg_h.m_connections[i]) begin
            m_prod_actions.push_back(PROD_NONE); // initialize
            m_cons_actions.push_back(CONS_NONE); // initialize
            src = m_cfg_h.get_token_source(m_cfg_h.m_connections[i]);
            dst = m_cfg_h.get_token_destination(m_cfg_h.m_connections[i]);
            reversed_indx = find_reverse_path_index(src, dst);
            m_reverse_connection_index_q.push_back(reversed_indx);
            `uvm_info(get_name(), $sformatf("Src: %s Dst: %s \n Unreversed: %s Reversed: %s \n index: %0d reversed index: %0d", src, dst, m_cfg_h.m_connections[i], {m_cfg_h.m_path_prefix, dst, m_cfg_h.m_connector, src}, i, reversed_indx), UVM_DEBUG)
        end
    endfunction

    function void post_randomize();
        string src, dst;
        int reversed_indx;
        bit has_dep;

        foreach (m_cfg_h.m_connections[i]) begin
            src = m_cfg_h.get_token_source(m_cfg_h.m_connections[i]);
            dst = m_cfg_h.get_token_destination(m_cfg_h.m_connections[i]);
            if (m_prod_actions[i] == PRODUCE) begin
                m_prod_list[src].push_back(dst);
            end
            if (m_cons_actions[i] == CONSUME) begin
                m_cons_list[src].push_back(dst);
            end
        end
        foreach (m_prod_list[i]) begin
            `uvm_info(get_name(), $sformatf("DBG- m_prod_list[%s]: %p", i, m_prod_list[i]), UVM_DEBUG)
        end
        repeat (2) begin // the second check is to further guarantee the end result has no cyclic dependency
            foreach (m_cons_list[i]) begin
                `uvm_info(get_name(), $sformatf("DBG- m_cons_list[%s]: %p", i, m_cons_list[i]), UVM_DEBUG)
                m_cons_chain.delete();
                has_dep = has_cyclic_dependencies(i);
                if (has_dep) begin
                    `uvm_info(get_name(), $sformatf("Cyclic Dependency detected! problem within: m_cons_list[%s] %p", i, m_cons_list[i]), UVM_FULL)
                end
            end
        end
    endfunction

    virtual function string convert2string();
        string s = super.convert2string();
        s = {s, $sformatf("\n----------- TOKEN MRG REFMODEL ITEM ----------------") };
        foreach (m_prod_actions[i]) begin
            s = {s, $sformatf("\n Connection name[%0d]: %s %s %s, reversed index: %0d", i, m_cfg_h.m_connections[i], m_prod_actions[i].name, m_cons_actions[i].name, m_reverse_connection_index_q[i])};
        end
        foreach (m_prod_list[i]) begin
            s = {s, $sformatf("\n m_prod_list[%s]: %p", i, m_prod_list[i])};
        end
        foreach (m_cons_list[i]) begin
            s = {s, $sformatf("\n m_cons_list[%s]: %p", i, m_cons_list[i])};
        end
        s = {s, $sformatf("\n---------------------------------------------") };
        return s;
    endfunction : convert2string

    // returns 1 if there is cyclic dependencies
    function bit has_cyclic_dependencies(string src_indx);
        bit has_dep = 0;
        // if the src device has 1 or more consume requirement
        if (m_cons_list[src_indx].size() > 0) begin
            m_cons_chain.push_back(src_indx); // the src itself is its own dependency
            // iterate through required dst to be consumed
            foreach (m_cons_list[src_indx][dst]) begin
                // if it is already inside the list , then there is cyclic dependency
                if (m_cons_list[src_indx][dst] inside {m_cons_chain}) begin
                    `uvm_info(get_name(), $sformatf("Item redundancy- src index %s: dst: %s so entry deleted at index %0d", src_indx, m_cons_list[src_indx][dst], dst), UVM_DEBUG)
                    consume_override(src_indx, m_cons_list[src_indx][dst]);
                    m_cons_list[src_indx].delete(dst);
                    return 1;
                end else begin
                    m_cons_chain.push_back(m_cons_list[src_indx][dst]);
                    `uvm_info(get_name(), $sformatf("Item unique- src index %s: dst: %s", src_indx, m_cons_list[src_indx][dst]), UVM_DEBUG)
                    has_dep = has_dep || has_cyclic_dependencies(m_cons_list[src_indx][dst]); // recursive function!
                end
            end
        end else begin
            // no cyclic dependencies since src does not consume tokens
            `uvm_info(get_name(), $sformatf("Item empty- src index %s:", src_indx), UVM_DEBUG)
            return 0;
        end

        return has_dep;
    endfunction

    function void consume_override(string src, string dst);
        string src_var;
        string dst_var;
        foreach (m_cfg_h.m_connections[i]) begin
            src_var = m_cfg_h.get_token_source(m_cfg_h.m_connections[i]);
            dst_var = m_cfg_h.get_token_destination(m_cfg_h.m_connections[i]);
            if (src_var == src && dst_var == dst) begin
                m_cons_actions[i] = CONS_NONE; // override as this causes cyclic dependencies
                `uvm_info(get_name(), $sformatf("DBG override- src %s: dst: %s overriden to %s (index: %0d)", src, dst, m_cons_actions[i].name(), i), UVM_DEBUG)
                break;
            end
        end
    endfunction


    virtual function int find_reverse_path_index(string src, string dst);
        foreach (m_cfg_h.m_connections[i]) begin
            if (m_cfg_h.m_connections[i] == {m_cfg_h.m_path_prefix, dst, m_cfg_h.m_connector, src}) begin
                return i;
            end
        end
        if (dst == "swep") begin
            return -1; // return negative index since swep is special case (i.e. not a device)
        end else begin
            `uvm_fatal(get_name(), $sformatf("Unable to find reversed token path: %s", {m_cfg_h.m_path_prefix, dst, m_cfg_h.m_connector, src}))
        end
    endfunction



endclass

`endif //TKN_MNG_AIC_REF_MODEL_ITEM_SV
