// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token Manager Configuration
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>
// Author: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef GUARD_TKN_MNG_AIC_REF_MODEL_CFG_SV
`define GUARD_TKN_MNG_AIC_REF_MODEL_CFG_SV

class tkn_mng_aic_ref_model_cfg extends uvm_object;

    `uvm_object_utils(tkn_mng_aic_ref_model_cfg)

    bit    cosume_all_tokens = 0;
    bit    m_refmodel_check_en = 1;
    string m_path_prefix = "";
    string m_connector = "_to_";
    string m_connections[$];
    string m_null_devices[$]; // device not connected except token lines

    function new (string name = "tkn_mng_aic_ref_model_cfg");
        super.new (name);
    endfunction : new

    function void add_connection(string connection);
        if (!(connection inside {m_connections})) begin
            m_connections.push_back(connection);
        end
    endfunction

    function void add_null_devices(string dev);
        if (!(dev inside {m_null_devices})) begin
            m_null_devices.push_back(dev);
        end
    endfunction

    function void reset_connection();
        m_connections.delete();
    endfunction

    function void reset_null_devices();
        m_null_devices.delete();
    endfunction

    // this func finds the string before the "_to_", aka the tkn source
    virtual function string get_token_source(string token_path);
        int match_required = m_connector.len();
        int match_count = 0;
        int index;
        foreach (token_path[i]) begin
            if ((token_path[i]) == m_connector[match_count]) begin
                match_count += 1;
                if (match_count == match_required) begin
                    index = i;
                    break;
                end
            end else begin
                match_count = 0;
            end
        end
        if (match_count != match_required) begin
            `uvm_fatal(get_name(), $sformatf("Cannot find token source! Token path: %s prefix: %s connector: %s ", token_path, m_path_prefix, m_connector));
        end else begin
            return (token_path.substr(m_path_prefix.len(), index-m_connector.len()));
        end
    endfunction

    // this func finds the string after the "_to_", aka the tkn destination
    virtual function string get_token_destination(string token_path);
        int match_required = m_connector.len();
        int match_count = 0;
        int index;
        foreach (token_path[i]) begin
            if ((token_path[i]) == m_connector[match_count]) begin
                match_count += 1;
                if (match_count == match_required) begin
                    index = i;
                    break;
                end
            end else begin
                match_count = 0;
            end
        end
        if (match_count != match_required) begin
            `uvm_fatal(get_name(), $sformatf("Cannot find token destination! Token path: %s prefix: %s connector: %s ", token_path, m_path_prefix, m_connector));
        end else begin
            return (token_path.substr(index+1, token_path.len()-1));
        end
    endfunction

    virtual function string convert2string();
        string s = super.convert2string();
        s = {s, $sformatf("\n-------- TOKEN MGR CFG -------------------") };
        foreach (m_connections[i]) begin
            s = {s, $sformatf("\n  Connection name[%0d]: %s", i, m_connections[i])};
        end
        s = {s, $sformatf("\n---------------------------------------------") };
        return s;
    endfunction : convert2string


endclass : tkn_mng_aic_ref_model_cfg

`endif //GUARD_TKN_MNG_AIC_REF_MODEL_CFG_SV
