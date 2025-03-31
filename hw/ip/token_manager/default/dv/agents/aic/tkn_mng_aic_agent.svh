// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Agent, no particular configs needed
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>

`ifndef TKN_MNG_AIC_AGENT_SV
`define TKN_MNG_AIC_AGENT_SV

class tkn_mng_aic_agent extends uvm_agent;
    `uvm_component_utils(tkn_mng_aic_agent)

    /** Token manager interface agent */
    token_agent                 m_token_agents[string];
    token_agent_config          m_token_agents_cfg[string];

    tkn_mng_aic_ref_model       m_tkn_mng_aic_ref_model;
    tkn_mng_aic_ref_model_cfg   m_tkn_mng_aic_ref_model_cfg;

    tkn_mng_aic_sequencer       m_tkn_mng_aic_seqr;

    function new (string name, uvm_component parent);
        super.new (name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        build_token_mgrs();

    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        foreach (m_token_agents[connection]) begin
            //IF changes
            m_token_agents[connection].m_tok_mon.ap.connect(m_tkn_mng_aic_ref_model.token_fifos[connection].analysis_export);
        end

        m_tkn_mng_aic_seqr.expected_aport.connect(m_tkn_mng_aic_ref_model.expected_aimp);
    endfunction


    // Start of simulation phase
    function void start_of_simulation_phase (uvm_phase phase);
        string token_connection_name;
        TB_TKN_MNG_AIC_DEV_ENUM current_device;

        foreach(m_token_agents_cfg[token_connection_name]) begin
            m_tkn_mng_aic_ref_model.set_counter(token_connection_name, 0);
        end

    endfunction: start_of_simulation_phase



    virtual function void build_token_mgrs();
        string token_connection_name;
        TB_TKN_MNG_AIC_DEV_ENUM current_device;


        `uvm_info(get_name(), $sformatf("inside token function ...."), UVM_LOW)

        m_tkn_mng_aic_ref_model_cfg = tkn_mng_aic_ref_model_cfg::type_id::create("m_tkn_mng_aic_ref_model_cfg");
        m_tkn_mng_aic_ref_model     = tkn_mng_aic_ref_model::type_id::create("m_tkn_mng_aic_ref_model", this);

        // sequencer
        m_tkn_mng_aic_seqr = tkn_mng_aic_sequencer::type_id::create("m_tkn_mng_aic_seqr", this);

        uvm_config_db#(tkn_mng_aic_ref_model_cfg)::set(this, "m_tkn_mng_aic_ref_model", "cfg", m_tkn_mng_aic_ref_model_cfg);

        // dev
        // start from 1, we avoid swep/acd to itself
        for(int i = 1; i< $size(DV_TKN_MNG_AIC_CONN_NUM); i++) begin
            current_device = i;
            for(int j = 0; j < DV_TKN_MNG_AIC_CONN_NUM[i]; j++) begin
                //create token agent configurations
                token_connection_name = {current_device.name(), "_TO_", TKN_MNG_AIC_PROD_MAP[j][i].name()};
                m_token_agents_cfg[token_connection_name.tolower()] = token_agent_config::type_id::create(token_connection_name.tolower());
                m_token_agents_cfg[token_connection_name.tolower()].m_b_active = 1;
                m_token_agents_cfg[token_connection_name.tolower()].m_type = TOK_AGT_SLAVE;

                //setting configuration to objects below agent
                uvm_config_db#(token_agent_config)::set(.cntxt(this), .inst_name(token_connection_name.tolower()), .field_name( "tok_agt_cfg" ), .value(m_token_agents_cfg[token_connection_name.tolower()]));
                m_token_agents[token_connection_name.tolower()] = token_agent::type_id::create(token_connection_name.tolower(), this);

                //REF MODEL CONFIG
                m_tkn_mng_aic_ref_model_cfg.add_connection(token_connection_name.tolower());
            end
        end

        // acd
        for(int i = 1; i < DV_TKN_MNG_AIC_ACD_CONN_NUM; i++) begin
            current_device = TB_TKN_MNG_AIC_DEV_ENUM'(i);
            //create token agent configurations
            token_connection_name = {"SWEP_OR_ACD", "_TO_", current_device.name()};
            m_token_agents_cfg[token_connection_name.tolower()] = token_agent_config::type_id::create(token_connection_name.tolower());
            m_token_agents_cfg[token_connection_name.tolower()].m_b_active = 1;
            m_token_agents_cfg[token_connection_name.tolower()].m_type = TOK_AGT_SLAVE;


            //setting configuration to objects below agent
            uvm_config_db#(token_agent_config)::set(.cntxt(this), .inst_name(token_connection_name.tolower()), .field_name( "tok_agt_cfg" ), .value(m_token_agents_cfg[token_connection_name.tolower()]));
            m_token_agents[token_connection_name.tolower()] = token_agent::type_id::create(token_connection_name.tolower(), this);

            //REF MODEL CONFIG
            m_tkn_mng_aic_ref_model_cfg.add_connection(token_connection_name.tolower());
        end

    endfunction


    function qstring get_token_agents_connections();
        string m_qstring[$];
        foreach(m_token_agents[i])
            m_qstring.push_back(i);


        return m_qstring;
    endfunction


endclass

`endif


