`ifndef TOKEN_AGENT_SV
`define TOKEN_AGENT_SV

class token_agent extends uvm_agent;
  `uvm_component_utils(token_agent)

  token_agent_config      m_tok_cfg;
  token_agent_monitor     m_tok_mon;
  token_agent_driver      m_tok_drv;
  token_agent_sequencer   m_tok_seqr;
  virtual token_agent_if  m_vif;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //create configuration
    if ( ! uvm_config_db#( token_agent_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "tok_agt_cfg" ), .value( m_tok_cfg ) ) ) begin
      `uvm_info(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db and so, the default configuration will be created and used (all active)"), UVM_HIGH)
      m_tok_cfg = token_agent_config::type_id::create("m_tok_cfg",this);
    end
    //setting configuration to objects below agent
    uvm_config_db#( token_agent_config )::set( .cntxt( this ), .inst_name( "*" ), .field_name( "tok_agt_cfg" ), .value( m_tok_cfg ) );
    //create monitor
    m_tok_mon = token_agent_monitor::type_id::create("m_tok_mon",this);

    //create sequencer and driver if it is an active agent
    if(m_tok_cfg.m_b_active) begin
      m_tok_seqr = token_agent_sequencer::type_id::create("m_tok_seqr",this);
      m_tok_drv = token_agent_driver::type_id::create("m_tok_drv",this);
    end

    //verify if the interface can be got through the config db
    if(!uvm_config_db#(virtual token_agent_if)::get(this, "", "vif", m_vif))
      `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    //connect interfaces to monitor and driver
    m_tok_mon.m_vif = m_vif;
    if(m_tok_cfg.m_b_active) begin
      m_tok_drv.m_vif = m_vif;
      m_tok_seqr.m_vif = m_vif;
    end

    //connect sequencer to driver
    if(m_tok_cfg.m_b_active) begin
      m_tok_drv.seq_item_port.connect(m_tok_seqr.seq_item_export);
    end

  endfunction

endclass

`endif // TOKEN_AGENT_SV


