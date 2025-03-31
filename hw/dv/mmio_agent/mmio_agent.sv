`ifndef MMIO_AGENT_SV
`define MMIO_AGENT_SV

// MMIO agents. sets up the mmio env. addr/data width parameters required as those change between DMC/RVV
class mmio_agent#(int DATA_WIDTH = 512, int ADDR_WIDTH = 22) extends uvm_agent;
  `uvm_component_param_utils(mmio_agent#(DATA_WIDTH, ADDR_WIDTH))

  mmio_config      m_cfg;
  mmio_monitor#(DATA_WIDTH, ADDR_WIDTH)     m_mon;
  mmio_scoreboard#(DATA_WIDTH, ADDR_WIDTH)  m_scb;

  virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH)  m_vif;

  int          m_has_scoreboard;
  int unsigned banks_num;
  int unsigned sub_banks_num;
  string       m_memory_path;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //create configuration
    if ( ! uvm_config_db#( mmio_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "m_cfg" ), .value( m_cfg ) ) ) begin
      `uvm_info(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db and so, the default configuration will be created and used (all active)"), UVM_HIGH)
      m_cfg = mmio_config::type_id::create("m_cfg",this);
    end else begin
      `uvm_info(get_full_name(), "Got configuration!", UVM_HIGH)
    end
    //setting configuration to objects below agent
    uvm_config_db#( mmio_config )::set( .cntxt( this ), .inst_name( "*" ), .field_name( "m_cfg" ), .value( m_cfg ) );
    //create monitor
    m_mon = mmio_monitor#(DATA_WIDTH, ADDR_WIDTH)::type_id::create("m_mon",this);
    // In case of RVV mmio connections, we add a scoreboard to make sure that every request has a response
    if (m_cfg.m_has_scoreboard) begin
      m_scb = mmio_scoreboard#(DATA_WIDTH, ADDR_WIDTH)::type_id::create("m_scb",this);
    end

    //verify if the interface can be got through the config db
    if(!uvm_config_db#(virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH))::get(this, "", "vif", m_vif)) begin
      `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
    end
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    m_mon.m_vif = m_vif;
    // In case of RVV, connect monitor to scoreboard
    if (m_cfg.m_has_scoreboard) begin
      m_mon.scb_ap.connect(m_scb.mmio_item_tfifo.analysis_export);
    end
  endfunction

endclass

`endif // MMIO_AGENT_SV


