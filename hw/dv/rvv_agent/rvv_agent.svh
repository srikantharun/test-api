`ifndef RVV_AGENT_SV
`define RVV_AGENT_SV

// RVV agent. starts up the whole RVV environemnt, including the MMIOs under it. data width and addr width are passed from above, as in MMIO those change depending on RVV/DMC
class rvv_agent#(int DATA_WIDTH = 128, int ADDR_WIDTH = 22) extends uvm_agent;
  `uvm_component_param_utils(rvv_agent#(DATA_WIDTH, ADDR_WIDTH))

  rvv_config                              m_rvv_cfg;
  mmio_config                             m_mmio_cfg;
  mmio_agent#(DATA_WIDTH, ADDR_WIDTH)     m_mmio_agents[];
  rvv_monitor#(DATA_WIDTH, ADDR_WIDTH)    m_rvv_mon;
  rvv_driver#(DATA_WIDTH, ADDR_WIDTH)     m_rvv_driver; // Placeholder
  rvv_sequencer#(DATA_WIDTH, ADDR_WIDTH)  m_rvv_sequencer; // Placeholder

  // mmio_interfaces
  virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH)  m_mmio_vif[];

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //create configuration
    if ( ! uvm_config_db#( rvv_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "m_rvv_cfg" ), .value( m_rvv_cfg ) ) ) begin
      `uvm_info(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db and so, the default configuration will be created and used (all active)"), UVM_MEDIUM)
      m_rvv_cfg = rvv_config::type_id::create("m_rvv_cfg",this);
      // in case rvv cfg was not passed, setting default values
      m_rvv_cfg.set_defaults();
    end else begin
      `uvm_info(get_full_name(), "Got configuration!", UVM_MEDIUM)
    end
    //setting configuration to objects below agent
    uvm_config_db#( rvv_config )::set( .cntxt( this ), .inst_name( "*" ), .field_name( "m_rvv_cfg" ), .value( m_rvv_cfg ) );
    // Setting up mmio configs based on RVV config. it's the same config for all of the mmio ports.
    m_mmio_cfg = mmio_config::type_id::create("m_cfg",this);
    m_mmio_cfg.m_has_scoreboard = m_rvv_cfg.m_has_scoreboard;
    m_mmio_cfg.banks_num        = m_rvv_cfg.banks_num;
    m_mmio_cfg.sub_banks_num    = m_rvv_cfg.sub_banks_num;
    m_mmio_cfg.m_memory_path    = m_rvv_cfg.m_memory_path;
    uvm_config_db#( mmio_config )::set( .cntxt( this ), .inst_name( "*" ), .field_name( "m_cfg" ), .value( m_mmio_cfg ) );
        
    // Instantiate mmio agents and create the virtual interface
    m_mmio_agents = new[m_rvv_cfg.connections_num];
    m_mmio_vif = new[m_rvv_cfg.connections_num];
    for (int i = 0; i < m_rvv_cfg.connections_num; i++) begin
      //verify if the interface can be got through the config db
      if (!uvm_config_db#(virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH))::get(this, "", $sformatf("m_mmio_vif_%0d", i), m_mmio_vif[i])) begin
        `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
      end
      m_mmio_agents[i] = mmio_agent#(DATA_WIDTH, ADDR_WIDTH)::type_id::create($sformatf("m_mmio_agent_%0d", i), this);
      uvm_config_db#(virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH))::set( .cntxt( this ), .inst_name( $sformatf("m_mmio_agent_%0d", i )), .field_name( "vif" ), .value( m_mmio_vif[i] ) );
    end

    //Instantiate monitor, driver, sequencer
    m_rvv_mon       = rvv_monitor#(DATA_WIDTH, ADDR_WIDTH)::type_id::create("m_rvv_monitor", this);
    m_rvv_driver    = rvv_driver#(DATA_WIDTH, ADDR_WIDTH)::type_id::create("m_rvv_driver", this);
    m_rvv_sequencer = rvv_sequencer#(DATA_WIDTH, ADDR_WIDTH)::type_id::create("m_rvv_sequencer", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    //connect interfaces to monitor and driver
    for (int i = 0; i < m_rvv_cfg.connections_num; i++) begin
      m_rvv_mon.m_mmio_vif[i]       = m_mmio_vif[i];
      m_rvv_driver.m_mmio_vif[i]    = m_mmio_vif[i];
      m_rvv_sequencer.m_mmio_vif[i] = m_mmio_vif[i];
    end        
    // Connect the sequencer to the driver
    m_rvv_driver.seq_item_port.connect(m_rvv_sequencer.seq_item_export);
  endfunction

endclass

`endif // RVV_AGENT_SV


