//
// File: lpddr_subsystem_environment.svh
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
`include "uvm_macros.svh"
class lpddr_subsystem_environment
#(
    string UNIQUE_ID = ""
) extends uvmf_environment_base #(.CONFIG_T(lpddr_subsystem_env_configuration));
    `uvm_component_param_utils(lpddr_subsystem_environment #(UNIQUE_ID))

    // Agent handles
    apb_master_0_agent_t apb_master_0;
    apb_master_1_agent_t apb_master_1;
    axi4_master_0_agent_t axi4_master_0;

		// virtual sequencer
		lpddr_subsystem_virtual_sequencer virtual_sequencer;
    
    // RAL associated
    lpddr_subsystem_apb_reg_block reg_model;
    reg2apb_adapter_t reg2apb;
    apb_reg_predictor_t reg_predictor;

    // It samples the SDRAM interface to generate the tracker file
    // with different timing parameters configured such as clock jitter and skew.
    // The DDR/LPDDR monitor to dump command and data activities appeared 
    // on the DDR/LPDDR interface.
    addr_monitor        ddr_monitor;
    addr_monitor        ddr_monitorB;

    //Predictor
    lpddr_subsystem_reference_model lpddr_predictor;

    //Scoreboard
    lpddr_subsystem_scoreboard lpddr_scoreboard;

    //Coverage Collector
    lpddr_subsystem_coverage_collector lpddr_coverage_collector;

    // Analysis exports
    uvm_analysis_export #(amem_command_class)   ddrmon_rw_export;
    uvm_analysis_export #(amem_command_class)   ddrmon_nonrw_export;
    // TLM FIFOs
    uvm_tlm_analysis_fifo #(amem_command_class) ddrmon_rw_fifo;
    uvm_tlm_analysis_fifo #(amem_command_class) ddrmon_nonrw_fifo;

    function new
    (
        string name = "lpddr_subsystem_environment",
        uvm_component parent = null
    );
        super.new(name, parent);
        
    endfunction
    
    extern function void build_phase
    (
        uvm_phase phase
    );
    
    extern function void connect_phase
    (
        uvm_phase phase
    );
    
endclass: lpddr_subsystem_environment

function void lpddr_subsystem_environment::build_phase
(
    uvm_phase phase
);
    apb_master_0 = apb_master_0_agent_t::type_id::create("apb_master_0", this );
    apb_master_0.set_mvc_config(configuration.apb_master_0_cfg);

    apb_master_1 = apb_master_1_agent_t::type_id::create("apb_master_1", this );
    apb_master_1.set_mvc_config(configuration.apb_master_1_cfg);
    
    axi4_master_0 = axi4_master_0_agent_t::type_id::create("axi4_master_0", this );
    axi4_master_0.set_mvc_config(configuration.axi4_master_0_cfg);

    if(!uvm_config_db#(addr_monitor)::get(this,"","ddr_monitorA",ddr_monitor)) begin
      `uvm_fatal("Config Error","uvm_config_db #(addr_monitor)::get cannot find resource 'ddr_monitor'")
  	end
    if(!uvm_config_db#(addr_monitor)::get(this,"","ddr_monitorB",ddr_monitorB)) begin
      `uvm_fatal("Config Error","uvm_config_db #(addr_monitor)::get cannot find resource 'ddr_monitorB'")
  	end
    ddrmon_rw_export= new("ddrmon_rw_export", this);
    ddrmon_rw_fifo  = new("ddrmon_rw_fifo", this);
    ddrmon_nonrw_export= new("ddrmon_nonrw_export", this);
    ddrmon_nonrw_fifo  = new("ddrmon_nonrw_fifo", this);

    //Create LPDDR Predictor
    lpddr_predictor = lpddr_subsystem_reference_model::type_id::create("lpddr_predictor", this);

    //Create LPDDR Scoreboard
    lpddr_scoreboard = lpddr_subsystem_scoreboard::type_id::create("lpddr_scoreboard", this);

    //Create LPDDR Coverage Collector
    lpddr_coverage_collector = lpddr_subsystem_coverage_collector::type_id::create("lpddr_coverage_collector", this);

    //apb2reg_predictor = new("apb2reg_predictor",this);
    reg_model=lpddr_subsystem_apb_reg_block::type_id::create("reg_model");
    reg_model.build();
    reg_model.reset();
    reg_model.lock_model();
    reg_model.print();

    // Create register adapter
    reg2apb = reg2apb_adapter_t::type_id::create("reg2apb");
    //reg2apb.en_addr_map = 1; TODO
    reg2apb.is_apb4 = 1; // For APB4
    reg2apb.supports_byte_enable = 1;

    // Create register predictor
    reg_predictor = apb_reg_predictor_t::type_id::create("reg_predictor", this);
    uvm_config_db#(lpddr_subsystem_apb_reg_block)::set(uvm_root::get(),"*","reg_model",reg_model);

		//create virtual_sequencer
    virtual_sequencer = lpddr_subsystem_virtual_sequencer::type_id::create("virtual_sequencer", this);

    uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"apb_master_0"},apb_master_0.m_sequencer);
    uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"apb_master_1"},apb_master_1.m_sequencer);
    //uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"axi4_master_0"},axi4_master_0.m_sequencer);
   // uvm_config_db #(lpddr_subsystem_virtual_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"p_sequencer"},virtual_sequencer);

endfunction: build_phase

function void lpddr_subsystem_environment::connect_phase
(
    uvm_phase phase
);
    uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"apb_master_0"},apb_master_0.m_sequencer);
    uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"apb_master_1"},apb_master_1.m_sequencer);
    uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"axi4_master_0"},axi4_master_0.m_sequencer);
    uvm_config_db #(lpddr_subsystem_virtual_sequencer)::set(null,UVMF_SEQUENCERS,{UNIQUE_ID,"p_sequencer"},virtual_sequencer);

    // direct connection to bus VIP
    reg_model.default_map.set_sequencer(apb_master_0.m_sequencer,reg2apb);

    reg_model.default_map.set_auto_predict(0);

    reg_predictor.map     = reg_model.default_map;
    reg_predictor.adapter = reg2apb;

    // Connect the predictor to the bus agent monitor analysis port
    apb_master_0.ap["trans_ap"].connect(reg_predictor.bus_item_export);

    ddr_monitor.rw_cmd_port.connect(ddrmon_rw_export);
    ddrmon_rw_export.connect( ddrmon_rw_fifo.analysis_export);
    ddr_monitor.nonrw_cmd_port.connect(ddrmon_nonrw_export);
    ddrmon_nonrw_export.connect( ddrmon_nonrw_fifo.analysis_export);
		//virtual_sequencer.env = this;
		//virtual_sequencer.connect(axi4_master_0.m_sequencer);

    //Connect Monitor to Predictor/scoreboard
    axi4_master_0.ap["trans_ap"].connect(lpddr_predictor.axi_analysis_port);
    ddr_monitor.rw_cmd_port.connect(lpddr_scoreboard.lpddr_act_rw_export);
    ddr_monitor.nonrw_cmd_port.connect(lpddr_scoreboard.lpddr_act_nonrw_export);
 
    //Connect predictor to scoreboard
    lpddr_predictor.exp_lpddr_port.connect(lpddr_scoreboard.lpddr_exp_export);

    //Connect AXI Agent to coverage collector
    axi4_master_0.ap["trans_ap"].connect(lpddr_coverage_collector.analysis_port_axi);
endfunction: connect_phase
