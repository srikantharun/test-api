//
// File: lpddr_subsystem_env_configuration.svh
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
class lpddr_subsystem_env_configuration extends uvmf_environment_configuration_base;
    `uvm_object_utils(lpddr_subsystem_env_configuration)
    // Handles for vip config for each of the QVIP instances
    
    apb_master_0_cfg_t apb_master_0_cfg;
    apb_master_1_cfg_t apb_master_1_cfg;
    axi4_master_0_cfg_t axi4_master_0_cfg;
    // Handles for address maps

		bit init_seq_done;
    
    address_map APB_ADDR_MAP;
    address_map AXI_ADDR_MAP;
    
    function new
    (
        string name = "lpddr_subsystem_env_configuration"
    );
        super.new(name);
        apb_master_0_cfg = apb_master_0_cfg_t::type_id::create("apb_master_0_cfg");
        apb_master_1_cfg = apb_master_1_cfg_t::type_id::create("apb_master_1_cfg");
        axi4_master_0_cfg = axi4_master_0_cfg_t::type_id::create("axi4_master_0_cfg");
    endfunction
    
    virtual function string convert2string;
        return {"lpddr_subsystem_env_configuration:",apb_master_0_cfg.convert2string(),apb_master_0_cfg.convert2string(),axi4_master_0_cfg.convert2string()};
    endfunction: convert2string
    
    extern function void initialize
    (
        uvmf_sim_level_t sim_level,
        string environment_path,
        string interface_names[],
        uvm_reg_block register_model = null,
        uvmf_active_passive_t interface_activity[] = {}
    );
    
endclass: lpddr_subsystem_env_configuration

function void lpddr_subsystem_env_configuration::initialize
(
    uvmf_sim_level_t sim_level,
    string environment_path,
    string interface_names[],
    uvm_reg_block register_model = null,
    uvmf_active_passive_t interface_activity[] = {}
);
    super.initialize(sim_level, environment_path, interface_names, register_model, interface_activity);
    
    if ( !uvm_config_db #(apb_master_0_bfm_t)::get( null, "UVMF_VIRTUAL_INTERFACES", interface_names[0], apb_master_0_cfg.m_bfm ) )
    begin
        `uvm_fatal("Config Error", $sformatf("uvm_config_db #(apb_master_0_bfm_t)::get() cannot find bfm vif handle for agent with interface_name '%s'", interface_names[0]))
    end

    if ( !uvm_config_db #(apb_master_1_bfm_t)::get( null, "UVMF_VIRTUAL_INTERFACES", interface_names[2], apb_master_1_cfg.m_bfm ) )
    begin
        `uvm_fatal("Config Error", $sformatf("uvm_config_db #(apb_master_1_bfm_t)::get() cannot find bfm vif handle for agent with interface_name '%s'", interface_names[2]))
    end
    
    if ( !uvm_config_db #(axi4_master_0_bfm_t)::get( null, "UVMF_VIRTUAL_INTERFACES", interface_names[1], axi4_master_0_cfg.m_bfm ) )
    begin
        `uvm_fatal("Config Error", $sformatf("uvm_config_db #(axi4_master_0_bfm_t)::get() cannot find bfm vif handle for agent with interface_name '%s'", interface_names[1]))
    end
    
    begin
        addr_map_entry_s addr_map_entries[] = new [1];
        addr_map_entries = '{1{
            '{MAP_NORMAL,"RANGE_1",1,MAP_NS,4'h0,64'h0,64'h2400000,MEM_NORMAL,MAP_NORM_SEC_DATA}}};
        APB_ADDR_MAP = address_map::type_id::create("APB_ADDR_MAP_addr_map");
        APB_ADDR_MAP.addr_mask = 64'hFFF;
        APB_ADDR_MAP.set( addr_map_entries );
    end
    begin
        addr_map_entry_s addr_map_entries[] = new [1];
        addr_map_entries = '{1{
            '{MAP_NORMAL,"RANGE_1",1,MAP_NS,4'h0,64'h0,64'h1000,MEM_NORMAL,MAP_NORM_SEC_DATA}}};
        AXI_ADDR_MAP = address_map::type_id::create("AXI_ADDR_MAP_addr_map");
        AXI_ADDR_MAP.addr_mask = 64'hFFF;
        AXI_ADDR_MAP.set( addr_map_entries );
    end
    
    apb_master_0_config_policy::configure(apb_master_0_cfg, APB_ADDR_MAP);
    apb_master_1_config_policy::configure(apb_master_1_cfg, APB_ADDR_MAP);
    axi4_master_0_config_policy::configure(axi4_master_0_cfg, AXI_ADDR_MAP);
    if ( interface_activity.size() > 0 )
    begin
        case ( interface_activity[0] )
            ACTIVE :
                apb_master_0_cfg.agent_cfg.is_active = 1;
            PASSIVE :
                apb_master_0_cfg.agent_cfg.is_active = 0;
        endcase
        case ( interface_activity[1] )
            ACTIVE :
                axi4_master_0_cfg.agent_cfg.is_active = 1;
            PASSIVE :
                axi4_master_0_cfg.agent_cfg.is_active = 0;
        endcase
	case ( interface_activity[3] )
            ACTIVE :
                apb_master_1_cfg.agent_cfg.is_active = 1;
            PASSIVE :
                apb_master_1_cfg.agent_cfg.is_active = 0;
        endcase
    end
endfunction: initialize

