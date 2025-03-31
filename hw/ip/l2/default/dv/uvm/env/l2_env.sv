
/**
 * Abstract: 
 * class 'l2_env' is extended from uvm_env base class.  It implements
 * the build phase to construct the structural elements of this environment.
 *
 * l2_env is the testbench environment, which constructs the AXI System
 * ENV in the build_phase method using the UVM factory service.  The AXI System
 * ENV  is the top level component provided by the AXI VIP. The AXI System ENV
 * in turn, instantiates constructs the AXI Master and Slave agents. 
 *
 * axi_basic env also constructs the virtual sequencer. This virtual sequencer
 * in the testbench environment obtains a handle to the reset interface using
 * the config db.  This allows reset sequences to be written for this virtual
 * sequencer.
 *
 * The simulation ends after all the objections are dropped.  This is done by
 * using objections provided by phase arguments.
 */
`ifndef GUARD_L2_ENV_SV
`define GUARD_L2_ENV_SV

`define L2_BASE_ADDR 'h0800_0000
typedef  l2_csr_reg_block L2_RAL;
// L2 environment class
class l2_env extends uvm_env;

  // L2 environment configuration
 // l2_env_cfg env_cfg;

  /** AXI System ENV */
  svt_axi_system_env axi_system_env;

  /** Virtual Sequencer */
  axi_virtual_sequencer sequencer;

  /** AXI System Configuration */
  cust_svt_axi_system_configuration cfg;

  /** AXI System Configuration from Core Consultant */
  cust_svt_axi_system_cc_configuration cc_cfg;

  /** Master/Slave Scoreboard */
  axi_uvm_scoreboard axi_scoreboard;
  
 
  svt_apb_system_env m_apb_system_env;
  apb_virtual_sequencer apb_sequencer;
  cust_l2_svt_apb_system_cfg apb_cfg;

  /** clock divider agent */
 // cc_clk_div_agent  m_clk_div_agt;

  /** RAL Models */
  L2_RAL                          regmodel;

  // HDL RAL register model
  string hdl_path;

  /** UVM Component Utility macro */
  `uvm_component_utils_begin(l2_env)
      `uvm_field_string(hdl_path,UVM_DEFAULT)
   `uvm_component_utils_end
    

  /** Class Constructor */
  function new (string name="l2_env", uvm_component parent=null);
    super.new (name, parent);
  endfunction:new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...",UVM_LOW)

    super.build_phase(phase);
   /* 
    if (env_cfg == null) begin
      if (!uvm_config_db#(l2_env_cfg)::get(this, "", "env_cfg", env_cfg))
      begin
        `uvm_error("ENV_BUILD_PHASE", "Unable to find environment configuration object in the uvm_config_db");
      end
    end
*/
    /**
     * Check if the configuration is passed to the environment.
     * If not then create the configuration and pass it to the agent.
     */

    // Configuration created through core consultant
    if (uvm_config_db#(cust_svt_axi_system_cc_configuration)::get(this, "", "cc_cfg", cc_cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", cc_cfg);
    end
    else if (uvm_config_db#(cust_svt_axi_system_configuration)::get(this, "", "cfg", cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", cfg);
    end
    // No configuration passed from test
    else begin
      cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", cfg);
    end

    /** Construct the system agent */
    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);

    /** Create clock divider agent */
   // create_clk_div_agt();

    /** Construct the virtual sequencer */
    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);

    /* Create the scoreboard */
    axi_scoreboard = axi_uvm_scoreboard::type_id::create("axi_scoreboard", this);
    
    //apb
    if (uvm_config_db#(cust_l2_svt_apb_system_cfg)::get(this, "", "cfg", apb_cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_apb_system_configuration)::set(this, "m_apb_system_env", "apb_cfg", apb_cfg);
    end
    // No configuration passed from test
    else begin 
     apb_cfg = cust_l2_svt_apb_system_cfg::type_id::create("apb_cfg");
     uvm_config_db#(svt_apb_system_configuration)::set(this, "m_apb_system_env", "cfg", apb_cfg);
    end

    m_apb_system_env = svt_apb_system_env::type_id::create("m_apb_system_env", this);
    apb_sequencer = apb_virtual_sequencer::type_id::create("apb_sequencer", this);

  // assert(env.m_apb_system_env != null) else $error("m_apb_system_env is NULL!");
    


    if (regmodel == null) begin
      `uvm_info(get_type_name(), $sformatf("regmodel is null, creating one"), UVM_LOW)
      regmodel = L2_RAL::type_id::create("regmodel");

      regmodel.set_hdl_path_root(hdl_path);

      `uvm_info(get_type_name(), $sformatf("Creating regmodel with L2_BASE_ADDR = %0h ", `L2_BASE_ADDR), UVM_LOW)

      regmodel.build(`L2_BASE_ADDR);
      regmodel.lock_model();

     uvm_config_db#(uvm_reg_block)::set(this, "m_apb_system_env", "apb_regmodel", regmodel);
     uvm_config_db#(uvm_reg_block)::set(this, "apb_master_env.master", "apb_regmodel", regmodel);
      regmodel.default_map.set_auto_predict(1);
      regmodel.default_map.set_check_on_read(1);

    end
     else
     `uvm_error("ENV_BUILD_PHASE", "Unable to build Reg Model");



     apb_sequencer.regmodel =this.regmodel;
    

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction:build_phase
   
  virtual task reset_phase(uvm_phase phase);
    phase.raise_objection(this, "Resetting regmodel");
    regmodel.reset();
    phase.drop_objection(this);
  endtask

  
  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...",UVM_LOW)
    /**
    * Connect the master and slave agent's analysis ports with
    * item_observed_before_export and item_observed_after_export ports of the
    * scoreboard.*/
    axi_system_env.master[0].monitor.item_observed_port.connect(axi_scoreboard.item_observed_initiated_export);
    axi_system_env.slave[0].monitor.item_observed_port.connect(axi_scoreboard.item_observed_response_export);
  endfunction:connect_phase
  
  /** function to create clock divider agent */
 // extern function void create_clk_div_agt();
endclass
/*
function void l2_env::create_clk_div_agt();
  if (!(env_cfg.m_clk_div_agt_cfg.randomize() with {m_b_enable==1;})) begin
    `uvm_fatal(get_name(), "Randomization failed for env_cfg.m_clk_div_agt_cfg!")
  end
  `uvm_info("build_phase", $sformatf("env_cfg.m_clk_div_agt_cfg after randomization: %s", env_cfg.m_clk_div_agt_cfg.convert2string()), UVM_LOW)
  /** Set configuration for Clock divider on  environment 
  uvm_config_db#(cc_clk_div_agent_config)::set(this, "m_clk_div_agt", "cfg", env_cfg.m_clk_div_agt_cfg);
  m_clk_div_agt = cc_clk_div_agent::type_id::create($sformatf("m_clk_div_agt"), this);
endfunction : create_clk_div_agt
*/
`endif // GUARD_L2_ENV_SV
