/**
 * Abstract:
 * class 'ai_core_env' is extended from uvm_env base class.  It implements
 * the build phase to construct the structural elements of this environment.
 *
 * ai_core_env is the testbench environment, which constructs the AXI System
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
`ifndef GUARD_AI_CORE_ENV_SV
`define GUARD_AI_CORE_ENV_SV

typedef  ai_core_top_reg_block AI_CORE_TOP_RAL;

// ai_core environment class
class ai_core_env extends uvm_env;

  typedef ai_core_ral#(`AXI_LP_ADDR_WIDTH, `AXI_LP_DATA_WIDTH) ai_core_ral_t;
  // ai_core environment configuration
  ai_core_top_env_cfg                      m_env_cfg;

  /** AXI System ENV */
  svt_axi_system_env                       m_axi_system_env;
  svt_apb_system_env                       m_apb_system_env;

  /** Virtual Sequencer */
  ai_core_top_axi_virtual_sequencer        sequencer;
  apb_virtual_sequencer                    apb_sequencer;


  /** AXI System Configuration */
  cust_svt_axi_system_configuration        cfg;
  cust_aicore_svt_apb_system_configuration apb_cfg;

  /** AXI System Configuration from Core Consultant */
  cust_svt_axi_system_cc_configuration     cc_cfg;

  //ls env
  aic_ls_env                           m_ls_env;
  aic_ls_env_cfg                   m_ls_env_cfg;
  /** Master/Slave Scoreboard */
  //axi_uvm_scoreboard                     axi_scoreboard;

  //ai_core_fcov_collector                 fcov_collector;

  virtual ai_core_top_if                   tb_cfg_if;

  /** RAL Models */
  AI_CORE_TOP_RAL                          regmodel;
  AI_CORE_TOP_RAL                          regmodel_core_ctrl;

  ai_core_ral_t                            m_ral;
  
  // HDL patto RAL register model
  string hdl_path;


  /** UVM Component Utility macro */
  `uvm_component_utils_begin(ai_core_env)
    `uvm_field_string(hdl_path, UVM_DEFAULT)
  `uvm_component_utils_end


  /** Class Constructor */
  function new (string name="ai_core_env", uvm_component parent=null);
    super.new (name, parent);
  endfunction:new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...",UVM_LOW)

    super.build_phase(phase);

    if (m_env_cfg == null) begin
      if (!uvm_config_db#(ai_core_top_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg))
      begin
        `uvm_error("ENV_BUILD_PHASE", "Unable to find environment configuration object in the uvm_config_db");
      end
    end

    /**
     * Check if the configuration is passed to the environment.
     * If not then create the configuration and pass it to the agent.
     */

    // Configuration created through core consultant
    if (uvm_config_db#(cust_svt_axi_system_cc_configuration)::get(this, "", "cc_cfg", cc_cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", cc_cfg);
    end
    else if (uvm_config_db#(cust_svt_axi_system_configuration)::get(this, "", "cfg", cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", cfg);
    end
    // No configuration passed from test
    else begin
      cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", cfg);
    end

    if (uvm_config_db#(cust_aicore_svt_apb_system_configuration)::get(this, "", "cfg", apb_cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_apb_system_configuration)::set(this, "m_apb_system_env", "apb_cfg", apb_cfg);
    end
    // No configuration passed from test
    else begin
     apb_cfg = cust_aicore_svt_apb_system_configuration::type_id::create("apb_cfg");
     uvm_config_db#(svt_apb_system_configuration)::set(this, "m_apb_system_env", "cfg", apb_cfg);
    end
    
    /** Create RAL Models */
    // RAL model


    if (regmodel == null) begin
      `uvm_info(get_type_name(), $sformatf("regmodel is null, creating one"), UVM_LOW)
      regmodel = AI_CORE_TOP_RAL::type_id::create("regmodel");

      regmodel.set_hdl_path_root(hdl_path);

      `uvm_info(get_type_name(), $sformatf("Creating regmodel with AI_CORE_BASE_ADDR = 'h%0h and CID = 'd%0d", `AI_CORE_BASE_ADDR, m_env_cfg.ai_core_cid), UVM_LOW)

      regmodel.build(`AI_CORE_BASE_ADDR);
      regmodel.lock_model();

      uvm_config_db#(uvm_reg_block)::set(this,"m_axi_system_env.master[0]", "axi_regmodel", regmodel);
      regmodel.default_map.set_auto_predict(1);
      regmodel.default_map.set_check_on_read(1);

    end

    m_ral = ai_core_ral_t::type_id::create("m_ral", this);
    uvm_config_db#(ai_core_ral_t)::set(null, "*", "ai_core_ral", m_ral);
    uvm_config_db#(ai_core_top_reg_block)::set(this, "m_ral", "ai_core_top_regmodel", regmodel);

    `uvm_info(get_type_name(), $sformatf("KSC_reg model"), UVM_LOW)
    /** Construct the system agent */
    m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);
    m_apb_system_env = svt_apb_system_env::type_id::create("m_apb_system_env", this);

    /** Construct the virtual sequencer */
    sequencer = ai_core_top_axi_virtual_sequencer::type_id::create("sequencer", this);
    apb_sequencer = apb_virtual_sequencer::type_id::create("apb_sequencer", this);

    /* Create the scoreboard */
    //uvm_config_db#(ai_core_top_env_cfg)::set(this, "axi_scoreboard", "m_env_cfg", m_env_cfg);
    //axi_scoreboard = axi_uvm_scoreboard::type_id::create("axi_scoreboard", this);

   // uvm_config_db#(ai_core_top_env_cfg)::set(this, "fcov_collector", "m_env_cfg", m_env_cfg);
   // fcov_collector = ai_core_fcov_collector::type_id::create("fcov_collector", this);

    // Connecting regmodel to axi virtual sequencer
    sequencer.regmodel = regmodel;
    sequencer.env = this;

    uvm_config_db#(virtual ai_core_top_if)::get(uvm_root::get(), "", "tb_cfg_if", tb_cfg_if);

    //ls env
    m_ls_env = aic_ls_env::type_id::create("m_ls_env", this);
    uvm_config_db#(aic_ls_env)::set(null,"*", "aic_ls_env", m_ls_env);
    randomize_env_cfg();
    uvm_config_db#(aic_ls_env_cfg)::set(this, "m_ls_env", "m_env_cfg", m_env_cfg.m_ls_env_cfg);



    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction:build_phase


  virtual task reset_phase(uvm_phase phase);
    phase.raise_objection(this, "Resetting regmodel");
    regmodel.reset();
    phase.drop_objection(this);
  endtask


  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...",UVM_LOW)
     tb_cfg_if.regmodel=regmodel;

    `ifdef SCB_EN
      /**
      * Connect the master and slave agent's analysis ports with
      * item_observed_before_export and item_observed_after_export ports of the
      * scoreboard.*/
      m_axi_system_env.master[0].monitor.item_observed_port.connect(axi_scoreboard.item_observed_initiated_export);
      m_axi_system_env.master[1].monitor.item_observed_port.connect(axi_scoreboard.item_observed_initiated_export_ctrlr);

      //TS
      m_axi_system_env.slave[0].monitor.item_observed_port.connect(axi_scoreboard.item_observed_response_export);
      m_axi_system_env.slave[1].monitor.item_observed_port.connect(axi_scoreboard.actual_data_response_export_noc_hp);
      m_axi_system_env.slave[2].monitor.item_observed_port.connect(axi_scoreboard.actual_data_response_export_mvm);
      m_axi_system_env.slave[3].monitor.item_observed_port.connect(axi_scoreboard.actual_data_response_export_dwpu);
      m_axi_system_env.slave[4].monitor.item_observed_port.connect(axi_scoreboard.actual_data_response_export_dpu_0);
      m_axi_system_env.slave[5].monitor.item_observed_port.connect(axi_scoreboard.actual_data_response_export_dpu_1);
      m_axi_system_env.slave[6].monitor.item_observed_port.connect(axi_scoreboard.actual_data_response_export_ls_lp);
      m_axi_system_env.slave[7].monitor.item_observed_port.connect(axi_scoreboard.actual_data_response_export_ls_hp);
    `endif

  endfunction:connect_phase

  virtual function void randomize_env_cfg();
    if (!(m_env_cfg.m_ls_env_cfg.randomize()with{m_env_cfg.m_ls_env_cfg.m_cid==1;})) begin //as of now for 1 ai core. TODO
      `uvm_fatal(get_name(), "Randomization failed for m_env_cfg.m_ls_env_cfg!")
    end
  endfunction

endclass




`endif // GUARD_AI_CORE_ENV_SV
