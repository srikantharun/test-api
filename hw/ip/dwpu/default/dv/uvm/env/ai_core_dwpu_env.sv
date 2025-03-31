/**
 * Abstract:
 */
`ifndef GUARD_AI_CORE_DWPU_ENV_SV
`define GUARD_AI_CORE_DWPU_ENV_SV

// AI CORE DWPU environment class
class ai_core_dwpu_env extends uvm_env;

  // HDL path to RAL register model
  string hdl_path="hdl_top.dut.u_csr";

  /** UVM Component Utility macro */
  `uvm_component_utils_begin(ai_core_dwpu_env)
    `uvm_field_string(hdl_path, UVM_DEFAULT)
  `uvm_component_utils_end

  // AI CORE DWPU environment configuration
  ai_core_dwpu_env_cfg env_cfg;

  /** AXI System ENV */
  svt_axi_system_env m_axi_system_env;

  /** Virtual Sequencer */
  dwpu_axi_virtual_sequencer sequencer;

  /** AXI System Configuration */
  dwpu_cust_svt_axi_system_configuration cfg;

  /** AXI System Configuration from Core Consultant */
  dwpu_cust_svt_axi_system_cc_configuration cc_cfg;


  // AI Core DWPU RAL Model
  DWPU_RAL m_dwpu_regmodel;

  bit icdf_test_en=0;

  /** DWPU Components */
  ai_core_dwpu_agent      dwpu_agt;
  ai_core_dwpu_ref_model  dwpu_mdl;
  ai_core_dwpu_coverage   dwpu_cov;
  ai_core_dwpu_scoreboard dwpu_scb;

  /** Token manager interface agent */
  token_agent             tok_agt;
  
  //verbosity options
  uvm_verbosity dp_dbg_verbosity = UVM_DEBUG;
  uvm_verbosity tok_dbg_verbosity = UVM_DEBUG;
  typedef uvm_enum_wrapper#(uvm_verbosity) verbosity_wrapper;

  /** Class Constructor */
  function new(string name = "ai_core_dwpu_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (!uvm_config_db#(ai_core_dwpu_env_cfg)::get(this, "", "m_env_cfg", env_cfg))
      `uvm_fatal("ENV_BUILD_PHASE", "Unable to find environment configuration object in the uvm_config_db");
    //get the RAL_TEST plusarg and set the configuration
    if ($test$plusargs("RAL_TEST")) env_cfg.ral_test = 1;

    // Configuration created through core consultant
    if (uvm_config_db#(dwpu_cust_svt_axi_system_cc_configuration)::get(this, "", "cc_cfg", cc_cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", cc_cfg);
    end else if (uvm_config_db#(dwpu_cust_svt_axi_system_configuration)::get(this, "", "cfg", cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", cfg);
    end
    // No configuration passed from test
    else
    begin
      cfg = dwpu_cust_svt_axi_system_configuration::type_id::create("cfg");
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", cfg);
    end

    /** Construct the system agent */
    m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);

    /** Construct the virtual sequencer */
    sequencer = dwpu_axi_virtual_sequencer::type_id::create("sequencer", this);


    /** Create RAL Models */
    // DWPU RAL Model
    if (m_dwpu_regmodel == null)
    begin
      m_dwpu_regmodel = DWPU_RAL::type_id::create("m_dwpu_regmodel");
      m_dwpu_regmodel.set_hdl_path_root(hdl_path);
      m_dwpu_regmodel.build(DWPU_CSR_ST_ADDR);
      m_dwpu_regmodel.lock_model();
      `uvm_info("build_phase", "AI Core DWPU Reg Model (Reg Model) created", UVM_LOW)
    end
    m_dwpu_regmodel.default_map.set_auto_predict(1);
    m_dwpu_regmodel.default_map.set_check_on_read(1);
    uvm_config_db#(uvm_reg_block)::set(this,"m_axi_system_env.master[0]", "axi_regmodel", m_dwpu_regmodel);

    dwpu_agt = ai_core_dwpu_agent::type_id::create("dwpu_agt", this);

    if (env_cfg.has_scoreboard) begin
      dwpu_mdl = ai_core_dwpu_ref_model::type_id::create("dwpu_mdl", this);
      dwpu_scb = ai_core_dwpu_scoreboard::type_id::create("dwpu_scb", this);
    end

    if (env_cfg.has_coverage) begin
      dwpu_cov = ai_core_dwpu_coverage::type_id::create("dwpu_cov", this);
    end

    /** Create token manager agent */
    tok_agt = token_agent::type_id::create("tok_agt", this);

    // Connect the register model
    sequencer.regmodel = m_dwpu_regmodel;
    if(env_cfg.has_scoreboard) begin
      dwpu_mdl.regmodel = m_dwpu_regmodel;
    end
    if (env_cfg.has_coverage) begin
      dwpu_cov.regmodel = m_dwpu_regmodel;
    end

    //set verbosity levels
    set_verbosity_levels();

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)

    if (env_cfg.has_scoreboard && !env_cfg.ral_test) begin
      //axi monitors connect to DWPU ref model
      dwpu_agt.mon.ap.connect(dwpu_mdl.taf_mon_dwpu.analysis_export);
      m_axi_system_env.master[0].monitor.item_observed_port.connect(dwpu_mdl.taf_mon_cfg.analysis_export);
      m_axi_system_env.master[1].monitor.item_observed_port.connect(dwpu_mdl.taf_mon_data.analysis_export);

      //axi stream out monitor to scoreboard
      m_axi_system_env.slave[0].monitor.item_observed_port.connect(dwpu_scb.taf_mon.analysis_export);
      //ref model outputs connect to scoreboard
      dwpu_mdl.ap_stream_out.connect(dwpu_scb.taf_mdl.analysis_export);
      //connect dwpu configuration monitor to scoreboard
      m_axi_system_env.master[0].monitor.item_observed_port.connect(dwpu_scb.taf_mon_cfg.analysis_export);

      //dwpu agent to scoreboard
      dwpu_agt.mon.ap.connect(dwpu_scb.taf_mon_dwpu.analysis_export);
      //dwpu item from mdl to scoreboard
      dwpu_mdl.ap_dwpu_out.connect(dwpu_scb.taf_mdl_dwpu.analysis_export);
      /** Only connect the token analysis port if the scoreboard is enabled for tokens */
      if(env_cfg.has_scoreboard_token) begin
        //connect token manager to scoreboard
        tok_agt.m_tok_mon.ap.connect(dwpu_scb.taf_mon_tok.analysis_export);
        //connect token manager model information to scoreboard
        dwpu_mdl.ap_tok_out.connect(dwpu_scb.taf_mdl_tok.analysis_export);
      end
    end

    if (env_cfg.has_coverage && !env_cfg.ral_test) begin
      m_axi_system_env.master[0].monitor.item_observed_port.connect(dwpu_cov.taf_mon_cfg.analysis_export);
      m_axi_system_env.master[1].monitor.item_observed_port.connect(dwpu_cov.taf_mon_data.analysis_export);
      m_axi_system_env.slave[0].monitor.item_observed_port.connect(dwpu_cov.taf_mon_data_out.analysis_export);
      dwpu_mdl.ap_dwpu_out.connect(dwpu_cov.taf_mdl_dwpu.analysis_export);
      tok_agt.m_tok_mon.ap.connect(dwpu_cov.taf_mon_tok.analysis_export);
    end

    /** Connect sequencers to virtual sequencer */
    sequencer.cfg_seqr       = m_axi_system_env.master[0].sequencer;
    sequencer.in_stream_seqr = m_axi_system_env.master[1].sequencer;
    
    //turn off vip messages
    m_axi_system_env.set_report_verbosity_level(UVM_NONE);
    m_axi_system_env.master[0].set_report_verbosity_level(UVM_NONE);
    m_axi_system_env.master[1].set_report_verbosity_level(UVM_NONE);
    m_axi_system_env.slave[0].set_report_verbosity_level(UVM_NONE);

  endfunction : connect_phase

  // Reset the register model
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this, "Resetting regmodel");
    // =======================================================================================================================
    // RAL Models reset
    // =======================================================================================================================
    m_dwpu_regmodel.reset();
    phase.drop_objection(this);
  endtask
  
  virtual function void set_verbosity_levels();
    string aux_str;

    //set vebosity levels for Datapath and token analysis
    if(!$value$plusargs("DP_DBG_VERBOSITY=%s", aux_str)) aux_str = "UVM_DEBUG";
    if(!verbosity_wrapper::from_name(aux_str, dp_dbg_verbosity)) begin
      `uvm_warning("dwpu_scb", $sformatf("The string passed into DP_DGB_SEVERITY = %0s cannot be used. The severity used will be UVM_DEBUG.", aux_str))
    end
    if(!$value$plusargs("TOK_DBG_VERBOSITY=%s", aux_str)) aux_str = "UVM_DEBUG";
    if(!verbosity_wrapper::from_name(aux_str, tok_dbg_verbosity)) begin
      `uvm_warning("dwpu_scb", $sformatf("The string passed into TOK_DGB_SEVERITY = %0s cannot be used. The severity used will be UVM_DEBUG.", aux_str))
    end

    //set to lower blocks
    uvm_config_db#(uvm_verbosity)::set(this, "*", "dp_dbg_verbosity", dp_dbg_verbosity);
    uvm_config_db#(uvm_verbosity)::set(this, "*", "tok_dbg_verbosity", tok_dbg_verbosity);
  endfunction : set_verbosity_levels

  virtual function bit is_output_data_consumed();
    //do nothing. This function will be overritten by icdf testcase env
  endfunction : is_output_data_consumed

endclass : ai_core_dwpu_env

`endif  // GUARD_AI_CORE_DWPU_ENV_SV
