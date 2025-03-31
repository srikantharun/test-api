/**
 * Abstract:
 */
`ifndef GUARD_AI_CORE_MVM_ENV_SV
`define GUARD_AI_CORE_MVM_ENV_SV

`define EXPLICIT_PREDICTOR

// AI CORE MVM environment class
class ai_core_mvm_env extends uvm_env;

  // HDL path to RAL register model
  string hdl_path;

  /** UVM Component Utility macro */
  `uvm_component_utils_begin(ai_core_mvm_env)
    `uvm_field_string(hdl_path, UVM_DEFAULT)
  `uvm_component_utils_end

  // AI CORE MVM environment configuration
  ai_core_mvm_env_cfg m_env_cfg;

  /** AXI System ENV */
  svt_axi_system_env axi_system_env;

  /** Virtual Sequencer */
  axi_virtual_sequencer sequencer;

  /** AXI System Configuration */
  cust_svt_axi_system_configuration cfg;

  /** AXI System Configuration from Core Consultant */
  cust_svt_axi_system_cc_configuration cc_cfg;

  /** Master/Slave Scoreboard */
  ai_core_mvm_scoreboard mvm_scoreboard;

  // icdf scoreboard
  axi_icdf_scoreboard axi_icdf_scb;

  // AI Core MVM RAL Model
  MVM_RAL mvm_regmodel;
   /** ai_core_mvm_ref model */
   ai_core_mvm_ref_model 	ai_core_mvm_ref_model_h;
   /** ai_core_mvm_func_cov */
   ai_core_mvm_func_cov 	ai_core_mvm_func_cov_h;
  
  /** Token agent
  * Bi-dimensional array with first dimension with 2 positions (one for Execution and other for Program).
  * Since both (Execution and Program) have the same number of tokens, and the number of consumer tokens is equal to producer tokens the macro MVM_EXE_NR_TOK_CONS was used to define the second dimension */
  token_agent             tok_agt[2][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS]; //2 is the number of token interfaces (Execution and Program)

  cc_clk_div_agent         clk_div_agt;
  cc_clk_div_agent_config  clk_div_agt_cfg;

`ifdef EXPLICIT_PREDICTOR
  // Explicit/Manual predictor
  // By default, the svt_axi_master_agent enables the auto reg prediction in the connect_phase. Enabling the manual/explicit
  // reg prediction is useful when the registers also get updated by normal transactions and not through reg sequence
  uvm_reg_predictor#(svt_axi_transaction) axi2reg_predictor;
`endif

  /** Class Constructor */
  function new(string name = "ai_core_mvm_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_HIGH)

    super.build_phase(phase);

    if (m_env_cfg == null)
    begin
      if (!uvm_config_db#(ai_core_mvm_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg))
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
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", cc_cfg);
    end else if (uvm_config_db#(cust_svt_axi_system_configuration)::get(this, "", "cfg", cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", cfg);
    end
    // No configuration passed from test
    else
    begin
      cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", cfg);
    end

    /** Construct the system agent */
    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);

    /** Construct the virtual sequencer */
    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);

    /* Create the scoreboard */
    mvm_scoreboard = ai_core_mvm_scoreboard::type_id::create("mvm_scoreboard", this);

    // Create icdf scoreboard
    axi_icdf_scb = axi_icdf_scoreboard::type_id::create("axi_icdf_scb", this);

`ifdef EXPLICIT_PREDICTOR
    // Predictor
    axi2reg_predictor = uvm_reg_predictor#(svt_axi_transaction)::type_id::create("axi2reg_predictor", this);
`endif

    /** Create RAL Models */
    // MVM RAL Model
    if (mvm_regmodel == null)
    begin
      mvm_regmodel = MVM_RAL::type_id::create("mvm_regmodel");
      mvm_regmodel.set_hdl_path_root(hdl_path);
      mvm_regmodel.build(MVMEXE_CSR_BASE_ADDR);
      mvm_regmodel.lock_model();
      uvm_config_db#(uvm_reg_block)::set(this,"axi_system_env.master[0]", "axi_regmodel", mvm_regmodel);
      mvm_regmodel.default_map.set_auto_predict(1);
      mvm_regmodel.default_map.set_check_on_read(1);
      `uvm_info("build_phase", "AI Core MVM Reg Model (Reg Model) created", UVM_HIGH)
    end
    else
      `uvm_error("ENV_BUILD_PHASE", "Unable to build Reg Model");

    // Connect the register model
    sequencer.regmodel = mvm_regmodel;

    ai_core_mvm_ref_model_h = ai_core_mvm_ref_model::type_id::create("ai_core_mvm_ref_model_h", this);

    ai_core_mvm_func_cov_h = ai_core_mvm_func_cov::type_id::create("ai_core_mvm_func_cov_h", this);
    /** Create token agent array */
    foreach (tok_agt[i,j]) begin
      tok_agt[i][j] = token_agent::type_id::create($sformatf("tok_agt[%0d][%0d]", i,j), this);
    end
    
    clk_div_agt_cfg = cc_clk_div_agent_config::type_id::create("clk_div_agt_cfg");
    clk_div_agt_cfg.randomize() with {m_b_enable==1;};
    `uvm_info("build_phase", $sformatf("clk_div_agt_cfg after randomization: %s", clk_div_agt_cfg.convert2string()), UVM_HIGH)
    /** Set configuration for Clock divider on MVM environment */
    uvm_config_db#(cc_clk_div_agent_config)::set(this, "clk_div_agt", "cfg", this.clk_div_agt_cfg);
    clk_div_agt = cc_clk_div_agent::type_id::create($sformatf("clk_div_agt"), this);

    `uvm_info("build_phase", "Exiting...", UVM_HIGH)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_HIGH)
    /**
    * Connect the master and slave agent's analysis ports with
    * item_observed_before_export and item_observed_after_export ports of the
    * scoreboard.*/
    //axi_system_env.master[0].monitor.item_observed_port.connect(
        //mvm_scoreboard.item_observed_initiated_export);
    //axi_system_env.slave[0].monitor.item_observed_port.connect(
        //mvm_scoreboard.item_observed_response_export);
`ifdef EXPLICIT_PREDICTOR
    // Explicit reg predictor
    axi2reg_predictor.map     = mvm_regmodel.get_default_map();
    axi2reg_predictor.adapter = axi_system_env.master[0].reg2axi_adapter;
    mvm_regmodel.default_map.set_auto_predict(0);
    axi_system_env.master[0].monitor.item_observed_port.connect(axi2reg_predictor.bus_in);
`endif
    if (m_env_cfg.has_scoreboard) begin
      axi_system_env.master[0].monitor.item_observed_port.connect(ai_core_mvm_ref_model_h.axi4_lp_2_ref_model_export);
      axi_system_env.master[1].monitor.item_observed_port.connect(ai_core_mvm_ref_model_h.axis_ifdw_2_ref_model_export);
      axi_system_env.master[2].monitor.item_observed_port.connect(ai_core_mvm_ref_model_h.axis_ifd0_2_ref_model_export);
      axi_system_env.master[3].monitor.item_observed_port.connect(ai_core_mvm_ref_model_h.axis_ifd2_2_ref_model_export); 
      axi_system_env.slave[0].monitor.item_observed_port.connect(mvm_scoreboard.actual_data_export);
      ai_core_mvm_ref_model_h.ref_model_2_sb_expected_data_port.connect(mvm_scoreboard.expected_data_export);
      // Func coverage
      axi_system_env.master[0].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axi4_lp_2_func_cov_export);
      axi_system_env.master[1].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axis_ifdw_2_func_cov_export);
      axi_system_env.master[2].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axis_ifd0_2_func_cov_export);
      axi_system_env.master[3].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axis_ifd2_2_func_cov_export);
      axi_system_env.slave[0].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axi4_iau_data_export);
      if(m_env_cfg.has_scoreboard_token) begin
        //connect token agent to scoreboard
        foreach (tok_agt[VERIF_MVM_EXE_TOK_AGT][i]) begin
          tok_agt[VERIF_MVM_EXE_TOK_AGT][i].m_tok_mon.ap.connect(mvm_scoreboard.taf_mon_tok[VERIF_MVM_EXE_TOK_AGT].analysis_export);
        end
        foreach (tok_agt[VERIF_MVM_PRG_TOK_AGT][i]) begin
          tok_agt[VERIF_MVM_PRG_TOK_AGT][i].m_tok_mon.ap.connect(mvm_scoreboard.taf_mon_tok[VERIF_MVM_PRG_TOK_AGT].analysis_export);
        end
        //connect token information from reference model to scoreboard
        foreach (ai_core_mvm_ref_model_h.ap_tok_out[i]) begin
          ai_core_mvm_ref_model_h.ap_tok_out[i].connect(mvm_scoreboard.taf_mdl_tok[i].analysis_export);
        end
      end

    end

    //axi stream input and output to axi icdf scoreboarad
    if (uvm_root::get().find("uvm_test_top").get_type_name() == "ai_core_mvm_icdf_test") begin
       axi_system_env.slave[0].monitor.item_observed_port.connect(axi_icdf_scb.item_observed_out_stream_export);
    end

    //connect ral model to ref model
     ai_core_mvm_ref_model_h.mvm_regmodel=mvm_regmodel;
    //connect ral model to ref model
     ai_core_mvm_func_cov_h.mvm_regmodel=mvm_regmodel;

    axi_system_env.set_report_verbosity_level(UVM_NONE);
    axi_system_env.master[0].set_report_verbosity_level(UVM_NONE);
    axi_system_env.master[1].set_report_verbosity_level(UVM_NONE);
    axi_system_env.master[2].set_report_verbosity_level(UVM_NONE);
    axi_system_env.master[3].set_report_verbosity_level(UVM_NONE);   
    axi_system_env.slave[0].set_report_verbosity_level(UVM_NONE); 
  
  endfunction : connect_phase

   // Reset the register model
   task reset_phase(uvm_phase phase);
     phase.raise_objection(this, "Resetting regmodel");
     // =======================================================================================================================
     // RAL Models reset
     // =======================================================================================================================
     mvm_regmodel.reset();
     if ( !($test$plusargs("no_ones_initialization")) ) begin
       for (int row = 0; row < IMC_ROWS; row++) begin
         for(int column = 0; column < IMC_COLUMN; column++) begin
            ai_core_mvm_ref_model_h.mvm_mem_ifdw_0[row][column] = 8'hFF;
            ai_core_mvm_ref_model_h.mvm_mem_ifdw_1[row][column] = 8'hFF;
            ai_core_mvm_ref_model_h.mvm_mem_ifdw_2[row][column] = 8'hFF;
            ai_core_mvm_ref_model_h.mvm_mem_ifdw_3[row][column] = 8'hFF;
            ai_core_mvm_func_cov_h.mvm_mem_ifdw_0[row][column] = 8'hFF;
            ai_core_mvm_func_cov_h.mvm_mem_ifdw_1[row][column] = 8'hFF;
            ai_core_mvm_func_cov_h.mvm_mem_ifdw_2[row][column] = 8'hFF;
            ai_core_mvm_func_cov_h.mvm_mem_ifdw_3[row][column] = 8'hFF;
          end
       end
     end
     phase.drop_objection(this);
   endtask

endclass : ai_core_mvm_env

`endif  // GUARD_AI_CORE_MVM_ENV_SV
