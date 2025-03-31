/**
 * Abstract:
 */
`ifndef AI_CORE_CD_ENV_SV
`define AI_CORE_CD_ENV_SV

// AI CORE CONTROL DISPATCHER  environment class
class ai_core_cd_env extends uvm_env;

  // HDL path to RAL register model
  string hdl_path="hdl_top.dut.u_csr";
  typedef axe_uvm_scoreboard#(token_agent_seq_item, token_agent_seq_item) axe_uvm_token_seq_item_scbd;

  /** UVM Component Utility macro */
  `uvm_component_utils_begin(ai_core_cd_env)
    `uvm_field_string(hdl_path, UVM_DEFAULT)
  `uvm_component_utils_end

  // AI CORE CONTROL DISPATCHER environment configuration
  ai_core_cd_env_cfg env_cfg;

  /** AXI System ENV */
  svt_axi_system_env m_axi_system_env;
  cust_svt_axi_monitor_callback cb_address_check;

  /** Virtual Sequencer */
  ai_core_cd_axi_virtual_sequencer sequencer;

  /** AXI System Configuration */
  ai_core_cd_cust_svt_axi_system_configuration axi_cfg;

  /** AXI System Configuration from Core Consultant */
  //dwpu_cust_svt_axi_system_cc_configuration cc_cfg;


  // AI Core CD RAL Model
  aic_cd_csr_reg_block m_aicd_regmodel;

  bit icdf_test_en=0;

  /** AICD Components */
  ai_core_cd_agent          aic_cd_agt;

  /** Token manager interface agent */
  //token_agent             local_tok_agt;
  token_agent             local_tok_agt[];
  token_agent             global_tok_agt[];

  //ai_core_dwpu_ref_model  dwpu_mdl;
  //ai_core_dwpu_coverage   dwpu_cov;
  //ai_core_dwpu_scoreboard dwpu_scb;

  ai_core_cd_mem_manager    m_mem_manager;
  ai_core_cd_ref_model      aicd_refmodel;


  axe_uvm_token_seq_item_scbd aicd_local_tkn_scb[];
  axe_uvm_token_seq_item_scbd aicd_global_tkn_scb[];


  
  //verbosity options
  uvm_verbosity dp_dbg_verbosity = UVM_DEBUG;
  uvm_verbosity tok_dbg_verbosity = UVM_DEBUG;
  typedef uvm_enum_wrapper#(uvm_verbosity) verbosity_wrapper;

  /** Class Constructor */
  function new(string name = "ai_core_cd_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (!uvm_config_db#(ai_core_cd_env_cfg)::get(this, "", "m_env_cfg", env_cfg))
      `uvm_fatal("ENV_BUILD_PHASE", "Unable to find environment configuration object in the uvm_config_db");
    //get the RAL_TEST plusarg and set the configuration
    if ($test$plusargs("RAL_TEST")) env_cfg.ral_test = 1;

    //forward the cofiguration from the env_cfg to the individual components 
    uvm_config_db#(ai_core_cd_ref_model_cfg)::set(this, "aicd_refmodel", "m_cfg", env_cfg.aicd_ref_model_cfg);
    `uvm_info("HDL_TOP_MY_DEBUG_ENV",$sformatf("env_cfg.aicd_ref_model_cfg: %0p",env_cfg.aicd_ref_model_cfg),UVM_NONE)


    // Configuration created through core consultant
    //-//if (uvm_config_db#(ai_core_cd_cust_svt_axi_system_cc_configuration)::get(this, "", "cc_cfg", cc_cfg)) begin
    //-//  /** Apply the configuration to the System ENV */
    //-//  uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", cc_cfg);
    //-//end else 
    if (uvm_config_db#(ai_core_cd_cust_svt_axi_system_configuration)::get(this, "", "axi_cfg", axi_cfg)) begin
      /** Apply the configuration to the System ENV */
      `uvm_info("ENV_BUILD_PHASE", " Setting ai_core_cd_cust_svt_axi_system_configuration created in TEST ", UVM_NONE)
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", axi_cfg);
    end
    // No configuration passed from test
    else
    begin
      axi_cfg = ai_core_cd_cust_svt_axi_system_configuration::type_id::create("axi_cfg");
      /** Apply the configuration to the System ENV */
      `uvm_info("ENV_BUILD_PHASE", " Setting ai_core_cd_cust_svt_axi_system_configuration created in ENV ", UVM_NONE)
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", axi_cfg);
    end

    /** Construct the system agent */
    m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);

    /** Construct the virtual sequencer */
    sequencer = ai_core_cd_axi_virtual_sequencer::type_id::create("sequencer", this);


    /** Create RAL Models */
    // AIC CD RAL Model
    if (m_aicd_regmodel == null)
    begin
      m_aicd_regmodel = aic_cd_csr_reg_block::type_id::create("m_aicd_regmodel");
      m_aicd_regmodel.set_hdl_path_root(hdl_path);
      m_aicd_regmodel.build(ACD_CSR_ST_ADDR);
      m_aicd_regmodel.lock_model();
      `uvm_info("build_phase", "AI Core DWPU Reg Model (Reg Model) created", UVM_LOW)
    end
    m_aicd_regmodel.default_map.set_auto_predict(1);
    m_aicd_regmodel.default_map.set_check_on_read(1);
    uvm_config_db#(uvm_reg_block)::set(this,"m_axi_system_env.master[0]", "axi_regmodel", m_aicd_regmodel);
    
    /** Create Memory Manager */
    m_mem_manager = ai_core_cd_mem_manager#(64, 256)::type_id::create("m_mem_manager", this);
    
    /** Create Ref Model */
    aicd_refmodel = ai_core_cd_ref_model::type_id::create("aicd_refmodel", this);

    //
    aic_cd_agt = ai_core_cd_agent::type_id::create("aic_cd_agt", this);
    //
    //if (env_cfg.has_scoreboard) begin
    //  dwpu_mdl = ai_core_dwpu_ref_model::type_id::create("dwpu_mdl", this);
    //  dwpu_scb = ai_core_dwpu_scoreboard::type_id::create("dwpu_scb", this);
    //end
    //
    //if (env_cfg.has_coverage) begin
    //  dwpu_cov = ai_core_dwpu_coverage::type_id::create("dwpu_cov", this);
    //end

    /** Create token manager agent */
    //local_tok_agt = token_agent::type_id::create("local_tok_agt", this);

    /** Create Token Agents */
    local_tok_agt = new[env_cfg.aicd_ref_model_cfg.local_token_line_num];
    for (int i=0; i<env_cfg.aicd_ref_model_cfg.local_token_line_num; i++)
    begin
      local_tok_agt[i] = token_agent::type_id::create($sformatf("local_tok_agt[%0d]",i), this);
      `uvm_info("HDL_TOP_MY_DEBUG_ENV",$sformatf("local_tok_agt[%0d]",i),UVM_NONE)
    end

    global_tok_agt = new[env_cfg.aicd_ref_model_cfg.global_token_line_num];
    for (int i=0; i<env_cfg.aicd_ref_model_cfg.global_token_line_num; i++)
    begin
      global_tok_agt[i] = token_agent::type_id::create($sformatf("global_tok_agt[%0d]",i), this);
      `uvm_info("HDL_TOP_MY_DEBUG_ENV",$sformatf("global_tok_agt[%0d]",i),UVM_NONE)
    end

    /** Create Token Scoreboards */
    aicd_local_tkn_scb = new[env_cfg.aicd_ref_model_cfg.local_token_line_num];
    for (int i=0; i<env_cfg.aicd_ref_model_cfg.local_token_line_num; i++)
    begin
      aicd_local_tkn_scb[i] = axe_uvm_token_seq_item_scbd::type_id::create($sformatf("aicd_local_tkn_scb[%0d]",i), this);
      aicd_local_tkn_scb[i].comp_min = 0;
      `uvm_info("HDL_TOP_MY_DEBUG_ENV",$sformatf("aicd_local_tkn_scb[%0d]",i),UVM_NONE)
    end
    
    aicd_global_tkn_scb = new[env_cfg.aicd_ref_model_cfg.global_token_line_num];
    for (int i=0; i<env_cfg.aicd_ref_model_cfg.global_token_line_num; i++)
    begin
      aicd_global_tkn_scb[i] = axe_uvm_token_seq_item_scbd::type_id::create($sformatf("aicd_global_tkn_scb[%0d]",i), this);
      aicd_global_tkn_scb[i].comp_min = 0;
      `uvm_info("HDL_TOP_MY_DEBUG_ENV",$sformatf("aicd_global_tkn_scb[%0d]",i),UVM_NONE)
    end

    // Connect the register model
    sequencer.regmodel = m_aicd_regmodel;
    //if(env_cfg.has_scoreboard) begin
    //  dwpu_mdl.regmodel = m_aicd_regmodel;
    //end
    //if (env_cfg.has_coverage) begin
    //  dwpu_cov.regmodel = m_aicd_regmodel;
    //end

    //set verbosity levels
    set_verbosity_levels();

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)

    if (env_cfg.has_scoreboard && !env_cfg.ral_test) begin
      //axi monitors connect to DWPU ref model
      //aic_cd_agt.mon.ap.connect(dwpu_mdl.taf_mon_dwpu.analysis_export);
      //m_axi_system_env.master[0].monitor.item_observed_port.connect(dwpu_mdl.taf_mon_cfg.analysis_export);
      //m_axi_system_env.master[1].monitor.item_observed_port.connect(dwpu_mdl.taf_mon_data.analysis_export);

      //axi stream out monitor to scoreboard
      //m_axi_system_env.slave[0].monitor.item_observed_port.connect(dwpu_scb.taf_mon.analysis_export);
      //ref model outputs connect to scoreboard
      //dwpu_mdl.ap_stream_out.connect(dwpu_scb.taf_mdl.analysis_export);
      //connect dwpu configuration monitor to scoreboard
      //m_axi_system_env.master[0].monitor.item_observed_port.connect(dwpu_scb.taf_mon_cfg.analysis_export);

      aicd_refmodel.regmodel = m_aicd_regmodel;

      //dwpu agent to scoreboard
      //aic_cd_agt.mon.ap.connect(dwpu_scb.taf_mon_dwpu.analysis_export);
      //dwpu item from mdl to scoreboard
      //dwpu_mdl.ap_dwpu_out.connect(dwpu_scb.taf_mdl_dwpu.analysis_export);
      /** Only connect the token analysis port if the scoreboard is enabled for tokens */
      if(env_cfg.has_scoreboard_token) begin
        //connect token ref model information to scoreboard
        for (int i=0; i<env_cfg.aicd_ref_model_cfg.local_token_line_num; i++)
        begin
          aicd_refmodel.local_token_exp_ap[i].connect(aicd_local_tkn_scb[i].analysis_imp_exp);
        end
        for (int i=0; i<env_cfg.aicd_ref_model_cfg.global_token_line_num; i++)
        begin
          aicd_refmodel.global_token_exp_ap[i].connect(aicd_global_tkn_scb[i].analysis_imp_exp);
        end

        //connect token monitors to scoreboard
        for (int i=0; i<env_cfg.aicd_ref_model_cfg.local_token_line_num; i++)
        begin
          local_tok_agt[i].m_tok_mon.ap.connect(aicd_local_tkn_scb[i].analysis_imp_obs);
        end
        for (int i=0; i<env_cfg.aicd_ref_model_cfg.global_token_line_num; i++)
        begin
          global_tok_agt[i].m_tok_mon.ap.connect(aicd_global_tkn_scb[i].analysis_imp_obs);
        end
      end
    end

    //connect reference model 
    aicd_refmodel.mem_manager_p = m_mem_manager;

    if (env_cfg.has_coverage && !env_cfg.ral_test) begin
      //m_axi_system_env.master[0].monitor.item_observed_port.connect(dwpu_cov.taf_mon_cfg.analysis_export);
      //m_axi_system_env.master[1].monitor.item_observed_port.connect(dwpu_cov.taf_mon_data.analysis_export);
      //m_axi_system_env.slave[0].monitor.item_observed_port.connect(dwpu_cov.taf_mon_data_out.analysis_export);
      //dwpu_mdl.ap_dwpu_out.connect(dwpu_cov.taf_mdl_dwpu.analysis_export);
      //tok_agt.m_tok_mon.ap.connect(dwpu_cov.taf_mon_tok.analysis_export);
    end

    /** Connect sequencers to virtual sequencer */
    //sequencer.cfg_seqr       = m_axi_system_env.master[0].sequencer;
    //sequencer.in_stream_seqr = m_axi_system_env.master[1].sequencer;
    
    //turn off vip messages
    //m_axi_system_env.set_report_verbosity_level(UVM_NONE);
    //m_axi_system_env.master[0].set_report_verbosity_level(UVM_NONE);
    //m_axi_system_env.master[1].set_report_verbosity_level(UVM_NONE);
    //m_axi_system_env.slave[0].set_report_verbosity_level(UVM_NONE);


    //connect callback
    cb_address_check = new("cust_svt_axi_monitor_callback_slave");
    cb_address_check.mem_mngr_p = m_mem_manager;
    uvm_callbacks#(svt_axi_port_monitor)::add(m_axi_system_env.slave[0].monitor, cb_address_check);


    //handle AXI SVT verbosity 
    m_axi_system_env.slave[0].set_report_verbosity_level(UVM_HIGH);


  endfunction : connect_phase


  virtual function void start_of_simulation_phase(uvm_phase phase);
    `uvm_info("start_of_simulation_phase", "Entered...",UVM_LOW)
    //initialize();
    
    if (!m_mem_manager.randomize() with {
    //    mem_size == 120;           
    //    mem_partition_num == 3;
    //    //spm_partition_idx == 3;  
//
//
    //    offset_tsk2base == 0;
    //    //offset_tsk2base == 8;
    //    offset_cmd2tsk  == 8;
    //    offset_prg2cmd  == 8;
//
    //    command_list_size == 2;
    //    task_list_size    == 5;
    //    cmd_mem_size      == 10;
    //    prg_mem_size      == 20;
    //    //task_list.length == task_list_size;
    })
       `uvm_fatal("ACD_MEM_MANAGER",$sformatf("Randomization failed")) 

    m_mem_manager.initialize();

    `uvm_info("start_of_simulation_phase", "Exiting...",UVM_LOW)
  endfunction : start_of_simulation_phase


  virtual task configure_phase(uvm_phase phase);
    `uvm_info("configure_phase", "Entered...",UVM_LOW)
    super.configure_phase(phase);

    m_axi_system_env.slave[0].axi_slave_mem.set_meminit(svt_mem::ZEROES); //initialize slv memory with zeroes
    `uvm_info("configure_phase", "Exiting...",UVM_LOW)
  endtask


  // Reset the register model
  task reset_phase(uvm_phase phase);
    phase.raise_objection(this, "Resetting regmodel");
    // =======================================================================================================================
    // RAL Models reset
    // =======================================================================================================================
    m_aicd_regmodel.reset();
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

  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
  endtask : main_phase


  task run_phase(uvm_phase phase);
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    super.run_phase(phase);

    //initialize the SVT SPM space 
    //m_axi_system_env.slave[0].axi_slave_mem.write_byte(); 
    foreach (m_mem_manager.ref_mem.system_memory[addr])
    begin
       `uvm_info("AI_CD_ENV",$sformatf("Transferring system_memory[%0h] : %0h  to SVT MEM", addr, m_mem_manager.ref_mem.system_memory[addr]),UVM_LOW)
       m_axi_system_env.slave[0].write_byte(addr, m_mem_manager.ref_mem.system_memory[addr]);
    end 

    
    `uvm_info("run_phase", "Exiting...", UVM_LOW)
  endtask : run_phase


endclass : ai_core_cd_env

`endif  // AI_CORE_CD_ENV_SV
