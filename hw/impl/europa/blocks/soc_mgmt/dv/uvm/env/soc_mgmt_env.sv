/**
 * Abstract:
 */
`ifndef GUARD_SOC_MGMT_ENV_SV
`define GUARD_SOC_MGMT_ENV_SV

`define EXPLICIT_PREDICTOR

//soc_mgmt environment class
class soc_mgmt_env extends uvm_env;

  // HDL path to RAL register model
  string hdl_path;

  /** UVM Component Utility macro */
  `uvm_component_utils_begin(soc_mgmt_env)
    `uvm_field_string(hdl_path, UVM_DEFAULT)
  `uvm_component_utils_end

  // soc_mgmt environment configuration
  soc_mgmt_env_cfg m_env_cfg;

  /** AXI System ENV */
  svt_axi_system_env axi_system_env;

  /** Virtual Sequencer */
  axi_virtual_sequencer sequencer;

  /** AXI System Configuration */
  cust_svt_axi_system_configuration cfg;

  /** AXI System Configuration from Core Consultant */
  cust_svt_axi_system_cc_configuration cc_cfg;

  /** APB VIP Master ENV */
  svt_apb_system_env apb_master_env;

  apb_virtual_sequencer apb_sequencer;
  /** APB System Configuration */
  apb_shared_cfg apb_cfg;

  /** Master/Slave Scoreboard */
  soc_mgmt_scoreboard soc_mgmt_scoreboard_h;

  //soc_mgmt RAL Model
  soc_mgmt_reg_block soc_mgmt_regmodel;
   /** soc_mgmt_ref model */
   soc_mgmt_ref_model 	soc_mgmt_ref_model_h;
   /** soc_mgmt_func_cov */
   soc_mgmt_func_cov 	soc_mgmt_func_cov_h;
  
`ifdef EXPLICIT_PREDICTOR
  // Explicit/Manual predictor
  // By default, the svt_axi_master_agent enables the auto reg prediction in the connect_phase. Enabling the manual/explicit
  // reg prediction is useful when the registers also get updated by normal transactions and not through reg sequence
  uvm_reg_predictor#(svt_axi_transaction) axi2reg_predictor;
`endif

  /** Class Constructor */
  function new(string name = "soc_mgmt_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (m_env_cfg == null)
    begin
      if (!uvm_config_db#(soc_mgmt_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg))
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

    //apb
    if (!uvm_config_db#(apb_shared_cfg)::get(this, "", "cfg", apb_cfg)) begin
      apb_cfg = apb_shared_cfg::type_id::create("apb_cfg", this);
    end

    /** Apply the configuration to the Master ENV */
    uvm_config_db#(svt_apb_system_configuration)::set(this, "apb_master_env", "cfg", apb_cfg.master_cfg);

    /** Construct the system agents */
    apb_master_env = svt_apb_system_env::type_id::create("apb_master_env", this);
    apb_sequencer = apb_virtual_sequencer::type_id::create("apb_sequencer", this);

    /** Construct the system agent */
    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);

    /** Construct the virtual sequencer */
    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);

    /* Create the scoreboard */
    soc_mgmt_scoreboard_h = soc_mgmt_scoreboard::type_id::create("soc_mgmt_scoreboard_h", this);

`ifdef EXPLICIT_PREDICTOR
    // Predictor
    axi2reg_predictor = uvm_reg_predictor#(svt_axi_transaction)::type_id::create("axi2reg_predictor", this);
`endif

    /** Create RAL Models */
    // soc_mgmt RAL Model
    if (soc_mgmt_regmodel == null)
    begin
      soc_mgmt_regmodel = soc_mgmt_reg_block::type_id::create("soc_mgmt_regmodel");
      soc_mgmt_regmodel.set_hdl_path_root(hdl_path);
      soc_mgmt_regmodel.build(0); //need to change according to spec
      soc_mgmt_regmodel.lock_model();
      uvm_config_db#(uvm_reg_block)::set(this,"axi_system_env.master[0]", "axi_regmodel", soc_mgmt_regmodel);
      soc_mgmt_regmodel.default_map.set_auto_predict(1);
      soc_mgmt_regmodel.default_map.set_check_on_read(1);
      `uvm_info("build_phase", "soc_mgmt Reg Model (Reg Model) created", UVM_LOW)
    end
    else
      `uvm_error("ENV_BUILD_PHASE", "Unable to build Reg Model");

    // Connect the register model
    sequencer.regmodel = soc_mgmt_regmodel;

    soc_mgmt_ref_model_h = soc_mgmt_ref_model::type_id::create("soc_mgmt_ref_model_h", this);

    soc_mgmt_func_cov_h = soc_mgmt_func_cov::type_id::create("soc_mgmt_func_cov_h", this);
    

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    /**
    * Connect the master and slave agent's analysis ports with
    * item_observed_before_export and item_observed_after_export ports of the
    * scoreboard.*/
    //axi_system_env.master[0].monitor.item_observed_port.connect(
        //soc_mgmt_scoreboard.item_observed_initiated_export);
    //axi_system_env.slave[0].monitor.item_observed_port.connect(
        //soc_mgmt_scoreboard.item_observed_response_export);
`ifdef EXPLICIT_PREDICTOR
    // Explicit reg predictor
    axi2reg_predictor.map     = soc_mgmt_regmodel.get_default_map();
    axi2reg_predictor.adapter = axi_system_env.master[0].reg2axi_adapter;
    soc_mgmt_regmodel.default_map.set_auto_predict(0);
    axi_system_env.master[0].monitor.item_observed_port.connect(axi2reg_predictor.bus_in);
`endif
    if (m_env_cfg.has_scoreboard) begin
      axi_system_env.slave[0].monitor.item_observed_port.connect(soc_mgmt_scoreboard_h.actual_data_export);

      //currently reference model is not functioning
      //TODO : to update in future when scoreboarding is funtioning (#2006)
      //soc_mgmt_ref_model_h.ref_model_2_sb_expected_data_port.connect(soc_mgmt_scoreboard_h.expected_data_export);
    end
    //connect ral model to ref model
     soc_mgmt_ref_model_h.soc_mgmt_regmodel=soc_mgmt_regmodel;
    //connect ral model to ref model
     soc_mgmt_func_cov_h.soc_mgmt_regmodel=soc_mgmt_regmodel;
  endfunction : connect_phase

   // Reset the register model
   task reset_phase(uvm_phase phase);
     phase.raise_objection(this, "Resetting regmodel");
     // =======================================================================================================================
     // RAL Models reset
     // =======================================================================================================================
     soc_mgmt_regmodel.reset();
     phase.drop_objection(this);
   endtask

endclass : soc_mgmt_env

`endif  // GUARD_SOC_MGMT_ENV_SV
