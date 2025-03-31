/**
 * Abstract:
 * class 'iau_env' is extended from uvm_env base class.  It implements
 * the build phase to construct the structural elements of this environment.
 *
 * iau_env is the testbench environment, which constructs the AXI System
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
`ifndef GUARD_IAU_ENV_SV
`define GUARD_IAU_ENV_SV


// IAU_DPU environment class
class iau_env extends uvm_env;

  // IAU_DPU environment configuration
  iau_env_cfg                      env_cfg;

  /** AXI System ENV */
  svt_axi_system_env                   axi_system_env;

  /** Virtual Sequencer */
  axi_virtual_sequencer                sequencer;

  /** AXI System Configuration */
  cust_svt_axi_system_configuration    cfg;


  /** IAU Components */
  iau_agent      iau_agt;
  iau_ref_model  iau_mdl;
  iau_func_cov   iau_cov;
  iau_scoreboard iau_scb;

  /** Token manager interface agent */
  token_agent             tok_agt;


  /** ICDF Test Scoreboard */
  axi_icdf_scoreboard axi_icdf_scb;

  //** IAU_RAL MODEL */
  IAU_RAL regmodel;

  // HDL path to IAU_RAL register model
  string hdl_path;


  /** IAU_Interface for sync b/w test and scoreboard's icdf task execution */
  virtual iau_if iau_vif;

  // UVM built in register predictor
  //uvm_reg_predictor # (cust_svt_axi_master_transaction) m_builtin_reg_predictor;

  /** UVM Component Utility macro */
  `uvm_component_utils(iau_env)

  /** Class Constructor */
  function new(string name = "iau_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    /**
     * Check if the configuration is passed to the environment.
     * If not then create the configuration and pass it to the agent.
     */

    if (!uvm_config_db#(iau_env_cfg)::get(this, "", "m_env_cfg", env_cfg))
      `uvm_fatal(get_full_name(), "Failed to get env_cfg from config_db")

    if(uvm_config_db#(cust_svt_axi_system_configuration)::get(this, "", "cfg", cfg)) begin
      /** Apply the configuration to the System ENV */
      `uvm_info(get_type_name(),
                $sformatf("cust_svt_axi_system_configuration collected and passed to the axi env"),
                UVM_LOW)

      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env*", "cfg", cfg);
    end
    // No configuration passed from test
    else
    begin
      cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
      /** Apply the configuration to the System ENV */
      `uvm_info(get_type_name(), $sformatf(
                "cust_svt_axi_system_configuration created and passed to the axi env"), UVM_LOW)
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env*", "cfg", cfg);
    end


    if(!uvm_config_db#(virtual iau_if)::get(this, "", "iau_vif", iau_vif))
      `uvm_fatal(get_full_name(), "Failed to get iau_vif handle from config_db in iau_env")

    if (regmodel == null) begin
      `uvm_info(get_type_name(), $sformatf("regmodel is null, creating one"), UVM_LOW)
      regmodel = IAU_RAL::type_id::create("regmodel");

      regmodel.set_hdl_path_root(hdl_path);
      regmodel.build(IAU_CSR_ADDR_ST);
      regmodel.lock_model();
      uvm_config_db#(uvm_reg_block)::set(this, "axi_system_env.master[0]", "axi_regmodel", regmodel);
      regmodel.default_map.set_auto_predict(1);
      regmodel.default_map.set_check_on_read(1);
    end
    /** Construct the system agent */
    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);

    /** Construct the virtual sequencer */
    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);


    // Connecting regmodel to axi virtual sequencer
    sequencer.regmodel = regmodel;
    sequencer.env = this;

    iau_agt = iau_agent::type_id::create("iau_agt", this);
    if (env_cfg.has_iau_scoreboard) begin
      iau_mdl = iau_ref_model::type_id::create("iau_mdl", this);
      iau_scb = iau_scoreboard::type_id::create("iau_scb", this);
      iau_mdl.regmodel = regmodel;
    end

    if (env_cfg.has_coverage) begin
      iau_cov = iau_func_cov::type_id::create("iau_cov", this);
      iau_cov.regmodel = regmodel;
    end

    tok_agt = token_agent::type_id::create("tok_agt", this);

    if (uvm_root::get().find("uvm_test_top").get_type_name() == "iau_icdf_test") begin
      axi_icdf_scb = axi_icdf_scoreboard::type_id::create("axi_icdf_scb", this);
    end

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  virtual task reset_phase(uvm_phase phase);
    phase.raise_objection(this, "Resetting regmodel");
    regmodel.reset();
    phase.drop_objection(this);
  endtask

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
   
    //axi stream input and output to axi icdf scoreboarad
    if (uvm_root::get().find("uvm_test_top").get_type_name() == "iau_icdf_test") begin
      axi_system_env.slave[0].monitor.item_observed_port.connect(axi_icdf_scb.item_observed_out_stream_export);
    end


    if (env_cfg.has_iau_scoreboard && !env_cfg.axi_test) begin
      //axi monitors connect to IAU ref model
      iau_agt.mon.ap.connect(iau_mdl.taf_mon_iau.analysis_export);
      axi_system_env.master[0].monitor.item_observed_port.connect(iau_mdl.taf_mon_cfg.analysis_export);
      axi_system_env.master[1].monitor.item_observed_port.connect(iau_mdl.taf_mon_data.analysis_export);

      axi_system_env.slave[0].monitor.item_observed_port.connect(iau_scb.taf_mon.analysis_export);
  
      //IAU ref model outputs connect to IAU scoreboard 
      iau_mdl.ap_stream_out.connect(iau_scb.taf_mdl.analysis_export);
      iau_agt.mon.ap.connect(iau_scb.taf_iau_mon.analysis_export);
      iau_mdl.ap_iau_out.connect(iau_scb.taf_iau_mdl.analysis_export);

      //token connection
      tok_agt.m_tok_mon.ap.connect(iau_scb.taf_mon_tok.analysis_export);
      iau_mdl.ap_tok_out.connect(iau_scb.taf_mdl_tok.analysis_export);
    end


    if (env_cfg.has_coverage && !env_cfg.axi_test) begin
      axi_system_env.master[0].monitor.item_observed_port.connect(iau_cov.taf_mon_cfg.analysis_export);
      axi_system_env.master[1].monitor.item_observed_port.connect(iau_cov.taf_mon_data.analysis_export);
      tok_agt.m_tok_mon.ap.connect(iau_cov.taf_mon_tok.analysis_export);
    end
  endfunction : connect_phase

endclass

`endif  // GUARD_IAU_ENV_SV
