`ifndef GUARD_DPU_ENV_SV
`define GUARD_DPU_ENV_SV

// dpu environment class
class dpu_env extends uvm_env;

  dpu_env_cfg env_cfg;

  svt_axi_system_env axi_system_env;

  axi_virtual_sequencer sequencer;

  cust_svt_axi_system_configuration cfg;

  dpu_func_cov    dpu_cov;
  dpu_scoreboard	dpu_scb;
  dpu_ref_model 	dpu_mdl;
  dpu_agent       dpu_agt;

  token_agent tok_agt;

  /** ICDF Test Scoreboard */
  axi_icdf_scoreboard axi_icdf_scb;


  DPU_RAL regmodel;

  virtual iid_if iid_if_i;

  string hdl_path;


  `uvm_component_utils(dpu_env)


  function new(string name = "dpu_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (!uvm_config_db#(dpu_env_cfg)::get(this, "", "m_env_cfg", env_cfg))
      `uvm_fatal(get_full_name(), "Failed to get env_cfg from config_db")

    uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env*", "cfg", cfg);

    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
    uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env*", "cfg", cfg);

    if (!uvm_config_db#(virtual iid_if)::get(this, "", "iid_if_i", iid_if_i))
      `uvm_fatal(get_full_name(), "Failed to get iid_if_i from config_db")

    if (regmodel == null) begin
      `uvm_info(get_type_name(), $sformatf("regmodel is null, creating one"), UVM_LOW)
      regmodel = DPU_RAL::type_id::create("regmodel");

      regmodel.set_hdl_path_root(hdl_path);
      regmodel.build(DPU_CSR_ADDR_ST);
      regmodel.lock_model();
      uvm_config_db#(uvm_reg_block)::set(this, "axi_system_env.master[0]", "axi_regmodel", regmodel);
      regmodel.default_map.set_auto_predict(1);
      regmodel.default_map.set_check_on_read(1);
    end

    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);

    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);
    sequencer.regmodel = regmodel;
    sequencer.env = this;

    dpu_agt = dpu_agent::type_id::create("dpu_agt", this);
    if (env_cfg.has_scoreboard) begin
      dpu_mdl = dpu_ref_model::type_id::create("dpu_mdl" , this);
      dpu_scb = dpu_scoreboard::type_id::create("dpu_scb", this);
      dpu_mdl.regmodel = regmodel;
    end

    if (env_cfg.has_coverage) begin
      dpu_cov = dpu_func_cov::type_id::create("dpu_cov", this);
      dpu_cov.regmodel = regmodel;
    end

    tok_agt = token_agent::type_id::create("tok_agt", this);

    if (uvm_root::get().find("uvm_test_top").get_type_name() == "dpu_icdf_test") begin
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
    if (uvm_root::get().find("uvm_test_top").get_type_name() == "dpu_icdf_test") begin
      axi_system_env.slave[0].monitor.item_observed_port.connect(axi_icdf_scb.item_observed_out_stream_export);
    end
    else if (env_cfg.has_scoreboard) begin
      if (uvm_root::get().find("uvm_test_top").get_type_name() != "dpu_register_test" &&
          uvm_root::get().find("uvm_test_top").get_type_name() != "dpu_irq_test") begin
        //DPU scoreboard and ref_model connections
        axi_system_env.master[0].monitor.item_observed_port.connect(dpu_mdl.taf_mon_cfg.analysis_export); // Config Axi Interface
        axi_system_env.master[1].monitor.item_observed_port.connect(dpu_mdl.taf_mon_s0_data.analysis_export); // IFD0 Axi Stream input to DPU
        axi_system_env.master[2].monitor.item_observed_port.connect(dpu_mdl.taf_mon_s1_data.analysis_export); // IFD1 Axi Stream input to DPU

        axi_system_env.slave[0].monitor.item_observed_port.connect(dpu_scb.taf_mon.analysis_export); 
        dpu_mdl.ap_stream_out.connect(dpu_scb.taf_mdl.analysis_export); 
        tok_agt.m_tok_mon.ap.connect(dpu_scb.taf_mon_tok.analysis_export);
        dpu_mdl.ap_tok_out.connect(dpu_scb.taf_mdl_tok.analysis_export);

        dpu_agt.mon.ap.connect(dpu_scb.taf_dpu_mon.analysis_export);
        dpu_mdl.ap_dpu_out.connect(dpu_scb.taf_dpu_mdl.analysis_export);
      end
    end
    if (env_cfg.has_coverage) begin
    //  axi_system_env.master[0].monitor.item_observed_port.connect(dpu_cov.taf_mon_cfg.analysis_export);
    //  tok_agt.m_tok_mon.ap.connect(dpu_cov.taf_mon_tok.analysis_export);
    end


  endfunction : connect_phase

endclass

`endif
