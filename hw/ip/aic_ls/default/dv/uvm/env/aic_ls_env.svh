/**
 * Abstract:
 */
`ifndef GUARD_AIC_LS_ENV_SV
`define GUARD_AIC_LS_ENV_SV

`define EXPLICIT_PREDICTOR

// AI CORE LS environment class
class aic_ls_env extends uvm_env;

  `uvm_component_utils(aic_ls_env)

  typedef aic_ls_subsys_reg_block LS_RAL;
  typedef aic_ls_ral#(AIC_LS_ENV_AXI_CFG_ADDR_W, AIC_LS_ENV_AXI_CFG_DATA_W) aic_ls_ral_t;
  typedef mmio_agent#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH) mmio_agent_t;
  typedef rvv_agent#(MMIO_RVV_DATA_WIDTH, MMIO_RVV_ADDR_WIDTH) rvv_agent_t;


  string                  m_hdl_path = "hdl_top.dut.u_aic_ls.u_dmc";   // HDL path to RAL register model
  aic_ls_env_cfg          m_env_cfg;
  svt_axi_system_env          m_axi_system_env;
  axi_virtual_sequencer       m_axi_virt_sqr;
  aic_ls_axi_system_cfg   m_axi_sys_cfg;
  dmc_addr_gen_cfg        m_dmc_cfg;
  aic_ls_agent_cfg        m_aic_ls_cfg;

  aic_ls_agent            m_aic_ls_agt;
  dmc_addr_gen_agent      m_dmc_agt[AIC_LS_ENV_DMC_NUM_DEVICE];
  dmc_addr_gen_ref_model  m_dmc_ref_mdl[AIC_LS_ENV_DMC_NUM_DEVICE];
  dmc_addr_gen_scoreboard m_dmc_addr_scb[AIC_LS_ENV_DMC_NUM_DEVICE];
  dmc_data_scoreboard     m_dmc_data_scb[AIC_LS_ENV_DMC_NUM_DEVICE];
  token_agent                 m_token_agents[string];
  token_agent_config          m_token_agents_cfg[string];

  mmio_agent_t                  m_mmio_agt[string];
  rvv_agent_t                   m_rvv_agent;
  rvv_config                    m_rvv_cfg;
  /// icdf scoreboard - used only in icdf test.
  axi_icdf_scoreboard axi_icdf_scb[AIC_LS_ENV_IFD_NUM_DEVICE];


  aic_ls_coverage         m_cov;
  // AI Core LS RAL Model
  aic_ls_subsys_reg_block m_ls_regmodel;
  uvm_reg_predictor#(svt_axi_transaction) m_cfg_axi2reg_predictor;
  aic_ls_ral_t            m_ral;

  function new(string name = "aic_ls_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void connect_token_agent();
    string token_connection_name;
    // we need to create token agent for each connection - all IFDs/ODRs to everything else!
    for (int i=0; i<AIC_LS_ENV_DMC_NUM_DEVICE; i++) begin //going through all IFDs/ODRs
      for(int j=0; j<AIC_LS_ENV_DMC_NUM_DEVICE+AIC_LS_ENV_TOKEN_VECTOR_OTHER_CONN_NUM; j++) begin
        if (i==j) continue;
        if (j<AIC_LS_ENV_DMC_NUM_DEVICE) begin
          token_connection_name = $sformatf("tkn_%s_to_%s", AIC_LS_ENV_TOKEN_VECTOR_DMC_CONNECTIONS[i], AIC_LS_ENV_TOKEN_VECTOR_DMC_CONNECTIONS[j]);
        end else begin
          token_connection_name = $sformatf("tkn_%s_to_%s", AIC_LS_ENV_TOKEN_VECTOR_DMC_CONNECTIONS[i], AIC_LS_ENV_TOKEN_VECTOR_OTHER_CONNECTIONS[j-AIC_LS_ENV_DMC_NUM_DEVICE]);
        end
        //create token agent configurations
        m_token_agents_cfg[token_connection_name] = token_agent_config::type_id::create(token_connection_name);
        m_token_agents_cfg[token_connection_name].m_b_init_reset = 1; // avoid garbage data when tkn mgr reset has not yet been done
        m_token_agents_cfg[token_connection_name].m_b_active = 1;
        //setting configuration to objects below agent
        uvm_config_db#( token_agent_config )::set( .cntxt( this ), .inst_name( token_connection_name ), .field_name( "tok_agt_cfg" ), .value( m_token_agents_cfg[token_connection_name]) );
        m_token_agents[token_connection_name] = token_agent::type_id::create(token_connection_name, this);
        `uvm_info(get_name(), $sformatf("TokenAgent[%0d][%0d] %s created!", i, j, token_connection_name), UVM_LOW)
      end
    end
  endfunction

  virtual function void build_mmio_agents();
    for (int i=0; i < AIC_LS_ENV_DMC_NUM_DEVICE; i++) begin
      m_mmio_agt[$sformatf("dmc_%s", AIC_LS_DMC_DEVICE_NAME[i])] = mmio_agent_t::type_id::create($sformatf("mmio_dmc_%s", AIC_LS_DMC_DEVICE_NAME[i]), this);
    end
    m_mmio_agt["axi_wr"] = mmio_agent_t::type_id::create("mmio_axi_wr", this);
    m_mmio_agt["axi_rd"] = mmio_agent_t::type_id::create("mmio_axi_rd", this);
    `ifndef AI_CORE_TOP_ENV_CHECK
     m_rvv_agent = rvv_agent_t::type_id::create("m_rvv", this);
     m_rvv_cfg = rvv_config::type_id::create("m_rvv_cfg",this);
     // Setting up configuration for RVV agent
     m_rvv_cfg.connections_num = 8;
     m_rvv_cfg.data_width = AIC_LS_ENV_RVV_DATA_WIDTH;
     m_rvv_cfg.addr_width = AIC_LS_ENV_RVV_ADDR_WIDTH;
     m_rvv_cfg.wbe_width = (AIC_LS_ENV_RVV_WBE_WIDTH + 7) / 8;
     m_rvv_cfg.m_has_scoreboard = 1;
     m_rvv_cfg.banks_num = AIC_LS_ENV_L1_NUM_BANKS;
     m_rvv_cfg.sub_banks_num = AIC_LS_ENV_L1_NUM_SUB_BANKS;
     m_rvv_cfg.m_memory_path = m_env_cfg.m_l1_mem_root_path;
     uvm_config_db#(rvv_config)::set( .cntxt( this ), .inst_name( "m_rvv" ), .field_name( "m_rvv_cfg" ), .value( m_rvv_cfg ) ); // setting cfg so it can be later retrieved in rvv_agent!
    `endif
  endfunction

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (m_env_cfg == null) begin
      if (!uvm_config_db#(aic_ls_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg))  begin
        `uvm_error("ENV_BUILD_PHASE", "Unable to find environment configuration object in the uvm_config_db");
      end
    end

    if (uvm_config_db#(aic_ls_axi_system_cfg)::get(this, "", "cfg", m_axi_sys_cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", m_axi_sys_cfg);
    end  else begin
      // No configuration passed from test
      m_axi_sys_cfg = aic_ls_axi_system_cfg::type_id::create("m_axi_sys_cfg");
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "m_axi_system_env", "cfg", m_axi_sys_cfg);
    end

    m_axi_system_env = svt_axi_system_env::type_id::create("m_axi_system_env", this);

    m_axi_virt_sqr = axi_virtual_sequencer::type_id::create("m_axi_virt_sqr", this);

    m_dmc_cfg = dmc_addr_gen_cfg::type_id::create("m_dmc_addr_gen_cfg", this);
    m_dmc_cfg.is_active = 0;

    m_aic_ls_cfg = aic_ls_agent_cfg::type_id::create("m_aic_ls_cfg", this);
    m_aic_ls_cfg.is_active = 0;
    m_aic_ls_agt = aic_ls_agent::type_id::create("m_aic_ls_agt" , this);
    uvm_config_db #(aic_ls_agent_cfg)::set(this, "m_aic_ls_agt", "cfg", m_aic_ls_cfg);

    for (int i=0; i < AIC_LS_ENV_DMC_NUM_DEVICE; i++) begin
      m_dmc_agt[i] = dmc_addr_gen_agent::type_id::create($sformatf("m_%s_agt", AIC_LS_DMC_DEVICE_NAME[i]), this);
      uvm_config_db #(dmc_addr_gen_cfg)::set(this, $sformatf("m_%s_agt", AIC_LS_DMC_DEVICE_NAME[i]), "cfg", m_dmc_cfg);
      if (m_env_cfg.m_has_scoreboard) begin
        m_dmc_addr_scb[i] = dmc_addr_gen_scoreboard::type_id::create($sformatf("m_%s_addr_scb", AIC_LS_DMC_DEVICE_NAME[i]), this);
        m_dmc_data_scb[i] = dmc_data_scoreboard::type_id::create($sformatf("m_%s_data_scb", AIC_LS_DMC_DEVICE_NAME[i]), this);
        m_dmc_data_scb[i].m_ai_core_cid = m_env_cfg.m_cid;
        if (AIC_LS_DMC_DEVICE_NAME[i] inside {"m_odr", "d_odr", "m_ifdw"}) begin
          m_dmc_data_scb[i].m_has_vtrsp = 1;
          if (AIC_LS_DMC_DEVICE_NAME[i] inside {"m_odr", "d_odr"}) m_dmc_data_scb[i].m_is_ifd_not_odr = 0;
        end
      end
      m_dmc_ref_mdl[i] = dmc_addr_gen_ref_model::type_id::create($sformatf("m_%s_ref_mdl", AIC_LS_DMC_DEVICE_NAME[i]), this);
    end

    `ifndef AI_CORE_TOP_ENV_CHECK
    connect_token_agent();
    `endif
    build_mmio_agents();

    if (m_env_cfg.m_has_coverage)
      m_cov = aic_ls_coverage::type_id::create("m_cov", this);

    m_cfg_axi2reg_predictor    = uvm_reg_predictor#(svt_axi_transaction)::type_id::create("m_cfg_axi2reg_predictor", this);

    m_ls_regmodel = LS_RAL::type_id::create("m_ls_regmodel");
    m_ls_regmodel.configure();
    m_ls_regmodel.build(`AI_LS_BASE_ADDR);
    m_ls_regmodel.lock_model();
    m_ls_regmodel.reset();
    uvm_config_db#(uvm_reg_block)::set(this,"m_axi_system_env.master[0]", "axi_regmodel", m_ls_regmodel);
    uvm_config_db#(aic_ls_subsys_reg_block)::set(this, "m_ral", "ls_regmodel", m_ls_regmodel);
    m_ls_regmodel.default_map.set_auto_predict(1);
    m_ls_regmodel.default_map.set_check_on_read(1);
    `uvm_info(get_name(), "build_phase: AI Core LS Reg Model (Reg Model) created", UVM_LOW)

    m_axi_virt_sqr.regmodel = m_ls_regmodel;
    m_ral = aic_ls_ral_t::type_id::create("m_ral", this);
    uvm_config_db#(aic_ls_ral_t)::set(null, "*", "ls_ral", m_ral);

    // Create icdf scoreboard
    //axi stream input and output to axi icdf scoreboarad
    if (uvm_root::get().find("uvm_test_top").get_type_name() == "aic_ls_icdf_stimuli_test") begin
      `uvm_info(get_name, "creating axi_icdf_scb!", UVM_LOW)
      axi_icdf_scb[0] = axi_icdf_scoreboard::type_id::create("m_m_ifd0_scb", this);
      axi_icdf_scb[1] = axi_icdf_scoreboard::type_id::create("m_m_ifd1_scb", this);
      axi_icdf_scb[2] = axi_icdf_scoreboard::type_id::create("m_m_ifd2_scb", this);
      axi_icdf_scb[3] = axi_icdf_scoreboard::type_id::create("m_m_ifdw_scb", this);
      axi_icdf_scb[4] = axi_icdf_scoreboard::type_id::create("m_d_ifd0_scb", this);
      axi_icdf_scb[5] = axi_icdf_scoreboard::type_id::create("m_d_ifd1_scb", this);
    end

    `uvm_info(get_name(), "Exiting build_phase...", UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info(get_name, "Entered connect_phase...", UVM_LOW)
    if (m_env_cfg.m_has_scoreboard) begin

      //axi stream input and output to axi icdf scoreboarad, in case of axi icdf stimuli test
      if (uvm_root::get().find("uvm_test_top").get_type_name() == "aic_ls_icdf_stimuli_test") begin
        `uvm_info(get_name, "connecting slaves to axi_icdf_scb!", UVM_LOW)
        m_axi_system_env.slave[0].monitor.item_observed_port.connect(axi_icdf_scb[0].item_observed_out_stream_export);
        m_axi_system_env.slave[1].monitor.item_observed_port.connect(axi_icdf_scb[1].item_observed_out_stream_export);
        m_axi_system_env.slave[2].monitor.item_observed_port.connect(axi_icdf_scb[2].item_observed_out_stream_export);
        m_axi_system_env.slave[3].monitor.item_observed_port.connect(axi_icdf_scb[3].item_observed_out_stream_export);
        m_axi_system_env.slave[4].monitor.item_observed_port.connect(axi_icdf_scb[4].item_observed_out_stream_export);
        m_axi_system_env.slave[5].monitor.item_observed_port.connect(axi_icdf_scb[5].item_observed_out_stream_export);
      end else begin
        for (int i=0; i < AIC_LS_ENV_DMC_NUM_DEVICE; i++) begin
          case (i)
            0: m_axi_system_env.slave[0].monitor.item_observed_port.connect(m_dmc_data_scb[i].m_axis_tfifo.analysis_export); // mvm_ifd0
            1: m_axi_system_env.slave[1].monitor.item_observed_port.connect(m_dmc_data_scb[i].m_axis_tfifo.analysis_export); // mvm_ifd1
            2: m_axi_system_env.slave[2].monitor.item_observed_port.connect(m_dmc_data_scb[i].m_axis_tfifo.analysis_export); // mvm_ifd2
            3: m_axi_system_env.slave[3].monitor.item_observed_port.connect(m_dmc_data_scb[i].m_axis_tfifo.analysis_export); // mvm_ifdw
            4: m_axi_system_env.slave[4].monitor.item_observed_port.connect(m_dmc_data_scb[i].m_axis_tfifo.analysis_export); // dwpu_ifd0
            5: m_axi_system_env.slave[5].monitor.item_observed_port.connect(m_dmc_data_scb[i].m_axis_tfifo.analysis_export); // dwpu_ifd1
            6: m_axi_system_env.master[2].monitor.item_observed_port.connect(m_dmc_data_scb[i].m_axis_tfifo.analysis_export); // mvm_odr
            7: m_axi_system_env.master[3].monitor.item_observed_port.connect(m_dmc_data_scb[i].m_axis_tfifo.analysis_export); // dwpu_odr
          endcase
          m_dmc_agt[i].mon.ag_ap.connect(m_dmc_ref_mdl[i].cmd_in.analysis_export);
          m_dmc_agt[i].mon.dpc_ap.connect(m_dmc_addr_scb[i].act_fifo.analysis_export);
          m_dmc_ref_mdl[i].cmd_out.connect(m_dmc_addr_scb[i].exp_fifo.analysis_export);
          m_dmc_ref_mdl[i].cmd_out.connect(m_dmc_data_scb[i].m_addr_in_fifo.analysis_export);
          if (m_dmc_data_scb[i].m_has_vtrsp && m_dmc_ref_mdl[i].vtrsp_out!= null) begin
            m_dmc_ref_mdl[i].vtrsp_out.connect(m_dmc_data_scb[i].m_vtrsp_in_fifo.analysis_export);
          end
        end
      end
    end

    if (m_env_cfg.m_has_coverage) begin
      m_aic_ls_agt.mon.ap.connect (m_cov.taf_mon_aic_ls.analysis_export);

      for (int i=0; i < AIC_LS_ENV_DMC_NUM_DEVICE; i++) begin
        //m_dmc_agt[i].mon.ag_ap.connect  (m_cov.taf_mon_dmc_ag[i].analysis_export);
        m_dmc_ref_mdl[i].cmd_out.connect  (m_cov.taf_mon_dmc_ag[i].analysis_export);
        m_dmc_agt[i].mon.dpc_ap.connect (m_cov.taf_mon_dmc_dpc[i].analysis_export);
        m_mmio_agt[$sformatf("dmc_%s", AIC_LS_DMC_DEVICE_NAME[i])].m_mon.ap.connect (m_cov.taf_mon_dmc_mmio[i].analysis_export);

      end
      `ifndef AI_CORE_TOP_ENV_CHECK
      for (int i=0; i < AIC_LS_ENV_RVV_CONNECTIONS; i++) begin  // create RVV mmio ports coverage connections
        m_rvv_agent.m_mmio_agents[i].m_mon.ap.connect (m_cov.taf_mon_rvv_mmio[i].analysis_export);
      end
      `endif
      m_mmio_agt["axi_wr"].m_mon.ap.connect(m_cov.taf_mon_dmc_axi2mmio[0].analysis_export);
      m_mmio_agt["axi_rd"].m_mon.ap.connect(m_cov.taf_mon_dmc_axi2mmio[1].analysis_export);

      m_axi_system_env.master[0].monitor.item_observed_port.connect(m_cov.taf_mon_axi_cfg.analysis_export);
      //slave if used to internal l1 access
      m_axi_system_env.master[1].monitor.item_observed_port.connect(m_cov.taf_mon_axi_hp_slv.analysis_export);
      //master if used to external access
      m_axi_system_env.slave[0].monitor.item_observed_port.connect (m_cov.taf_mon_axi_hp_mst.analysis_export);
    end

    m_cfg_axi2reg_predictor.map     = m_ls_regmodel.get_default_map();
    m_cfg_axi2reg_predictor.adapter = m_axi_system_env.master[0].reg2axi_adapter;
    m_axi_system_env.master[0].monitor.item_observed_port.connect(m_cfg_axi2reg_predictor.bus_in);

    // backdoor settings
    m_ls_regmodel.set_hdl_path_root(m_hdl_path);
    `uvm_info(get_name, "Exiting connect_phase...", UVM_LOW)
  endfunction : connect_phase

  function void reset_addr_gen_refmodel();
    foreach (m_dmc_ref_mdl[i]) begin
      m_dmc_ref_mdl[i].m_stream_info_q.delete(); // reset addr length queue for all address gen
    end
  endfunction

  function void set_l1_base_addr(mem_baseaddr_t l1_base_addr);
    foreach (m_dmc_agt[i]) begin
       m_dmc_agt[i].mon.l1_base_addr = l1_base_addr;
    end
  endfunction
endclass : aic_ls_env

`endif  // GUARD_AIC_LS_ENV_SV


