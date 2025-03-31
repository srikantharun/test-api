/**
 * Abstract:
 */
`ifndef DMA_IP_ENV_SV
`define DMA_IP_ENV_SV

`define EXPLICIT_PREDICTOR

// DMA IP environment class
class dma_ip_env extends uvm_env;

  // HDL path to RAL register model
  string hdl_path;

  /** UVM Component Utility macro */
  `uvm_component_utils_begin(dma_ip_env)
    `uvm_field_string(hdl_path, UVM_DEFAULT)
  `uvm_component_utils_end

  // AI CORE MVM environment configuration
  dma_ip_env_config m_env_cfg;

  /** AXI System ENV */
  svt_axi_system_env axi_system_env;

  /** Virtual Sequencer */
  axi_virtual_sequencer sequencer;

  /** AXI System Configuration */
  axi_vip_config axi_vip_cfg;
  
  // DMA Irq Agent (Monitors IRQ lines and generates status on anaylysis ports)
  irq_agent  m_dma_irq_agent;

  // DMA Transfer Scoreboard
  dma_ip_transfer_scoreboard  m_dma_transfer_scbd;

  // DMA IP RAL Model
  dma_ip_reg_block  dma_ip_regmodel;

   /** ai_core_mvm_ref model */
//   ai_core_mvm_ref_model 	ai_core_mvm_ref_model_h;
   /** ai_core_mvm_func_cov */
//   ai_core_mvm_func_cov 	ai_core_mvm_func_cov_h;
  
  /** Token agent
  * Bi-dimensional array with first dimension with 2 positions (one for Execution and other for Program).
  * Since both (Execution and Program) have the same number of tokens, and the number of consumer tokens is equal to producer tokens the macro MVM_EXE_NR_TOK_CONS was used to define the second dimension */


`ifdef EXPLICIT_PREDICTOR
  // Explicit/Manual predictor
  // By default, the svt_axi_master_agent enables the auto reg prediction in the connect_phase. Enabling the manual/explicit
  // reg prediction is useful when the registers also get updated by normal transactions and not through reg sequence
  uvm_reg_predictor#(svt_axi_transaction) axi2reg_predictor;
`endif

  /** Class Constructor */
  function new(string name = "dma_ip_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  /** Build the AXI System ENV */
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (m_env_cfg == null)
    begin
      if (!uvm_config_db#(dma_ip_env_config)::get(this, "", "m_env_cfg", m_env_cfg))
      begin
        `uvm_error("ENV_BUILD_PHASE", "Unable to find environment configuration object in the uvm_config_db");
      end
    end

    /**
     * Check if the configuration is passed to the environment.
     * If not then create the configuration and pass it to the agent.
     */

    // Configuration created through core consultant
    if (uvm_config_db#(axi_vip_config)::get(this, "", "cfg", axi_vip_cfg)) begin
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", axi_vip_cfg);
    end
    // No configuration passed from test
    else
    begin
      axi_vip_cfg = axi_vip_config::type_id::create("axi_vip_cfg");
      /** Apply the configuration to the System ENV */
      uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", axi_vip_cfg);
    end

    /** Construct the system agent */
    axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);

    /** Construct the virtual sequencer */
    sequencer = axi_virtual_sequencer::type_id::create("sequencer", this);

    /* Create the scoreboard */
    m_dma_transfer_scbd = dma_ip_transfer_scoreboard::type_id::create("m_dma_transfer_scbd", this);

`ifdef EXPLICIT_PREDICTOR
    // Predictor
    axi2reg_predictor = uvm_reg_predictor#(svt_axi_transaction)::type_id::create("axi2reg_predictor", this);
`endif

    /** Create RAL Models */
    // DMA I{ RAL Model
    if (dma_ip_regmodel == null)
    begin
      dma_ip_regmodel = dma_ip_reg_block::type_id::create("dma_ip_regmodel");
      dma_ip_regmodel.set_hdl_path_root(hdl_path);
      dma_ip_regmodel.build(null);  
      dma_ip_regmodel.lock_model();
      uvm_config_db#(uvm_reg_block)::set(this,"axi_system_env.master[0]", "axi_regmodel", dma_ip_regmodel);
      dma_ip_regmodel.default_map.set_auto_predict(1);
      dma_ip_regmodel.default_map.set_check_on_read(1);
      `uvm_info("build_phase", "DMA_IP Reg Model (Reg Model) created", UVM_LOW)
    end
    else
      `uvm_error("ENV_BUILD_PHASE", "Unable to build DMA_IP Reg Model");

    // Connect the register model
    sequencer.dma_ip_regmodel = dma_ip_regmodel;
    m_dma_transfer_scbd.dma_ip_regmodel = dma_ip_regmodel;

//    ai_core_mvm_ref_model_h = ai_core_mvm_ref_model::type_id::create("ai_core_mvm_ref_model_h", this);

//    ai_core_mvm_func_cov_h = ai_core_mvm_func_cov::type_id::create("ai_core_mvm_func_cov_h", this);
    

    // DMA IRQ Agent
    m_dma_irq_agent = irq_agent::type_id::create("m_dma_irq_agent",this);


    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    `uvm_info("connect_phase", "Entered...", UVM_LOW)
    /**
    * Connect the master and slave agent's analysis ports with
    * item_observed_before_export and item_observed_after_export ports of the
    * scoreboard.*/
    //axi_system_env.master[0].monitor.item_observed_port.connect(
        //dma_scoreboard.item_observed_initiated_export);
    //axi_system_env.slave[0].monitor.item_observed_port.connect(
        //dma_scoreboard.item_observed_response_export);

`ifdef EXPLICIT_PREDICTOR
    // Explicit reg predictor  - TBD What is this for ???
    axi2reg_predictor.map     = dma_ip_regmodel.get_default_map();
    axi2reg_predictor.adapter = axi_system_env.master[0].reg2axi_adapter;
    dma_ip_regmodel.default_map.set_auto_predict(0);
    axi_system_env.master[0].monitor.item_observed_port.connect(axi2reg_predictor.bus_in);
`endif

//    if (m_env_cfg.has_scoreboard) begin
//      axi_system_env.master[0].monitor.item_observed_port.connect(ai_core_mvm_ref_model_h.axi4_lp_2_ref_model_export);
//      axi_system_env.master[1].monitor.item_observed_port.connect(ai_core_mvm_ref_model_h.axis_ifdw_2_ref_model_export);
//      axi_system_env.master[2].monitor.item_observed_port.connect(ai_core_mvm_ref_model_h.axis_ifd0_2_ref_model_export);
//      axi_system_env.slave[0].monitor.item_observed_port.connect(dma_scoreboard.actual_data_export);
//      ai_core_mvm_ref_model_h.ref_model_2_sb_expected_data_port.connect(dma_scoreboard.expected_data_export);
      // Func coverage
//      axi_system_env.master[0].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axi4_lp_2_func_cov_export);
//      axi_system_env.master[1].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axis_ifdw_2_func_cov_export);
//      axi_system_env.master[2].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axis_ifd0_2_func_cov_export);
//      axi_system_env.slave[0].monitor.item_observed_port.connect(ai_core_mvm_func_cov_h.axi4_iau_data_export);
//    end

    // -------------------------------------------------------------------
    // Connect DMA Transfer SCOREBOARD to correct Monitors
    axi_system_env.master[0].monitor.item_observed_port.connect(m_dma_transfer_scbd.aimp_axi_master_trans_export);
    axi_system_env.slave[0].monitor.item_observed_port.connect(m_dma_transfer_scbd.aimp_axi_slave0_trans_export);
    axi_system_env.slave[1].monitor.item_observed_port.connect(m_dma_transfer_scbd.aimp_axi_slave1_trans_export);

    m_dma_irq_agent.monitor.ap.connect(m_dma_transfer_scbd.aimp_irq_info_export);
    // -------------------------------------------------------------------

  // DMA IRQ Agent Connections  TBD to SCOREBOARD and others
  // m_irq_agent.ap.connect(TO INSTANCE.ap port)


  endfunction : connect_phase

   // Reset the register model
   task reset_phase(uvm_phase phase);
     phase.raise_objection(this, "Resetting regmodel");
     // =======================================================================================================================
     // RAL Models reset
     // =======================================================================================================================
     dma_ip_regmodel.reset();
     if ( !($test$plusargs("no_ones_initialization")) ) begin
     // for (int row = 0; row < IMC_ROWS; row++) begin
     //   for(int column = 0; column < IMC_COLUMN; column++) begin
     //      ai_core_mvm_ref_model_h.mvm_mem_ifdw_0[row][column] = 8'hFF;
     //      ai_core_mvm_ref_model_h.mvm_mem_ifdw_1[row][column] = 8'hFF;
     //      ai_core_mvm_ref_model_h.mvm_mem_ifdw_2[row][column] = 8'hFF;
     //      ai_core_mvm_ref_model_h.mvm_mem_ifdw_3[row][column] = 8'hFF;
     //      ai_core_mvm_func_cov_h.mvm_mem_ifdw_0[row][column] = 8'hFF;
     //      ai_core_mvm_func_cov_h.mvm_mem_ifdw_1[row][column] = 8'hFF;
     //      ai_core_mvm_func_cov_h.mvm_mem_ifdw_2[row][column] = 8'hFF;
     //      ai_core_mvm_func_cov_h.mvm_mem_ifdw_3[row][column] = 8'hFF;
     //    end
     // end
     end
     phase.drop_objection(this);
   endtask

endclass : dma_ip_env

`endif  // DMA_IP_ENV_SV
