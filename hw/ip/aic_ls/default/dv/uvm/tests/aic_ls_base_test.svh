// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Base test. All tests
//              inherit from this class
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_DMC_BASE_TEST_SV
`define GUARD_AIC_DMC_BASE_TEST_SV
// AI CORE LS base test class
class aic_ls_base_test extends uvm_test;

  `uvm_component_utils(aic_ls_base_test)

  typedef bit[AIC_LS_ENV_AXI_CFG_ADDR_W-1:0] cfg_addr_t;
  typedef bit[AIC_LS_ENV_AXI_CFG_DATA_W-1:0] cfg_data_t;
  typedef bit[AIC_LS_ENV_AXI_CFG_DATA_W/8-1:0] cfg_wstrb_t;
  typedef bit[AIC_LS_ENV_AXI_HP_ADDR_W-1:0] hp_addr_t;
  typedef bit[AIC_LS_ENV_AXI_HP_DATA_W-1:0] hp_data_t;
  typedef bit[AIC_LS_ENV_AXI_HP_DATA_W/2-1:0] half_data_t;
  typedef bit[AIC_LS_ENV_AXI_STREAM_DATA_W-1:0] stream_data_t;

  aic_ls_env                  m_env;
  aic_ls_env_cfg              m_env_cfg;
  aic_ls_axi_system_cfg       m_axi_sys_cfg;
  aic_ls_demoter              m_catcher;
  aic_ls_ifd_seq_t            m_ifd_seq[];
  aic_ls_odr_seq_t            m_odr_seq[];
  aic_ls_l1_init_seq_t        m_l1_init_seq;
  int unsigned                    m_test_iteration = 1;
  int unsigned                    m_ifd_tlast_count[];
  int unsigned                    m_odr_tlast_count[];
  int unsigned                    m_ifd_mem_base_offsett[];
  int unsigned                    m_odr_mem_base_offsett[];
  int unsigned                    m_num_poll_cycles = 500;
  bit                             m_init_other_core_l1_mem = 0; // L1 of other cores
  string                          m_irq_path = "hdl_top.dut.o_dmc_irq";
  string                          m_icdf_setup = "icdf/setup.sh";
  bit                             m_lp_axi_override;
  bit                             m_init_l1_en=0;

  function new(string name = "aic_ls_base_test", uvm_component parent=null);
    int fd;
    super.new(name,parent);
    uvm_top.set_timeout(5ms,1);
    m_ifd_seq = new[AIC_LS_ENV_IFD_NUM_DEVICE];
    m_odr_seq = new[AIC_LS_ENV_ODR_NUM_DEVICE];
    m_ifd_tlast_count = new[AIC_LS_ENV_IFD_NUM_DEVICE];
    m_odr_tlast_count = new[AIC_LS_ENV_ODR_NUM_DEVICE];
    m_ifd_mem_base_offsett = new[AIC_LS_ENV_IFD_NUM_DEVICE];
    m_odr_mem_base_offsett = new[AIC_LS_ENV_ODR_NUM_DEVICE];
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(get_name(), "build_phase() started.",UVM_LOW)
    m_catcher = new();
    uvm_report_cb::add(null, m_catcher);
    if (m_lp_axi_override==0) set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());
    else set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_lp_axi_master_read_transaction::get_type());
    m_axi_sys_cfg = aic_ls_axi_system_cfg::type_id::create("m_axi_sys_cfg");
    uvm_config_db#(aic_ls_axi_system_cfg)::set(this, "m_env", "m_axi_sys_cfg", m_axi_sys_cfg);
    m_env_cfg = aic_ls_env_cfg::type_id::create("m_env_cfg");
    randomize_env_cfg();
    uvm_config_db#(aic_ls_env_cfg)::set(this, "m_env", "m_env_cfg", m_env_cfg);
    m_env = aic_ls_env::type_id::create("m_env", this);
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.m_axi_system_env.master[1].sequencer.main_phase", "default_sequence", axi_master_random_discrete_virtual_sequence::type_id::get());
    // Set the sequence length to generate 2 transactions
    uvm_config_db#(int unsigned)::set(this, "m_env.m_axi_system_env.master[1].sequencer.axi_master_random_discrete_virtual_sequence", "sequence_length", 2);
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_virt_sqr.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());

    /** Apply the Slave default response sequence to every Slave sequencer
     * Slaves will use the memory response sequence by default.  To override this behavior
     * extended tests can apply a different sequence to the Slave Sequencers.
     *
     * This sequence is configured for the run phase since the slave should always
     * respond to recognized requests.
     */
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info(get_name(), "build_phase() ended.",UVM_LOW)
  endfunction: build_phase

  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    `uvm_info(get_name(), "end_of_elaboration_phase() started.", UVM_LOW)
    uvm_top.print_topology();
    `uvm_info(get_name(), "end_of_elaboration_phase() ended.", UVM_LOW)
  endfunction: end_of_elaboration_phase

  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);
    // set cfg axi mst and slv agent in config db to be retrieved by non uvm components like report catcher and sequences
    uvm_config_db#(svt_axi_master_agent)::set(null,"*", "CFG_AXI_MST_AGENT", m_env.m_axi_system_env.master[0]);
    uvm_config_db#(aic_ls_env)::set(null,"*", "AIC_LS_ENV", m_env);
  endfunction: start_of_simulation_phase

  virtual task reset_phase(uvm_phase phase);
    super.reset_phase(phase);
    phase.raise_objection(this);
    `uvm_info(get_name(), "reset_phase() started.",UVM_LOW)
    @ (negedge m_env.m_axi_system_env.vif.interconnect_resetn);
    `uvm_info(get_name(), "reset_phase() encountered low reset!",UVM_LOW)
    @ (posedge m_env.m_axi_system_env.vif.interconnect_resetn);
    `uvm_info(get_name(), "reset_phase() ended.",UVM_LOW)
    phase.drop_objection(this);
  endtask: reset_phase

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    `uvm_info(get_name(), "configure_phase() started.",UVM_LOW)
    phase.raise_objection(this);
    init_l1();
    `uvm_info(get_name(), "configure_phase() ended.",UVM_LOW)
    phase.drop_objection(this);
  endtask

  virtual task post_reset_phase(uvm_phase phase);
    logic[7:0] cid_val;
    super.post_reset_phase(phase);
    phase.raise_objection(this);
    `uvm_info(get_name(), "post_reset_phase() started.",UVM_LOW)

    cid_val = m_env_cfg.m_cid;
    if (!uvm_hdl_force("hdl_top.i_cid", cid_val)) begin
      `uvm_fatal(get_name(), "Force failed for hdl_top.i_cid")
    end

    `uvm_info(get_name(), "post_reset_phase() ended.",UVM_LOW)
    phase.drop_objection(this);
  endtask: post_reset_phase

  virtual task post_configure_phase(uvm_phase phase);
    hp_data_t addr;
    hp_data_t wdata;
    hp_data_t rdata;
    int txt_len;
    super.post_configure_phase(phase);
    `uvm_info(get_name(), "post_configure_phase() started.",UVM_LOW)
    phase.raise_objection(this);
    if (m_init_other_core_l1_mem) begin
      txt_len = AIC_LS_ENV_L1_MEM_SIZE / (AIC_LS_ENV_AXI_HP_DATA_W/8);
      for (int cid=1; cid <= 4; cid++) begin
        if (cid == m_env_cfg.m_cid) continue; // do not program since it is own chip and won't go outside L1
        for (int a=0; a < txt_len; a++) begin
          addr = ((AIC_LS_ENV_CID_ADDR_OFFSET * cid) + AIC_LS_ENV_L1_MEM_OFFSET + AIC_LS_ENV_L1_ADDR_START) + (a * (AIC_LS_ENV_AXI_HP_DATA_W/8));
          for (int i=0; i < AIC_LS_ENV_AXI_HP_DATA_W; i++) begin
            wdata[i] = bit'($urandom_range(0,1));
          end
          m_env.m_axi_system_env.slave[0].axi_slave_mem.write(addr, wdata);
          rdata = m_env.m_axi_system_env.slave[0].axi_slave_mem.read(addr);
          if (a==0 || a== txt_len-1) begin
            `uvm_info(get_name(), $sformatf("Initializing HP Slave Mem: Addr: 0x%0x Data: 0x%0x", addr, wdata),UVM_LOW)
          end
        end
      end
    end
    `uvm_info(get_name(), "post_configure_phase() ended.",UVM_LOW)
    phase.drop_objection(this);
  endtask

  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    super.final_phase(phase);
    `uvm_info(get_name(), "final_phase() started.",UVM_LOW)
    svr = uvm_report_server::get_server();
    if (svr.get_severity_count(UVM_FATAL) + svr.get_severity_count(UVM_ERROR) + svr.get_severity_count(UVM_WARNING) > 0) begin
      `uvm_info(get_name(), "\nSvtTestEpilog: Failed\n", UVM_NONE)
    end else begin
      `uvm_info(get_name, "\nSvtTestEpilog: Passed\n", UVM_NONE)
    end
    `uvm_info(get_name(), "final_phase() ended.",UVM_LOW)
  endfunction: final_phase

  function void hdl_write(int index, l1_data_t data);
    /* performs the write of one value to the memory. it does that by reading the whole cell, replacing the relevant bits, and then writing back */
    int offset, m_bank, sram_index, sram_mux_l, sram_mux_r;
    string mem_location;
    l1_phys_data_t data_phys;
    l1_half_data_t data_l, data_r;
    l1_quarter_data_t partial_data;

    m_bank = index%DEFAULT_L1_NUM_BANKS;
    offset = index/DEFAULT_L1_NUM_BANKS;
    sram_index = offset/AIC_LS_ENV_L1_SRAM_MUX;
    sram_mux_r = offset%AIC_LS_ENV_L1_SRAM_MUX;
    sram_mux_l = (AIC_LS_ENV_L1_SRAM_MUX-1)-sram_mux_r;

    for (int s_bank=0; s_bank<L1_SUB_BANKS_PER_BANK; s_bank++) begin
      partial_data = data[s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE +: AIC_LS_ENV_L1_SRAM_WORD_SIZE];  // only work with the relevant 128 bits of data

    `ifndef TARGET_DFT
      mem_location = $sformatf("%s.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.mem[%0d]", m_env_cfg.m_l1_mem_root_path, s_bank, m_bank, sram_index);
    `else
      mem_location = $sformatf("%s.\\g_sbank[%0d].u_sub_bank .\\g_mini_bank[%0d].u_mini_bank .\\g_macro[0].u_macro .u_macro .\\gen_inst.i_sramspehd.u_mem.mem[%0d]", m_env_cfg.m_l1_mem_root_path, s_bank, m_bank, sram_index);
    `endif

      if (!uvm_hdl_read(mem_location, data_phys)) begin
        `uvm_fatal(get_name(), $sformatf("Failed to read HDL path! %s", mem_location))
      end
      
      data_r = data_phys[AIC_LS_ENV_L1_SRAM_FULL_SIZE-1:(AIC_HT_AXI_DATA_WIDTH/2)+(AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS*2)];	// WO redundancy bits - 256+8...512+8
      data_l = data_phys[AIC_HT_AXI_DATA_WIDTH/2-1:0];
      
      for(int j=0; j<AIC_LS_ENV_L1_SRAM_WORD_SIZE/2; j++) begin	 // we ran from 0 to 63, filling both the lower and upper half in parallel. this is following the SRAM definitions
        data_l[(j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_l] = partial_data[j];
        data_r[(j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_r] = partial_data[j+(AIC_LS_ENV_L1_SRAM_WORD_SIZE/2)];
      end

      data_phys[L1_BANK_DATA_WIDTH/2-1:0] = data_l;  // left side - bits 0:255 + 256:259 redun
      data_phys[L1_BANK_DATA_WIDTH/2+(AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS*2) +: L1_BANK_DATA_WIDTH/2] = data_r; // have to take redundancy into account as well - right side - bits 260:263 redun + 264:519 

      if (!uvm_hdl_deposit(mem_location, data_phys)) begin
        `uvm_fatal(get_name(), $sformatf("Failed to deposit HDL path! %s", mem_location))
      end
    end
  endfunction: hdl_write

  function l1_data_t hdl_read(int index);
    /* performs the write of one value to the memory. it does that by reading the whole cell, replacing the relevant bits, and then writing back */
    int offset, m_bank, sram_index, sram_mux_l, sram_mux_r;
    string mem_location;
    l1_phys_data_t data_phys;
    l1_half_data_t data_l, data_r;
    l1_data_t backdoor_data;

    m_bank = index%DEFAULT_L1_NUM_BANKS;
    offset = index/DEFAULT_L1_NUM_BANKS;
    sram_index = offset/AIC_LS_ENV_L1_SRAM_MUX;
    sram_mux_r = offset%AIC_LS_ENV_L1_SRAM_MUX;
    sram_mux_l = (AIC_LS_ENV_L1_SRAM_MUX-1)-sram_mux_r;

    for (int s_bank=0; s_bank<L1_SUB_BANKS_PER_BANK; s_bank++) begin
    `ifndef TARGET_DFT
      mem_location = $sformatf("%s.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.mem[%0d]", m_env_cfg.m_l1_mem_root_path, s_bank, m_bank, sram_index);
    `else
      mem_location = $sformatf("%s.\\g_sbank[%0d].u_sub_bank .\\g_mini_bank[%0d].u_mini_bank .\\g_macro[0].u_macro .u_macro .\\gen_inst.i_sramspehd.u_mem.mem[%0d]", m_env_cfg.m_l1_mem_root_path, s_bank, m_bank, sram_index);
    `endif

      if (!uvm_hdl_read(mem_location, data_phys)) begin
        `uvm_fatal(get_name(), $sformatf("Failed to read HDL path! %s", mem_location))
      end
      
      data_r = data_phys[AIC_LS_ENV_L1_SRAM_FULL_SIZE-1:(AIC_HT_AXI_DATA_WIDTH/2)+(AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS*2)];	// WO redundancy bits - 256+8...512+8
      data_l = data_phys[AIC_HT_AXI_DATA_WIDTH/2-1:0];

      for(int j=0; j<AIC_LS_ENV_L1_SRAM_WORD_SIZE/2; j++) begin	 // we ran from 0 to 63, filling both the lower and upper half in parallel. this is following the SRAM definitions
        backdoor_data[j+(s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE)] = data_l[(j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_l];
        backdoor_data[j+AIC_LS_ENV_L1_SRAM_WORD_SIZE/2+(s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE)] = data_r[(j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_r];
        `uvm_info(get_name(), $sformatf("More debug: backdoor_data[%0d] = temp_data_l[%0d]", j+(s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE), (j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_l), UVM_HIGH)
        `uvm_info(get_name(), $sformatf("More debug: backdoor_data[%0d] = temp_data_r[%0d]", j+AIC_LS_ENV_L1_SRAM_WORD_SIZE/2+(s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE), (j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_r), UVM_HIGH)
      end
      `uvm_info(get_name(), $sformatf("More debug: backdoor_data for this iteration: 0x%x", backdoor_data[s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE +: AIC_LS_ENV_L1_SRAM_WORD_SIZE]), UVM_MEDIUM)
    end
    return backdoor_data;
  endfunction: hdl_read

  virtual function void randomize_env_cfg();
    if (!(m_env_cfg.randomize())) begin
      `uvm_fatal(get_name(), "Randomization failed for m_env_cfg!")
    end
  endfunction

  function int remap_index(int indx);
    int reg_indx;
    string device_name;
    int res_array[$];
    // function remaps the indexes used in the sequences which uses ifd-odr order into mvm-dwpu order
    // {"mvm_ifd0", "mvm_ifd1", "mvm_ifdw", "dwpu_ifd0", "dwpu_ifd1", "mvm_odr", "dwpu_odr", "token_mgr"};
    // {"m_ifd0", "m_ifd1", "m_ifdw", "m_odr", "d_ifd0", "d_ifd1", "d_odr", "mvm_exe", "mvm_prg", "dwpu", "d_dpu", "d_iau", "m_dpu", "m_iau"};

    // Get the value from logical_order based on the index
    device_name = AIC_LS_DMC_DEVICE_NAME[indx];

    // Use find_index to find the index in physical_order where the value matches
    res_array = AIC_LS_DMC_DEVICE_NAME_DUT.find_index with (item == device_name);
    reg_indx = res_array[0];
    `uvm_info(get_name(), $sformatf("Remapping indexes: device_name: %s, tb index: %0d, dut index: %0d", AIC_LS_DMC_DEVICE_NAME[indx], indx, reg_indx), UVM_LOW)
    return reg_indx;
  endfunction

  // for function coverage
  virtual task trigger_reg_evt(int device_index, string reg_name);
    cfg_data_t rd_data;
    uvm_event reg_evt = uvm_event_pool::get_global($sformatf("%s_reg_evt", AIC_LS_DMC_DEVICE_NAME[device_index]));
    v_object v_obj= v_object::type_id::create("v_obj");
    m_env.m_ral.bkdr_read_reg(.regblock_num(device_index),  .data(rd_data), .name(reg_name));
    v_obj.m_64bit_data = rd_data;
    v_obj.m_string = reg_name;
    reg_evt.trigger(v_obj);
    `uvm_info(get_name(), $sformatf("Triggering %s_reg_evt", AIC_LS_DMC_DEVICE_NAME[device_index]), UVM_HIGH)
  endtask

  // Common Tasks/ Functions
  virtual task enable_cmdblk(int index=-1);
    int start_index = (index==-1)? 0: index;
    int end_index   = (index==-1)? AIC_LS_ENV_DMC_NUM_DEVICE: index+1;
    aic_ls_device_index_t  device_index;
    cfg_data_t wdata = 1; // enable value: bit 0: EXEC_EN
    for (int i = start_index; i < end_index; i ++) begin
      device_index = aic_ls_device_index_t'(i);
      m_env.m_ral.write_reg(.regblock_num(device_index),  .data(wdata), .name("cmdblk_ctrl"));
      `uvm_info(get_name(), $sformatf("enable_cmdblk() done for %s", device_index.name()), UVM_LOW)
    end
    repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk);
  endtask

  virtual task run_token_producer(string src, string dst, int count=1);
    token_agent_prod_sequence tok_prod_seq;
    string prod_mst = $sformatf("tkn_%s_to_%s", src, dst);
    for (int i=0; i < count; i++) begin
      tok_prod_seq = token_agent_prod_sequence::type_id::create("tok_prod_seq");
      `uvm_info (get_name(), $sformatf("starting token prod sequence with %s started.", prod_mst), UVM_LOW)
      tok_prod_seq.start(m_env.m_token_agents[prod_mst].m_tok_seqr);
    end
  endtask

  virtual task run_token_consumer(string src, string dst, int count=1, bit delay_en=0);
    token_agent_cons_sequence tok_cons_seq;
    string cons_mst = $sformatf("tkn_%s_to_%s", src, dst);
    for (int i=0; i < count; i++) begin
      tok_cons_seq = token_agent_cons_sequence::type_id::create("m_tok_cons_seq");
      `uvm_info (get_name(), $sformatf("starting token cons sequence with %s started.", cons_mst), UVM_LOW)
      tok_cons_seq.start(m_env.m_token_agents[cons_mst].m_tok_seqr);
      if (delay_en==1) begin
        #30ns; // put high delay so producer count saturates
      end
    end
  endtask

  virtual task check_expected_irq(logic exp_irq, int indx);
    logic [7:0] irq_out;
    if (uvm_hdl_read(m_irq_path, irq_out)) begin
      if (irq_out[indx] !== exp_irq) begin
        `uvm_error(get_name(), $sformatf("Invalid IRQ Value! Exp: 0x%0x Act: 0x%0x", exp_irq, irq_out))
      end
    end else begin
      `uvm_fatal(get_name(), $sformatf("Unable to read: %s", m_irq_path))
    end
    `uvm_info(get_name(), "check_expected_irq() done.", UVM_LOW)
  endtask

  virtual task reset_ls();
    `uvm_info(get_name(), "Reset start", UVM_LOW)
    if (!uvm_hdl_force("hdl_top.axi_reset_if.reset", 1'b0)) begin
      `uvm_fatal(get_name(), "Force failed for hdl_top.axi_reset_if.reset")
    end

    foreach (m_env.m_dmc_addr_scb[i]) begin
      -> m_env.m_dmc_addr_scb[i].m_rst_evt;
    end
    foreach (m_env.m_dmc_data_scb[i]) begin
      -> m_env.m_dmc_data_scb[i].m_rst_evt;
    end
    foreach (m_env.m_dmc_ref_mdl[i]) begin
      -> m_env.m_dmc_ref_mdl[i].m_rst_evt;
    end

    repeat(50) @(posedge m_env.m_axi_system_env.vif.common_aclk);
    if (!uvm_hdl_force("hdl_top.axi_reset_if.reset", 1'b1)) begin
      `uvm_fatal(get_name(), "Force failed for hdl_top.axi_reset_if.reset")
    end

    foreach (m_env.m_dmc_addr_scb[i]) begin
      -> m_env.m_dmc_addr_scb[i].m_rst_done_evt;
    end
    foreach (m_env.m_dmc_data_scb[i]) begin
      -> m_env.m_dmc_data_scb[i].m_rst_done_evt;
    end
    foreach (m_env.m_dmc_ref_mdl[i]) begin
      -> m_env.m_dmc_ref_mdl[i].m_rst_done_evt;
    end
    m_env.m_ls_regmodel.reset();
    aic_ls_ifd_seq_t::m_init_l1_done = 0;
    `uvm_info(get_name(), "Reset end", UVM_LOW)
  endtask

  virtual task read_register(int device_index, string name, string field="", bit poll=0, cfg_data_t poll_val=0);
    cfg_data_t rdata;
    aic_ls_device_index_t device = aic_ls_device_index_t'(device_index);
    fork
      forever begin
        m_env.m_ral.read_reg(.regblock_num(device_index),  .data(rdata), .name(name), .field(field));
        trigger_reg_evt(device_index, name);
        if (rdata==poll_val || poll==0) begin
          `uvm_info(get_name(), $sformatf("read_register(.name(%s), .field(%s), .poll(%0d), poll_val(0x%0x)) ended for %s with rdata 0x%0x", name, field, poll, poll_val,  device.name(), rdata), UVM_HIGH)
          break;
        end
        if (poll==1) begin
          repeat(m_num_poll_cycles) @(posedge m_env.m_axi_system_env.vif.common_aclk); // do not poll too frequently as it avoids parallel txn to succeed
        end
      end
      begin
        #1ms;
        `uvm_fatal(get_name(), $sformatf("Polling Timeout! Waiting for %s %s %s to be 0x%0x did not happen!", device.name(), name, field, poll_val))
      end
    join_any
    disable fork;
  endtask

  virtual task gen_axi_stream(int odr_indx);
    int unsigned txn_len;
    m_env.m_dmc_ref_mdl[odr_indx + AIC_LS_ENV_IFD_NUM_DEVICE].wait_address_gen_output(txn_len);
    `uvm_info(get_name(), $sformatf("Got stream length for %s! Length=%0d", AIC_LS_DMC_DEVICE_NAME[odr_indx + AIC_LS_ENV_IFD_NUM_DEVICE], txn_len), UVM_LOW)
    fork send_axi_stream(txn_len, odr_indx); join_none
    //#10ns;
    //m_env.reset_addr_gen_refmodel();
  endtask

  virtual task send_axi_stream(int txn_len, int odr_indx);
    axi_master_stream_base_sequence odr_short_stream_seq, odr_stream_seq_q[$];
    stream_data_t sdata;
    stream_data_t stream_data_q[$];
    stream_data_q.delete();

    for (int i = 0; i < txn_len; i++) begin
      for (int d=0; d < AIC_LS_ENV_AXI_STREAM_DATA_W; d++) begin
        sdata[d] = bit'($urandom_range(0,1));
      end
      stream_data_q.push_back(sdata); // store all data
      if (i%txn_len==0) begin
        odr_short_stream_seq = axi_master_stream_base_sequence::type_id::create("odr_short_stream_seq");
        if (!(odr_short_stream_seq.randomize() with {
            sequence_length == 'd1;
        })) begin
          `uvm_fatal(get_name(), "Randomization failed for odr_short_stream_seq!")
        end
        odr_short_stream_seq.data.delete();
        odr_short_stream_seq.burst_length = txn_len;
      end
      odr_short_stream_seq.data.push_back(sdata);
      if (i%txn_len==txn_len-1) begin
        odr_stream_seq_q.push_back(odr_short_stream_seq); // stor for starting later
      end
    end
    foreach (odr_stream_seq_q[i]) begin
      odr_stream_seq_q[i].start(m_env.m_axi_system_env.master[odr_indx + 2].sequencer);
        `uvm_info(get_name(), $sformatf("AXI Stream[%0d of %0d] Sent for %s from AXI Stream MST%0d", i, odr_stream_seq_q.size()-1, AIC_LS_DMC_DEVICE_NAME[odr_indx + AIC_LS_ENV_IFD_NUM_DEVICE], odr_indx+2), UVM_LOW)
    end
  endtask

  virtual task cfg_axi_write(cfg_addr_t addr, cfg_data_t data, cfg_wstrb_t wstrb=8'hFF);
    aic_ls_axi_cfg_if_write_sequence cfg_write;
    cfg_write = aic_ls_axi_cfg_if_write_sequence::type_id::create("cfg_write");
    if (!(cfg_write.randomize() with {
        cfg_addr        == addr;
        cfg_wstrb       == wstrb;
        use_random_strb == 1;
        burst_length    == 1;
        sequence_length == 1;
    })) begin
      `uvm_fatal(get_name(), "Randomization failed for cfg_write!")
    end
    cfg_write.cfg_data_q.push_back(data);
    cfg_write.start(m_env.m_axi_system_env.master[0].sequencer);
  endtask

  virtual task cfg_axi_read(cfg_addr_t addr, output cfg_data_t data);
    aic_ls_axi_cfg_if_read_sequence cfg_read;
    cfg_read = aic_ls_axi_cfg_if_read_sequence::type_id::create("cfg_read");
    if (!(cfg_read.randomize() with {
        cfg_addr        == addr;
        sequence_length == 1;
    })) begin
      `uvm_fatal(get_name(), "Randomization failed for cfg_write!")
    end
    cfg_read.start(m_env.m_axi_system_env.master[0].sequencer);
    foreach(cfg_read.read_tran.data[i]) begin
      data = cfg_read.read_tran.data[i];
    end
  endtask

  virtual task init_l1(bit debug_data=0);
    if (m_init_l1_en) begin
      aic_ls_l1_init_seq_t m_l1_init_seq;
      m_l1_init_seq = aic_ls_l1_init_seq_t::type_id::create("m_l1_init_seq");
      m_l1_init_seq.m_l1_debug_data = debug_data;
      m_l1_init_seq.start(null);
      `uvm_info(get_name(), "init_l1() done!", UVM_LOW)
    end
  endtask

  virtual task update_tlast(int tlast_index, bit is_ifd_not_odr);
    // very simple function that updates the appropriate m_ifd_tlast_count's value, for cases where we first wait for the previous sequence to end before we launch the next one
    if (is_ifd_not_odr) m_ifd_tlast_count[tlast_index] = m_ifd_seq[tlast_index].m_tlast_count;
    else m_odr_tlast_count[tlast_index] = m_odr_seq[tlast_index].m_tlast_count;
  endtask
endclass:aic_ls_base_test

`endif // GUARD_AIC_DMC_BASE_TEST_SV
