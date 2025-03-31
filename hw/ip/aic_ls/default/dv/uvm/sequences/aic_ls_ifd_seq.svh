// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD Sequence
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
class aic_ls_ifd_seq#(type T = aic_ls_env) extends uvm_sequence;
  `uvm_object_param_utils(aic_ls_ifd_seq#(T))

  typedef bit[AIC_LS_ENV_AXI_CFG_ADDR_W-1:0] cfg_addr_t;
  typedef bit[AIC_LS_ENV_AXI_HP_ADDR_W-1:0] hp_addr_t;
  typedef bit[AIC_LS_ENV_AXI_CFG_DATA_W-1:0] cfg_data_t;
  typedef bit[AIC_LS_ENV_AXI_HP_DATA_W-1:0] hp_data_t;
  typedef bit[L1_BANK_DATA_WIDTH-1:0] l1_data_t;
  typedef bit[L1_BANK_DATA_WIDTH/2-1:0] l1_half_data_t;
  typedef bit[L1_BANK_DATA_WIDTH/4-1:0] l1_quarter_data_t;
  typedef bit[AIC_LS_ENV_L1_SRAM_FULL_SIZE-1:0] l1_phys_data_t;
  typedef bit[AIC_LS_ENV_L1_SRAM_WORD_SIZE-1:0] l1_phys_word_t;
  typedef bit[AIC_LS_ENV_AXI_STREAM_DATA_W-1:0] stream_data_t;
  typedef bit[AIC_LS_ENV_AXI_STREAM_DATA_W/2-1:0] half_stream_data_t;

  string                          m_env_name = "AIC_LS_ENV";
`ifdef AI_CORE_TOP_ENV_CHECK
  string                          m_l1_mem_root_path   = DATA_SB_TOP_L1_MEM_ROOT_PATH;
  protected int unsigned          m_cmdblk_fifo_offset = AI_CORE0_TOP_ENV_CMDBLK_FIFO_OFFSET;
`else
  string                          m_l1_mem_root_path   = DATA_SB_L1_MEM_ROOT_PATH;
  protected int unsigned          m_cmdblk_fifo_offset = AIC_LS_ENV_CMDBLK_FIFO_OFFSET;
`endif
  rand aic_ls_device_t            m_device;
  rand int unsigned               m_cid;
  rand int unsigned               m_tlast_count;
  rand bit                        m_wait_for_status;
  rand bit                        m_wait_data_done_en;

  // AG Related
  rand addr_gen_cmdformat_t       m_ag_cmd_format;
  rand bit[15:0]                  header_tkn_consumer;
  rand bit[15:0]                  header_tkn_producer;
  rand hp_addr_t                  m_ag_mem_baseaddr;
  rand bit[15:0]                  m_ag_length;
  rand int unsigned               m_desc_mem_offset;
  rand int                        m_ag_dim_def_ptr;
  rand int                        m_ag_loop_def_ptr;
  rand int                        m_ag_num_dim;
  rand int                        m_ag_vect_dim;
  rand int unsigned               m_ag_ringbuffsize;
  rand int                        m_ag_mask_start;
  rand int                        m_ag_mask_end;
  rand bit[1:0]                   m_ag_vtrsp_mode;
  rand bit                        m_ag_decompression_en;
  rand int unsigned               m_ag_mem_bsize;
  rand int                        m_ag_header_vector_mode;
  rand int                        m_ag_format;

  rand bit                        m_use_token_mechanism;
  rand int unsigned               m_stream_len;

  int unsigned                    m_prev_tlast_count; // not rand to simplify randomization in loops
  int unsigned                    m_hp_mst_index = 1;
  int unsigned                    m_cfg_mst_index = 0;
  int unsigned                    iteration;
  bit                             m_enable_cmdb = 1;
  bit                             m_enable_wr_to_l1 = 1;
  bit                             m_backdoor_polling = 0;
  bit                             m_token_override = 0; // set to 1 for sweeping token header tests
  bit                             m_cfg_b2b_en;
  ifdw_decompression_seq_item     m_decomp_item_h;
  bit                             m_l1_debug_data=0;
  bit                             m_use_mem_bsize = 0;
  bit                             m_rand_addr_item = 1;
  bit                             m_program_defmem = 1;

  // Error Handling
  string                          m_irq_status_field = "";
  dmc_addr_gen_seq_item       m_addr_item;

  protected rand aic_ls_device_index_t  m_device_index;
  protected T                               m_ral_env_h;
  protected aic_ls_env                  m_ls_env_h;
  protected aic_ls_env_cfg              m_env_cfg_h;
  protected int                             m_memory_range;
  static bit                                m_init_l1_done=0;

  constraint C_CID {
    soft m_cid == 1;
  }

  constraint C_DEVICE {
    soft m_device inside {MIFD0, MIFD1, MIFD2, MIFDW, DIFD0, DIFD1};
  }

  constraint C_DEVICE_INDEX {
    (m_device==MIFD0) -> soft m_device_index==MVM_IFD0;
    (m_device==MIFD1) -> soft m_device_index==MVM_IFD1;
    (m_device==MIFD2) -> soft m_device_index==MVM_IFD2;
    (m_device==MIFDW) -> soft m_device_index==MVM_IFDW;
    (m_device==DIFD0) -> soft m_device_index==DWPU_IFD0;
    (m_device==DIFD1) -> soft m_device_index==DWPU_IFD1;
  }

  constraint C_DEVICE_ADDR_ALLOC {
    (m_device==MIFD0) -> soft m_ag_mem_baseaddr=='h800_0000 + m_cid * (1 << 28);
    (m_device==MIFD1) -> soft m_ag_mem_baseaddr=='h808_0000 + m_cid * (1 << 28);
    (m_device==MIFD2) -> soft m_ag_mem_baseaddr=='h810_0000 + m_cid * (1 << 28);
    (m_device==MIFDW) -> soft m_ag_mem_baseaddr=='h818_0000 + m_cid * (1 << 28);
    (m_device==DIFD0) -> soft m_ag_mem_baseaddr=='h820_0000 + m_cid * (1 << 28);
    (m_device==DIFD1) -> soft m_ag_mem_baseaddr=='h828_0000 + m_cid * (1 << 28);
  }

  constraint C_MEM_BSIZE_DEFAULT {
    soft m_ag_mem_bsize == 'h40_0000; // default large value if used
  }
  
  constraint C_TOKEN_MECHANISM {
    soft m_use_token_mechanism == 0;
  }

 `ifndef AI_CORE_TOP_ENV_CHECK
  constraint C_TOKEN_PROD_CONS {
    (m_use_token_mechanism==0) -> soft header_tkn_consumer == 0;
    (m_use_token_mechanism==0) -> soft header_tkn_producer == 0;
  }
 `endif

  constraint C_TLAST_COUNT {
    soft m_tlast_count == 1;
  }

  constraint C_LINEAR_LENGTH {
    soft m_ag_length % aic_common_pkg::AIC_PWORD_SIZE == 0; // align to PWORD
    soft m_ag_length > 0;
    soft m_ag_length <= 4 * 1024;
  }

  constraint C_ADDR_GEN_PTR_DEFAULT {
    soft m_ag_dim_def_ptr == -1;
    soft m_ag_loop_def_ptr == -1;
  }

  constraint C_ADDR_GEN_NUM_DIM_DEFAULT {
    soft m_ag_num_dim == -1;
  }

  constraint C_DESC_MEM_ADDRESS_DEFAULT {
    soft m_desc_mem_offset == AIC_LS_ENV_DESCMEM_OFFSET;
  }

  constraint C_RINGBUFFSIZE_DEFAULT {
    soft m_ag_ringbuffsize == -1;
  }

  constraint C_MASK_DEFAULT {
    soft m_ag_mask_start == -1; // negative means allow the item's default constraint
    soft m_ag_mask_end == -1; // negative means allow the item's default constraint
  }

  constraint C_VECT_DIM_DEFAULT {
    soft m_ag_vect_dim == -1; // negative means allow the item's default constraint
  }

  constraint C_DECOMPRESSION_DEFAULT {
    soft m_ag_decompression_en == 0;
  }

  constraint C_VTRSP_DEFAULT {
    soft m_ag_vtrsp_mode == 0;
  }

  constraint C_INT_FORMAT_DEFAULT {  // default is generate randomly
    soft m_ag_header_vector_mode == -1;
    soft m_ag_format == -1;
  }

  constraint C_SOLVER {
    solve m_device before m_device_index, m_ag_mem_baseaddr;
    solve m_stream_len before m_tlast_count;
    solve m_use_token_mechanism before header_tkn_consumer, header_tkn_producer;
    solve m_cid before m_ag_mem_baseaddr;
  }
  constraint C_WAIT_FOR_IDLE_EN_SANITY {
    soft m_wait_for_status == 1;
  }
  constraint C_WAIT_DATA_DONE_EN_SANITY {
    soft m_wait_data_done_en == 1;
  }

  function new(string name = "aic_ls_ifd_seq");
    super.new(name);
  endfunction

  function void post_randomize();
    super.post_randomize();
    m_tlast_count += m_prev_tlast_count; // support for multiple creation and iteration of the sequence
    `uvm_info(get_name(), convert2string(), UVM_HIGH)
  endfunction

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n----------- %s IFD/ODR Sequence ----------------", m_env_name) };
    s = {s, $sformatf("\n Name                        : %s", get_name()) };
    s = {s, $sformatf("\n iteration                   : %0d", iteration) };
    s = {s, $sformatf("\n m_cid                       : 0x%0x", m_cid) };
    s = {s, $sformatf("\n m_device                    : %s", m_device.name()) };
    s = {s, $sformatf("\n m_tlast_count               : 0x%0x", m_tlast_count) };
    s = {s, $sformatf("\n m_prev_tlast_count          : 0x%0x", m_prev_tlast_count) };
    s = {s, $sformatf("\n m_use_token_mechanism       : 0x%0x", m_use_token_mechanism) };
    s = {s, $sformatf("\n m_ag_cmd_format             : %s", m_ag_cmd_format.name()) };
    s = {s, $sformatf("\n m_ag_dim_def_ptr            : %0d", m_ag_dim_def_ptr) };
    s = {s, $sformatf("\n m_ag_loop_def_ptr           : %0d", m_ag_loop_def_ptr) };
    s = {s, $sformatf("\n m_ag_mask_start             : %0d", m_ag_mask_start) };
    s = {s, $sformatf("\n m_ag_mask_end               : %0d", m_ag_mask_end) };
    s = {s, $sformatf("\n m_ag_ringbuffsize           : %0d", m_ag_ringbuffsize) };
    s = {s, $sformatf("\n m_ag_length                 : %0d", m_ag_length) };
    s = {s, $sformatf("\n m_ag_num_dim                : %0d", m_ag_num_dim) };
    s = {s, $sformatf("\n m_ag_decompression_en       : %0d", m_ag_decompression_en) };
    s = {s, $sformatf("\n m_ag_vtrsp_mode             : %0d", m_ag_vtrsp_mode) };
    s = {s, $sformatf("\n m_ag_header_vector_mode     : %0d", m_ag_header_vector_mode) };
    s = {s, $sformatf("\n m_ag_format                 : %0d", m_ag_format) };
    s = {s, $sformatf("\n header_tkn_producer         : 0x%0x", header_tkn_producer) };
    s = {s, $sformatf("\n header_tkn_consumer         : 0x%0x", header_tkn_consumer) };
    s = {s, $sformatf("\n m_stream_len                : 0x%0x", m_stream_len) };
    s = {s, $sformatf("\n m_ag_mem_baseaddr           : 0x%0x", m_ag_mem_baseaddr) };
    s = {s, $sformatf("\n m_device_index              : 0x%0x", m_device_index) };
    s = {s, $sformatf("\n m_l1_mem_root_path          : %s", m_l1_mem_root_path) };
    s = {s, $sformatf("\n m_irq_status_field          : %s", m_irq_status_field) };
    s = {s, $sformatf("\n m_wait_for_status           : %0d", m_wait_for_status) };
    s = {s, $sformatf("\n m_wait_data_done_en           : %0d", m_wait_data_done_en) };
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;
  endfunction : convert2string

  virtual function void stream_compare(stream_data_t exp, stream_data_t act, int indx);
    if (act != exp) begin
      `uvm_error(get_name(), $sformatf("Data[%0d] Mismatch! Exp: 0x%0x Act: 0x%0x", indx, exp, act))
    end else begin
      `uvm_info(get_name(), $sformatf("Data[%0d] Match! Exp: 0x%0x Act: 0x%0x", indx, exp, act), UVM_LOW)
    end
  endfunction

  virtual function bit is_outside_l1(hp_addr_t addr);
    // DEBUG
    // `uvm_info(get_name(), $sformatf("is_outside_l1() started! addr: 0x%0x , m_l1_full_start_addr = 0x%0x ,m_l1_full_end_addr =0x%0x", addr, m_env_cfg_h.m_l1_full_start_addr, m_env_cfg_h.m_l1_full_end_addr), UVM_LOW)
    return (addr < m_env_cfg_h.m_l1_full_start_addr || addr > m_env_cfg_h.m_l1_full_end_addr);
  endfunction

  virtual function void randomize_item();
    if (m_rand_addr_item) begin
      m_addr_item = dmc_addr_gen_seq_item::type_id::create("m_addr_item");
      m_addr_item.iteration = iteration;
      if (!(m_addr_item.randomize() with {
        header_token_producer == header_tkn_producer;
        header_token_consumer == header_tkn_consumer;
        m_cmd_format     == m_ag_cmd_format;
        m_length         == m_ag_length;
        m_mem_baseaddr   == m_ag_mem_baseaddr;
        m_vtrsp_mode     == m_ag_vtrsp_mode;
        m_decomp_en      == m_ag_decompression_en;
        if (m_use_mem_bsize ==  1) m_mem_bsize == m_ag_mem_bsize;
        if (m_ag_ringbuffsize != -1) m_ring_buff_size == m_ag_ringbuffsize;
        if (m_ag_dim_def_ptr != -1) m_dim_def_ptr == m_ag_dim_def_ptr;
        if (m_ag_loop_def_ptr != -1) m_loop_def_ptr == m_ag_loop_def_ptr;
        if (m_ag_mask_start != -1) m_mask_start == m_ag_mask_start;
        if (m_ag_mask_end != -1) m_mask_end == m_ag_mask_end;
        if (m_ag_num_dim != -1 && (m_ag_cmd_format inside {CMDFORMAT_DEF_BASED, CMDFORMAT_OFFSET_BASED})) m_num_dim == m_ag_num_dim;
        if (m_ag_vect_dim != -1) m_vect_dim == m_ag_vect_dim;
        if (m_ag_header_vector_mode != -1) header_vector_mode == m_ag_header_vector_mode;
        if (m_ag_format != -1) m_format == m_ag_format;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_addr_item!")
      end
    end else begin
      if (m_addr_item==null) begin
        `uvm_fatal(get_name(), "m_addr_item is null!")
      end
    end
    `uvm_info(get_name(), $sformatf("m_addr_item randomized with: %s", m_addr_item.convert2string()), UVM_LOW)
    m_memory_range = m_addr_item.m_mem_bsize;
  endfunction

  virtual function void set_header();
    bit temp_value;
    if (m_use_token_mechanism) begin
      `uvm_info(get_name(), $sformatf("Generating header for command!"), UVM_LOW)
      for (int i=0; i<AIC_LS_ENV_TOKEN_VECTOR_TOTAL_CONN_NUM+1; i++) begin // we add one additional bit for ACD. it's not part of the tok vector, but it is part of the header.
        temp_value = bit'($urandom_range(0,1));  // producer gets the random value, consumer gets the other. this way they are never the same
        header_tkn_producer[i] = temp_value;
        header_tkn_consumer[i] = 1-temp_value;
      end
      for (int i=AIC_LS_ENV_TOKEN_VECTOR_TOTAL_CONN_NUM+1; i<AIC_LS_ENV_TOKEN_VECTOR_LENGTH+1; i++) begin
        header_tkn_producer[i] = bit'($urandom_range(0,1));  // reserved bits, their values shouldn't matter at all.
        header_tkn_consumer[i] = bit'($urandom_range(0,1));
      end
    end
    `uvm_info(get_name(), $sformatf("Setting %s producer to 0b%10b and consumer to 0b%10b", m_device.name.tolower(), header_tkn_producer, header_tkn_consumer), UVM_LOW)
  endfunction

  // for function coverage
  virtual task trigger_reg_evt(string reg_name);
    cfg_data_t rd_data;
    uvm_event reg_evt = uvm_event_pool::get_global($sformatf("%s_reg_evt", AIC_LS_DMC_DEVICE_NAME[m_device_index]));
    v_object v_obj= v_object::type_id::create("v_obj");
    m_ral_env_h.m_ral.bkdr_read_reg(.regblock_num(m_device_index),  .data(rd_data), .name(reg_name));
    v_obj.m_64bit_data = rd_data;
    v_obj.m_string = reg_name;
    reg_evt.trigger(v_obj);
    `uvm_info(get_name(), $sformatf("Triggering %s_reg_evt for register: %s", AIC_LS_DMC_DEVICE_NAME[m_device_index], reg_name), UVM_HIGH)
  endtask

  virtual task pre_body();
    if (!uvm_config_db #(T)::get(null, "", m_env_name, m_ral_env_h)) begin
        `uvm_fatal(get_name(), $sformatf("Unable to get RAL %s", m_env_name))
    end
    if (!uvm_config_db #(aic_ls_env)::get(null, "", "AIC_LS_ENV", m_ls_env_h)) begin
        `uvm_fatal(get_name(), "Unable to get ENV AIC_LS_ENV")
    end
    m_env_cfg_h = m_ls_env_h.m_env_cfg;
  endtask : pre_body

  virtual task cfg_axi_write(cfg_addr_t addr, cfg_data_t data_q[$]);
    aic_ls_axi_cfg_if_write_sequence cfg_write;
    int data_size = data_q.size();
    cfg_write = aic_ls_axi_cfg_if_write_sequence::type_id::create("cfg_write");
    foreach (data_q[i]) begin
      cfg_write.cfg_data_q.push_back(data_q[i]);
    end
    if (!(cfg_write.randomize() with {
        cfg_addr        == addr;
        burst_length    == data_size;
        sequence_length == 1;
    })) begin
      `uvm_fatal(get_name(), "Randomization failed for cfg_write!")
    end
    cfg_write.b2b_en = m_cfg_b2b_en;
    cfg_write.start(m_ral_env_h.m_axi_system_env.master[m_cfg_mst_index].sequencer);
  endtask

  virtual task print_debug_data(input l1_data_t data, input int m_bank, input int s_bank, output l1_data_t result[AIC_LS_ENV_L1_NUM_BANKS*AIC_LS_ENV_L1_SRAM_MUX]);
    l1_half_data_t data_l;
    l1_half_data_t data_r;
    l1_phys_word_t data_words[AIC_LS_ENV_L1_SRAM_MUX];
    int mux_val_l, mux_val_r;

    data_r = data[AIC_LS_ENV_AXI_HP_DATA_W-1:AIC_LS_ENV_AXI_HP_DATA_W/2];
    data_l = data[AIC_LS_ENV_AXI_HP_DATA_W/2-1:0];
    `uvm_info(get_name(), $sformatf("Deposited data: left: 0x%0x, right: 0x%0x", data_l, data_r), UVM_MEDIUM)

    foreach (data_words[word_index]) begin
      mux_val_r = word_index;  // 0..3
      mux_val_l = (AIC_LS_ENV_L1_SRAM_MUX-1)-mux_val_r;  // complementary yo mux_val_r
      for(int j=0; j<AIC_LS_ENV_L1_SRAM_WORD_SIZE/2; j++) begin	 // we ran from 0 to 63, filling both the lower and upper half in parallel. this is following the SRAM definitions
        data_words[word_index][j] = data_l[(j*AIC_LS_ENV_L1_SRAM_MUX) + mux_val_l];
        data_words[word_index][j+AIC_LS_ENV_L1_SRAM_WORD_SIZE/2] = data_r[(j*AIC_LS_ENV_L1_SRAM_MUX) + mux_val_r];
      end
    end
    foreach (data_words[word_index]) begin
      result[m_bank + word_index*AIC_LS_ENV_L1_NUM_BANKS][s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE +: AIC_LS_ENV_L1_SRAM_WORD_SIZE] = data_words[word_index];
      `uvm_info(get_name(), $sformatf("DEBUG: data_chunk[%0d][%0d:%0d] = data_words[%0d]", m_bank + word_index*AIC_LS_ENV_L1_NUM_BANKS, s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE, s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE+AIC_LS_ENV_L1_SRAM_WORD_SIZE, word_index), UVM_HIGH)
    end
  endtask: print_debug_data

  virtual task write_to_l1();
    hp_addr_t current_addr;
    l1_data_t random_data;
    l1_phys_data_t random_data_phys;
    string mem_location;
    int txn_len = DEFAULT_L1_NUM_BANKS*L1_BANK_DATA_DEPTH; // 4MB of data total, 16 banks * 4096 entries each
    // if (get_verbosity_level() >= UVM_MEDIUM) begin
      l1_data_t data_chunk[AIC_LS_ENV_L1_NUM_BANKS*AIC_LS_ENV_L1_SRAM_MUX];
    // end

    if (m_init_l1_done==1) begin
       `uvm_info(get_name(), "write_to_l1() adlready done! Now exiting task.", UVM_LOW)
      return;
    end
    m_init_l1_done = 1; // set to 1 so that other sequence instance cannot write to L1 anymore

    `uvm_info(get_name(), $sformatf("write_to_l1() started! Start Address: 0x%0x txn_len: %0d", m_ag_mem_baseaddr,txn_len), UVM_LOW)
    for (int sram_mem=0; sram_mem<AIC_LS_ENV_L1_BANK_PARTITION_DEP; sram_mem++) begin
      for (int s_bank=0; s_bank<AIC_LS_ENV_L1_NUM_SUB_BANKS; s_bank++) begin // after filling all values of sram cell, we want to fill subbanks, so we can write them to DUT
        for (int m_bank=0; m_bank<AIC_LS_ENV_L1_NUM_BANKS; m_bank++) begin // total mbanks is the outermost loop
          if (! m_l1_debug_data) begin
            for (int j=0; j < L1_BANK_DATA_WIDTH; j++) begin  // 0..512
              random_data[j] = bit'($urandom_range(0,1));
            end
          end else begin
            for (int j=0; j < L1_BANK_DATA_WIDTH/32; j++) begin
              random_data[32*j +: 32] = current_addr;
            end
          end
        `ifndef TARGET_DFT
          mem_location = $sformatf("%s.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.mem[%0d]", m_l1_mem_root_path, s_bank, m_bank, sram_mem);
        `else
          mem_location = $sformatf("%s.\\g_sbank[%0d].u_sub_bank .\\g_mini_bank[%0d].u_mini_bank .\\g_macro[0].u_macro .u_macro .\\gen_inst.i_sramspehd.u_mem.mem[%0d]", m_l1_mem_root_path, s_bank, m_bank, sram_mem);
        `endif
          /* The way SRAM memory works is:
          we're writing 512 bits of data + 8 (4+2) bits of redundancy. redun is in the middle, so we have 256 + 8 +256 bits of data.
          the way it's physically written is like that:
          MSB: 0 1 2 3 0 1 2 3 redun 3 2 1 0 3 2 1 0 :LSB
          So that right side is mirroring left side (best solution timing wise)
          we need to read the data accordingly as well to know what did we write and where.
          this is why you see that we read differently from the lower half and the upper half*/
          random_data_phys[L1_BANK_DATA_WIDTH/2-1:0] = random_data[L1_BANK_DATA_WIDTH/2-1:0];  // left side - bits 0:255 + 256:259 redun
          random_data_phys[L1_BANK_DATA_WIDTH/2+(AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS*2) +: L1_BANK_DATA_WIDTH/2] = random_data[L1_BANK_DATA_WIDTH-1:L1_BANK_DATA_WIDTH/2]; // have to take redundancy into account as well - right side - bits 260:263 redun + 264:519 
          if (!uvm_hdl_deposit(mem_location, random_data_phys)) begin
            `uvm_fatal(get_name(), $sformatf("Failed to deposit HDL path! %s", mem_location))
          end
          `uvm_info(get_name(), $sformatf("Deposited data for Loop Number = %0d and txn_length =0x%0d. Addr=0x%0x Data = 0x%0x", m_bank + sram_mem*AIC_LS_ENV_L1_NUM_BANKS*AIC_LS_ENV_L1_SRAM_MUX, txn_len, (m_bank + sram_mem*AIC_LS_ENV_L1_BANK_DEPTH)*64, random_data_phys), UVM_MEDIUM)
          if (uvm_top.get_report_verbosity_level() >= UVM_HIGH) begin
            print_debug_data(random_data, m_bank, s_bank, data_chunk);  // Run function only if verbosity is UVM_HIGH or above
          end
        end
      end

      if (uvm_top.get_report_verbosity_level() >= UVM_HIGH) begin
        foreach (data_chunk[i]) begin
          `uvm_info(get_name(), $sformatf("Backdoor WR to L1 Loop Number = %0d and txn_length =0x%0d. Addr=0x%0x Data = 0x%0x", sram_mem*AIC_LS_ENV_L1_NUM_BANKS*AIC_LS_ENV_L1_SRAM_MUX + i, txn_len, (sram_mem*AIC_LS_ENV_L1_NUM_BANKS*AIC_LS_ENV_L1_SRAM_MUX + i)*64, data_chunk[i]), UVM_LOW)
        end
      end
      // end
    end
    `uvm_info(get_name(), $sformatf("write_to_l1() done!"), UVM_LOW)
  endtask: write_to_l1

  function void hdl_write(int index, l1_data_t data);
    /* performs the write of one value to the memory. it does that by reading the whole cell, replacing the relevant bits, and then writing back 
    see more on how SRAM cells work in write_to_l1 comments*/
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
      mem_location = $sformatf("%s.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.mem[%0d]", m_l1_mem_root_path, s_bank, m_bank, sram_index);
    `else
      mem_location = $sformatf("%s.\\g_sbank[%0d].u_sub_bank .\\g_mini_bank[%0d].u_mini_bank .\\g_macro[0].u_macro .u_macro .\\gen_inst.i_sramspehd.u_mem.mem[%0d]", m_l1_mem_root_path, s_bank, m_bank, sram_index);
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

  virtual task write_decompression_stream_to_l1();
    hp_addr_t current_addr;
    int current_index;
    l1_data_t compressed_pword;
    if (m_ag_decompression_en == 1 && m_device== MIFDW && m_decomp_item_h!=null) begin
      `uvm_info(get_name(), $sformatf("write_decompression_stream_to_l1() started! Start Address: 0x%0x", m_ag_mem_baseaddr), UVM_LOW)
      foreach (m_decomp_item_h.m_compressed_pword_q[i]) begin
        current_addr = (m_ag_mem_baseaddr) + i*'d64; // removed mem_offset. mem_offset is not part of Linear Command
        current_index = (current_addr - m_env_cfg_h.m_l1_full_start_addr)/m_env_cfg_h.m_pword_size;
        compressed_pword = m_decomp_item_h.m_compressed_pword_q[i];
        `uvm_info(get_name(), $sformatf("writing to memory at index %d\ndata: 0x%0x", current_index, compressed_pword), UVM_MEDIUM)
        hdl_write(current_index, compressed_pword);
      end
      `uvm_info(get_name(), $sformatf("write_decompression_stream_to_l1() done! End Address: 0x%0x", current_addr), UVM_LOW)
    end
  endtask

  virtual task enable_cmdblk();
    cfg_data_t wdata = 1; // enable value: bit 0: EXEC_EN
    if (m_enable_cmdb==1) begin
      m_ral_env_h.m_ral.write_reg(.regblock_num(m_device_index),  .data(wdata), .name("cmdblk_ctrl"));
      repeat(50) @(posedge m_ral_env_h.m_axi_system_env.vif.common_aclk); // TODO: check if it can be removed
      `uvm_info(get_name(), $sformatf("enable_cmdblk() done for %s", m_device.name()), UVM_LOW)
    end
  endtask

  // Generate CMDB command structure, taken from aic_ls_addrgen_base_test. TODO: Need to improve
  virtual task write_cmdblk_data();
    cfg_addr_t waddr;
    cfg_data_t wdata;
    uvm_event addr_gen_evt =  uvm_event_pool::get_global($sformatf("m_%s_agt_addr_gen_evt", AIC_LS_DMC_DEVICE_NAME[m_device_index]));
    `uvm_info(get_name, $sformatf("m_%s_agt_addr_gen_evt created in sequence!", AIC_LS_DMC_DEVICE_NAME[m_device_index]), UVM_LOW)

    if (m_addr_item == null) begin
      `uvm_fatal(get_name(), "m_addr_item is null!")
    end else begin
      addr_gen_evt.trigger(m_addr_item);
    end

    if (m_program_defmem) begin
      // DESC MEM
      waddr = m_desc_mem_offset + m_device + (m_addr_item.m_dim_def_ptr * 8);
      foreach (m_addr_item.m_dim_def_q[i]) begin
        `uvm_info(get_name, $sformatf("Writing m_addr_item.m_dim_def_q[%0d] with def_ptr: 0x%0x: Addr: 0x%0x Data: 0x%16x", i, m_addr_item.m_dim_def_ptr, (waddr + (i*8)), m_addr_item.m_dim_def_q[i]), UVM_LOW)
      end
      if (m_addr_item.m_dim_def_q.size()> 0) cfg_axi_write(waddr, m_addr_item.m_dim_def_q);

      waddr = m_desc_mem_offset + m_device + (m_addr_item.m_loop_def_ptr * 8);
      foreach (m_addr_item.m_loop_def_q[i]) begin
      end
      if (m_addr_item.m_loop_def_q.size()> 0) cfg_axi_write(waddr, m_addr_item.m_loop_def_q);
    end
    // CMDBLK
    waddr = m_cmdblk_fifo_offset + m_device;
    foreach (m_addr_item.m_cmd_q[i]) begin
      `uvm_info(get_name(), $sformatf("Writing m_addr_item.m_cmd_q[%0d]: Addr: 0x%0x Data: 0x%16x", i, waddr, m_addr_item.m_cmd_q[i]), UVM_LOW)
    end
    cfg_axi_write(waddr, m_addr_item.m_cmd_q);
  endtask

  virtual task wait_data_done();
    m_ls_env_h.m_dmc_data_scb[m_device_index].wait_tlast(m_tlast_count);
    `uvm_info(get_name(), $sformatf("wait_data_done() ended for %s", m_device.name()), UVM_LOW)
  endtask

  virtual task read_register(string name, string field="", bit poll=0, cfg_data_t poll_val=0, bit backdoor=0);
    cfg_data_t rdata, full_data; // full_data is for func cov support
    fork
      forever begin
        if (backdoor==0) begin
          m_ral_env_h.m_ral.read_reg(.regblock_num(m_device_index),  .data(rdata), .name(name), .field(field));
        end else begin
          m_ral_env_h.m_ral.bkdr_read_reg(.regblock_num(m_device_index),  .data(rdata), .name(name), .field(field));
        end
        `ifndef AI_CORE_TOP_ENV_CHECK
          trigger_reg_evt(.reg_name(name)); // for function cov
        `endif
        if (rdata==poll_val || poll==0) begin
          `uvm_info(get_name(), $sformatf("read_register(.name(%s), .field(%s), .poll(%0d), poll_val(0x%0x)) ended for %s with rdata 0x%0x", name, field, poll, poll_val,  m_device.name(), rdata), UVM_MEDIUM)
          break;
        end
        if (poll==1) begin
          repeat(500) @(posedge m_ral_env_h.m_axi_system_env.vif.common_aclk); // do not poll too frequently as it avoids parallel txn to succeed
        end
      end
      begin
        #1ms;
        `uvm_fatal(get_name(), $sformatf("Polling Timeout! Waiting for %s %s %s to be 0x%0x did not happen!", m_device.name(), name, field, poll_val))
      end
    join_any
    disable fork;
  endtask

  virtual task body();
    `uvm_info(get_name(), $sformatf("IFD Sequence start for %s, %s (pre-header)", m_device.name(), convert2string()), UVM_LOW)
    set_header();
    randomize_item();
    if (m_enable_wr_to_l1) begin
      write_to_l1();
    end
    write_decompression_stream_to_l1();
    write_cmdblk_data();
    enable_cmdblk();
`ifndef AI_CORE_TOP_ENV_CHECK
    if(m_wait_data_done_en) begin
        wait_data_done();
    end
    if (m_wait_for_status == 1) begin
      if (m_irq_status_field=="") begin
        read_register("cmdblk_status", "state", 1, 0, m_backdoor_polling); // poll STATE field to be 0 (IDLE)
      end else begin
        read_register("irq_status", m_irq_status_field, 1, 1, m_backdoor_polling); // poll error field to be 1
      end
    end
    `uvm_info(get_name(), $sformatf("IFD Sequence end for %s", m_device.name()), UVM_LOW)
`endif
  endtask : body

endclass : aic_ls_ifd_seq
