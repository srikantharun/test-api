/**************************************************************************
 Testname: dmc_data_scoreboard
 Description: This component implements scoreboard for LS
 the way this works is:
 we have two proccesses running in parallel:
 - one waits for data from reference model: list of addresses, masks, pad values. all of them are put into a queue as one long list of generated expected addresses
 - the second one waits for information from AXI streams.

 once we get an AXI stream we compare it to the generated reference data:
 - for IFD:
  - in case there's compression:
    we compare the uncompressed data we passed on from the compression item, to the output of the IFDW AXI stream.
  - in case there's VTRSP:
    we take the list of expected addresses, read their contents from L1, apply padding and masking, and transpose them (using the same code as in ref model).
    after that we compare the transposed results with the ones from the IFDW AXI stream
  ***decompression and VTRSP are mutually exclusive (one only happens in LINEAR case, the other only happens otherwise)***
  - for the rest, we read the data from L1 using the reference-model-generated addresses, apply padding and masking, and compare them to IFD AXI stream
- for ODR:
  - since we generated the input stream, we read continously from the expected address in L1, and compare the data with the stream we generated. if after some time the data didn't change, we raise an error.
  - in case there's VTRSP, we receive with the reference model, the expected transposed data which should be written into L1 (already padded and masked), and make sure it's equal to the data in L1, in the same matter as above.
 **************************************************************************/
`ifndef _DMC_DATA_SCOREBOARD_SV
`define _DMC_DATA_SCOREBOARD_SV

// AI Core LS Scoreoboard class
class dmc_data_scoreboard extends uvm_scoreboard;

  // Registration with the factory
  `uvm_component_utils(dmc_data_scoreboard)

  // RAL model handle
  aic_ls_subsys_reg_block  scbd_ls_ral;
  uvm_tlm_analysis_fifo #(svt_axi_transaction)      m_axis_tfifo;
  uvm_tlm_analysis_fifo#(dmc_addr_gen_seq_item) m_addr_in_fifo;
  uvm_tlm_analysis_fifo#(odr_stream_mem_t)          m_vtrsp_in_fifo;

  int unsigned               m_ai_core_cid        = DATA_SB_AI_CORE_CID;
  data_sb_axis_addr_t        m_ai_core_base_addr  = DATA_SB_AI_CORE_BASE_ADDR;
  data_sb_axis_addr_t        m_l1_start_offset    = DATA_SB_L1_START_OFFSET;
  data_sb_axis_addr_t        m_l1_end_offset      = DATA_SB_L1_END_OFFSET;
  int unsigned               m_l1_ram_dw          = DATA_SB_L1_RAM_DW;
  int unsigned               m_l1_ram_array_size  = DATA_SB_L1_RAM_ARRAY_SIZE;
  `ifdef AI_CORE_TOP_ENV_CHECK
  string                     m_l1_mem_root_path   = DATA_SB_TOP_L1_MEM_ROOT_PATH;
  `else
  string                     m_l1_mem_root_path   = DATA_SB_L1_MEM_ROOT_PATH;
  `endif
  int unsigned               m_l1_num_banks       = DEFAULT_L1_NUM_BANKS;
  int unsigned               m_pword_size         = AIC_DMC_PWORD_SIZE;
  bit                        m_is_ifd_not_odr     = 1; // 0: ODR, 1: IFD
  bit                        m_has_vtrsp          = 0;
  data_sb_axis_data_t        m_outside_l1_data;
  dpc_cmd_t                  m_dpc_cmd_q[$];
  data_sb_axis_data_t        m_sw_bypass_data_q[$];
  bit                        m_odr_axi_err_en = 0;
  bit                        m_ifd_compression_err_en = 0;
  bit                        m_ifdw_vtrsp_err_en = 0;  // in case we want to force decomp error in ifdw, we toggle this on to skip on decomp

  event                      m_rst_evt;
  event                      m_rst_done_evt;
  bit                        m_is_rst;

  `ifdef AI_CORE_TOP_ENV_CHECK
  string                     refmodel_path = "$REPO_ROOT/hw/ip/aic_ls/default/dv/uvm/refmodels/dmc_addr_gen_ref_model"; // absolute path
 `else
  string                     refmodel_path = "$REPO_ROOT/hw/ip/aic_ls/default/dv/uvm/refmodels/dmc_addr_gen_ref_model"; // absolute path
 `endif
  string                     python_version = "python3.10";
  string                     model_name;

  protected svt_mem              m_hp_slv_mem_h;
  protected data_sb_axis_addr_t  m_l1_start_addr;
  protected data_sb_axis_addr_t  m_l1_end_addr;
  protected int unsigned         m_l1_ram_size_kbytes;
  protected string               m_mem_path_list[L1_SUB_BANKS_PER_BANK];  // the 512 bits of data are divided equally between 4 (for now) sub banks of 128 bits
  protected data_sb_mem_t        m_mem[$];
  protected int                  m_iterations_q[$];
  protected int unsigned         m_axis_tlast_count;
  protected int unsigned         m_axis_word_index;
  protected bit[511:0]           m_uncompressed_data_q[$];
  protected data_sb_axis_addr_t  m_prev_start_addr;
  protected data_sb_axis_addr_t  m_curr_start_addr;
  protected int unsigned         m_prev_dpc_txn_count;
  protected int unsigned         m_curr_dpc_txn_count;
  protected bit                  m_vtrsp_active;
  protected int unsigned         m_timeout_multiplier = 1;

  // Class constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  extern function void build_phase(uvm_phase phase);
  extern function void start_of_simulation_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);
  extern function data_sb_axis_data_t hdl_read(dpc_cmd_t dpc_cmd);
  extern function data_sb_axis_data_t backdoor_read_l1(dpc_cmd_t dpc_cmd);
  extern function void backdoor_read_l1_and_convert(dpc_cmd_t dpc_cmd, ref sb_axis_data_q_t backdoor_data_q, ref string data_source_q[$]);
  extern function void add_mem(dpc_cmd_t dpc_cmd);
  extern function bit  is_outside_l1(data_sb_axis_addr_t addr);
  extern function void reset_scb(bit del_dpc=1);
  extern function void flush_fifos();
  extern function data_sb_axis_data_t apply_pad_value(bit[15:0] pad_val, bit int16_not_int8);
  extern function data_sb_axis_data_t get_masked_data(bit[63:0] dpc_mask, bit[15:0] pad_val, bit int16_not_int8, data_sb_axis_data_t raw_data);
  extern function void set_uncompressed_stream(bit[511:0] stream_data[$]);
  extern function void set_vtrsp_enable(bit en);
  extern function void run_system_cmd(string cmd, bit print_cmd = 1, bit is_fatal=1);
  extern function void update_model_name(int iteration);
  extern function sb_axis_data_q_t transpose_ifd_axi_transcation(int axi_trans_size);
  extern function void create_transpose_data(sb_axis_data_q_t input_data_q, bit int16_to_int8_casting);
  extern function sb_axis_data_q_t collect_transposed_data();
  extern function void check_ifd_stream(svt_axi_transaction axis_txn);
  extern function data_sb_axis_data_t odr_cast_int16_to_int8(dpc_cmd_t dpc_cmd, svt_axi_transaction axis_copy, int current_size);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual task run_scoreboard();
  extern virtual task sample_axi_stream ();
  extern virtual task check_via_odr_stream (svt_axi_transaction axis_txn);
  extern virtual task check_via_icdf_memory ();
  extern virtual task wait_l1_data(dpc_cmd_t dpc_cmd, data_sb_axis_data_t exp_data, int indx, int size);
  extern virtual task wait_tlast(int count=1); // user method to wait for tlast
endclass: dmc_data_scoreboard

function void dmc_data_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  m_axis_tfifo   = new ("m_axis_tfifo", this);
  m_addr_in_fifo = new ("m_addr_in_fifo", this);
  if (m_has_vtrsp==1) begin
    m_vtrsp_in_fifo = new ("m_vtrsp_in_fifo", this);
  end
endfunction: build_phase

function void dmc_data_scoreboard::start_of_simulation_phase(uvm_phase phase);
  super.start_of_simulation_phase(phase);
  m_l1_start_addr = (m_ai_core_cid * m_ai_core_base_addr) + m_l1_start_offset;
  m_l1_end_addr = (m_ai_core_cid * m_ai_core_base_addr) + m_l1_end_offset;
  m_l1_ram_size_kbytes = m_l1_ram_array_size * m_l1_ram_dw / 8;
endfunction: start_of_simulation_phase

function void dmc_data_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  if (!m_axis_tfifo.is_empty()) begin
    `uvm_error(get_name(),"m_axis_tfifo is not empty!")
  end
  if (!m_addr_in_fifo.is_empty()) begin
    `uvm_error(get_name(),"m_addr_in_fifo is not empty!")
  end
  if (m_has_vtrsp && m_vtrsp_active) begin
    if (!m_vtrsp_in_fifo.is_empty()) begin
      `uvm_error(get_name(),"m_vtrsp_in_fifo is not empty!")
    end
  end
  if (m_dpc_cmd_q.size()!=0) begin
    foreach (m_dpc_cmd_q[i]) begin
      `uvm_info(get_name(), $sformatf("m_dpc_cmd_q[%0d]: addr: 0x%0x msk: 0x%0x pad: %0d", i, m_dpc_cmd_q[i].dpc_addr, m_dpc_cmd_q[i].dpc_msk, m_dpc_cmd_q[i].dpc_pad), UVM_LOW)
    end
    `uvm_error(get_name(),"m_dpc_cmd_q is not empty!")
  end
  `uvm_info(get_name(), "Check Phase Done!", UVM_LOW)
endfunction: check_phase

task dmc_data_scoreboard::run_phase (uvm_phase phase);
  super.run_phase(phase);

  forever begin
    fork
      run_scoreboard();
      @ (m_rst_evt); // triggered by the user
    join_any
    disable fork;
    m_is_rst = 1;
    m_dpc_cmd_q.delete();
    @ (m_rst_done_evt); // triggered by the user
    m_is_rst = 0;
    `uvm_info(get_name(), "Reset before 1ns!", UVM_LOW)
    flush_fifos();
    reset_scb();
    `uvm_info(get_name(), "Reset done!", UVM_LOW)
  end
endtask : run_phase

task dmc_data_scoreboard::run_scoreboard ();
  dmc_addr_gen_seq_item dpc_item;
  realtime addr_in_time;
  fork
    forever begin
      m_addr_in_fifo.get(dpc_item);
      if (dpc_item.m_dpc_cmd.dpc_last == 1) m_iterations_q.push_back(dpc_item.iteration);
      // `uvm_info(get_name(), $sformatf("Pushed %0d into m_iterations_q", m_iterations_q[$]), UVM_LOW)
      m_dpc_cmd_q.push_back(dpc_item.m_dpc_cmd);
      if ($realtime != addr_in_time) begin
        addr_in_time =  $realtime;
        m_prev_start_addr = m_curr_start_addr;
        m_curr_start_addr = dpc_item.m_dpc_cmd.dpc_addr;
        m_prev_dpc_txn_count =  m_curr_dpc_txn_count;
      end
      m_curr_dpc_txn_count += 1;
      // ODR requires addiotional logic to account for pad drop
      if (m_is_ifd_not_odr==0) begin
         add_mem(dpc_item.m_dpc_cmd);
      end
    end
    sample_axi_stream();
  join
endtask : run_scoreboard

function void dmc_data_scoreboard::update_model_name(int iteration);
  // this function updates the path where the correct reference model data is located, to read from it vtrsp data
  int unsigned seed;
  string testcase_name;
  if ($value$plusargs("UVM_TESTNAME=%s", testcase_name)) begin
    seed = $get_initial_random_seed();
  end else begin
    `uvm_fatal(get_name(), $sformatf("Tescase name not found!, %s", testcase_name))
  end
  model_name = $sformatf("%s_%s_%0d_%0d", testcase_name, "m_m_ifdw_ref_mdl", iteration, seed); // the ref model path
  `uvm_info(get_name(), $sformatf("update_model_name: updated to %s", model_name), UVM_MEDIUM)
endfunction

function void dmc_data_scoreboard::reset_scb(bit del_dpc=1);
  if (del_dpc) m_dpc_cmd_q.delete();
  m_uncompressed_data_q.delete();
  m_odr_axi_err_en = 0;
  m_ifd_compression_err_en = 0;
  m_mem.delete();
  m_axis_tlast_count = 0;
  m_axis_word_index = 0;
  //m_vtrsp_active = 0;
endfunction

function void dmc_data_scoreboard::flush_fifos();
  int counter;
  svt_axi_transaction axis_txn;
  dmc_addr_gen_seq_item dpc_item;
  odr_stream_mem_t odr_item;
  while(m_axis_tfifo.try_get(axis_txn)) begin
    `uvm_info(get_name(), $sformatf("Got reset axis_txn: %0d", counter), UVM_LOW)
    counter += 1;
  end
  counter = 0;
  while(m_addr_in_fifo.try_get(dpc_item)) begin
    `uvm_info(get_name(), $sformatf("Got reset dpc_item: %0d", counter), UVM_LOW)
    counter += 1;
  end
  counter = 0;
  if (m_has_vtrsp && m_vtrsp_active) begin
    while(m_vtrsp_in_fifo.try_get(odr_item)) begin
      `uvm_info(get_name(), $sformatf("Got reset odr_item: %0d", counter), UVM_LOW)
      counter += 1;
    end
  end
endfunction


function void dmc_data_scoreboard::add_mem(dpc_cmd_t dpc_cmd);
  data_sb_mem_t mem_entry;
  bit last_access = 0;
  int unsigned last_access_index;

  mem_entry.addr = dpc_cmd.dpc_addr;
  if (dpc_cmd.dpc_pad == 1) begin
    mem_entry.write_type = DROP_DATA;
    mem_entry.skip = 1;
  end else if (dpc_cmd.dpc_msk == 0) begin
    mem_entry.write_type = WRITE_INTRA_PAD;
  end else begin
    mem_entry.write_type = NORMAL_DATA;
  end
  m_mem.push_back(mem_entry);

  for (int i=m_mem.size()-1; i >=0; i--) begin
    if (m_mem[i].addr == dpc_cmd.dpc_addr) begin
      if (m_mem[i].write_type != DROP_DATA) begin
        m_mem[i].skip = 0;
        if (last_access == 0) begin
          last_access = 1;
          last_access_index = i;
        end
      end
      if (last_access == 1 && i != last_access_index) begin
        m_mem[i].skip = 1;
      end
    end
  end
endfunction

function data_sb_axis_data_t dmc_data_scoreboard::hdl_read(dpc_cmd_t dpc_cmd);
  /*
    hdl_top.dut.u_aic_ls.i_l1.i_l1_mem.g_l1_bank[0].i_l1_bank.g_l1_ram[0].i_l1_ram.i_tc_sram.i_inst.i_sramsphs.uut.mem_core_array[0] --> 4096 entries, 256 bits == 128 Kbytes
    hdl_top.dut.u_aic_ls.i_l1.i_l1_mem.g_l1_bank[0].i_l1_bank.g_l1_ram[1].i_l1_ram.i_tc_sram.i_inst.i_sramsphs.uut.mem_core_array[0] --> 4096 entries, 256 bits == 128 Kbytes
    ...
    256 Kbytes * 16 banks = 4096 Kbytes = 4MB
  */
  data_sb_axis_data_t backdoor_data;
  phys_data_sb_axis_data_t temp_data;
  data_sb_axis_half_data_t temp_data_l, temp_data_r;
  int index, offset, mbank_num, sram_index, mask;
  int mux_val_l, mux_val_r;

  if (dpc_cmd.dpc_addr % m_pword_size != 0) begin
    `uvm_error(get_name(), $sformatf("Address 0x%0x not aligned to PWORD (i.e. %0d bytes)!", dpc_cmd.dpc_addr, m_pword_size))
  end else begin
    index = (dpc_cmd.dpc_addr - m_l1_start_addr)/m_pword_size;
    mbank_num = index%DEFAULT_L1_NUM_BANKS;
    offset = index/DEFAULT_L1_NUM_BANKS;
    sram_index = offset/DATA_SB_L1_SRAM_MUX;
    // DEBUG
    //`uvm_info(get_name(), $sformatf("DBG: addr: 0x%0x m_l1_full_start_addr: 0x%0x data_size: %0d (bytes) m_l1_num_banks: %0d m_l1_num_sub_banks: %0d", addr, m_env_cfg_h.m_l1_full_start_addr, memory_block_size, m_env_cfg_h.m_l1_num_banks, m_env_cfg_h.m_l1_num_sub_banks), UVM_LOW)
    `uvm_info(get_name(), $sformatf("DBG: addr: 0x%0x L1 index: 0x%0x Bank: %0d Index: %0d", (dpc_cmd.dpc_addr - m_l1_start_addr), index, mbank_num, offset), UVM_FULL)
  end

  `ifndef TARGET_DFT
  foreach (m_mem_path_list[i]) begin
    m_mem_path_list[i] = $sformatf("%s.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.mem[%0d]", m_l1_mem_root_path, i, mbank_num, sram_index);
  end
`else
  foreach (m_mem_path_list[i]) begin
    m_mem_path_list[i] = $sformatf("%s.\\g_sbank[%0d].u_sub_bank .\\g_mini_bank[%0d].u_mini_bank .\\g_macro[0].u_macro .u_macro .\\gen_inst.i_sramspehd.u_mem.mem[%0d]", m_l1_mem_root_path, i, mbank_num, sram_index);
  end
`endif


  foreach (m_mem_path_list[i]) begin
    if (!uvm_hdl_read(m_mem_path_list[i], temp_data)) begin
      `uvm_fatal(get_name(), $sformatf("Failed to read HDL path! %s", m_mem_path_list[i]))
    end
    mux_val_r = offset%DATA_SB_L1_SRAM_MUX;
    mux_val_l = (DATA_SB_L1_SRAM_MUX-1)-mux_val_r;

    temp_data_r = temp_data[DATA_SB_L1_SRAM_FULL_SIZE-1:(AIC_HT_AXI_DATA_WIDTH/2)+(DATA_SB_L1_SRAM_REDUNDANCY_BITS*2)];	// WO redundancy bits - 256+8...512+8
    temp_data_l = temp_data[AIC_HT_AXI_DATA_WIDTH/2-1:0];

    // `uvm_info(get_name(), $sformatf("Got the following data: Addr: 0x%0x, index: %0d, mbank_num: 0x%0x, sram_index: 0x%0x, i: %0d, data: 0x%0x", (dpc_cmd.dpc_addr - m_l1_start_addr), index, mbank_num, sram_index, i, temp_data), UVM_LOW)

    // `uvm_info(get_name(), $sformatf("More debug: temp_data_l is: 0x%x, temp_data_r is: 0x%x", temp_data_l, temp_data_r), UVM_LOW)
    for(int j=0; j<DATA_SB_L1_SRAM_WORD_SIZE/2; j++) begin	 // we ran from 0 to 63, filling both the lower and upper half in parallel. this is following the SRAM definitions
      backdoor_data[j+(i*DATA_SB_L1_SRAM_WORD_SIZE)] = temp_data_l[(j*DATA_SB_L1_SRAM_MUX) + mux_val_l];
      backdoor_data[j+DATA_SB_L1_SRAM_WORD_SIZE/2+(i*DATA_SB_L1_SRAM_WORD_SIZE)] = temp_data_r[(j*DATA_SB_L1_SRAM_MUX) + mux_val_r];
      // `uvm_info(get_name(), $sformatf("More debug: backdoor_data[%0d] = temp_data_l[%0d]", j+(i*DATA_SB_L1_SRAM_WORD_SIZE), (j*DATA_SB_L1_SRAM_MUX) + mux_val_l), UVM_LOW)
      // `uvm_info(get_name(), $sformatf("More debug: backdoor_data[%0d] = temp_data_r[%0d]", j+DATA_SB_L1_SRAM_WORD_SIZE/2+(i*DATA_SB_L1_SRAM_WORD_SIZE), (j*DATA_SB_L1_SRAM_MUX) + DATA_SB_L1_SRAM_WORD_SIZE/2 + mux_val_r), UVM_LOW)
    end
    // `uvm_info(get_name(), $sformatf("More debug: backdoor_data for this iteration: 0x%x", backdoor_data[i*DATA_SB_L1_SRAM_WORD_SIZE +: DATA_SB_L1_SRAM_WORD_SIZE]), UVM_LOW)
  end
  return backdoor_data;
endfunction: hdl_read

function bit dmc_data_scoreboard::is_outside_l1(data_sb_axis_addr_t addr);
  // nothing should be outside l1 if it's not dropped!!!
  `uvm_info(get_name(), $sformatf("Addr: 0x%0x  L1 Start: 0x%0x L1 End: 0x%0x", addr, m_l1_start_addr, m_l1_end_addr), UVM_FULL)
  return (addr < m_l1_start_addr || addr > m_l1_end_addr);
endfunction

function data_sb_axis_data_t dmc_data_scoreboard::apply_pad_value(bit[15:0] pad_val, bit int16_not_int8);
  data_sb_axis_data_t padded_data;
  if (int16_not_int8) padded_data = {(AIC_HT_AXI_DATA_WIDTH/2){pad_val}}; // if we're int16, repeat 32 time the 16 bit value
  else padded_data = {(AIC_HT_AXI_DATA_WIDTH){pad_val[7:0]}}; // else, repeat 64 time the 8 bit value
  return padded_data;
endfunction

function data_sb_axis_data_t dmc_data_scoreboard::get_masked_data(bit[63:0] dpc_mask, bit[15:0] pad_val, bit int16_not_int8, data_sb_axis_data_t raw_data);
  data_sb_axis_data_t mask_data = raw_data;
  `uvm_info(get_name(), $sformatf("received intra_pad_val is 0x%4x", pad_val), UVM_HIGH)
  foreach (dpc_mask[i]) begin
    if (!dpc_mask[i]) begin  // mask is 0. writing explicitly for convenience
      // in case we're in int16 mode, and we're in an odd index, we apply the upper 8 bit of the intra_pad value.
      // in any other case - int16 mode+even index/ int8 mode, we apply the lower 8 bit of the intra_pad value.
      mask_data[i*8+:8] = (int16_not_int8 && (i%2 != 0)) ? pad_val[15:8] : pad_val[7:0];
    end
  end
  `uvm_info(get_name(), $sformatf("get_masked_data: masked data: 0x%0x", mask_data), UVM_HIGH)
  return mask_data;
endfunction

function void dmc_data_scoreboard::set_uncompressed_stream(bit[511:0] stream_data[$]);
  m_uncompressed_data_q.delete();
  foreach (stream_data[i]) begin
    m_uncompressed_data_q.push_back(stream_data[i]);

  end
  `uvm_info(get_name(), "Setting of uncompressed data done!", UVM_LOW)
  foreach (m_uncompressed_data_q[i]) begin
    `uvm_info(get_name(), $sformatf("SB Uncompressed data[%0d] 0x%0x!", i, m_uncompressed_data_q[i]), UVM_MEDIUM)
  end
endfunction

function void dmc_data_scoreboard::set_vtrsp_enable(bit en);
  if (m_has_vtrsp==0 && en==1) begin
    `uvm_fatal(get_name(), "Setting VTRSP enable to an unsupported device!")
  end else begin
    m_vtrsp_active = en;
  end
endfunction

function void dmc_data_scoreboard::run_system_cmd(string cmd, bit print_cmd = 1, bit is_fatal=1);
  // simple function to run system commands in a safe manner
  if ($system(cmd) != 0) begin
    `uvm_error(get_name(), $sformatf("Exit status not 0 for %s", cmd));
    if (is_fatal) begin
      `uvm_fatal(get_name(), $sformatf("Exit status not 0 for %s", cmd));
    end
  end else begin
    if (print_cmd) begin
      `uvm_info(get_name(), $sformatf("Executing cmd: \n\n %s \n\n done!", cmd), UVM_NONE);
    end
  end
endfunction

function void dmc_data_scoreboard::create_transpose_data(sb_axis_data_q_t input_data_q, bit int16_to_int8_casting);
  // this function creates the data for the transpose. putting it separately to not overcrowd transpose_ifd_axi_transcation
  // similar to get_odr_stream in dmc_addr_gen_ref_model, but done here to avoid changes in data between ref generation and IFD AXI stream
  string bash_cmd;
  int batch_size = 300;
  int input_data_size = input_data_q.size();
  string vtrsp_recipe_path = $sformatf("./refmodel/%s/vtrsp_recipe.json", model_name);
  string vtrsp_ifd_memory_path = $sformatf("./refmodel/%s/vtrsp_output.txt", model_name);
  string vtrsp_input_data_q_path = $sformatf("./refmodel/%s/vtrsp_input_data_q.json", model_name);
  int start_index;

  `uvm_info(get_name(), $sformatf("IFD Stream size is %0d", input_data_size), UVM_LOW)

  $sformat(bash_cmd, "echo -e '");
  $sformat(bash_cmd, "%s[\n", bash_cmd); 
  $sformat(bash_cmd, "%s' > %s", bash_cmd, vtrsp_input_data_q_path);
  run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
  while (input_data_size > 0) begin
    /* in some cases, the stream is too tolng to write it in one echo command. because of this we need to write it in part
    how this work is we write every time batch_size of the input_data_q, until we have less then batch_size, then we write what's left and close
    */
    if (input_data_size > batch_size) begin  // if we have more then batch_size left
      start_index = input_data_q.size()-input_data_size;
      bash_cmd = "";
      $sformat(bash_cmd, "echo -e '");
      for (int i = start_index; i < start_index+batch_size; i++) begin  // loop to write batch_size entries
        `uvm_info(get_name(), $sformatf("IFD Stream[%0d]: 0x%128x", i, input_data_q[i]), UVM_MEDIUM)
        $sformat(bash_cmd, "%s  \"%128x\",\n", bash_cmd, input_data_q[i]);
      end
      $sformat(bash_cmd, "%s' >> %s", bash_cmd, vtrsp_input_data_q_path);
      input_data_size = input_data_size-batch_size;
      run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
    end else begin  // if we have less then batch_size left
      start_index = input_data_q.size()-input_data_size;
      bash_cmd = "";
      $sformat(bash_cmd, "echo -e '");
      for (int i = start_index; i < input_data_q.size(); i++) begin  // loop to write what's left
        `uvm_info(get_name(), $sformatf("IFD Stream[%0d]: 0x%128x", i, input_data_q[i]), UVM_MEDIUM)
        $sformat(bash_cmd, "%s  \"%128x\"%s\n", bash_cmd, input_data_q[i], i!=input_data_q.size()-1 ? ",":"");  // we add ',' for everything except the last entry!
      end
      $sformat(bash_cmd, "%s]\n", bash_cmd);  // closes a json file
      $sformat(bash_cmd, "%s' >> %s", bash_cmd, vtrsp_input_data_q_path);
      input_data_size = 0;
      run_system_cmd(.cmd(bash_cmd), .print_cmd(0));
    end
  end
  `uvm_info(get_name(), $sformatf("create_transpose_data: running vtrsp_data_gen.py for queue size of %0d", input_data_q.size()), UVM_MEDIUM)
  if (int16_to_int8_casting) bash_cmd = $sformatf("vtrsp_data_gen %s %s %s %s", vtrsp_input_data_q_path, vtrsp_recipe_path, vtrsp_ifd_memory_path, "int16_to_int8");  // now run python model to transpose the odr stream
  else bash_cmd = $sformatf("vtrsp_data_gen %s %s %s", vtrsp_input_data_q_path, vtrsp_recipe_path, vtrsp_ifd_memory_path);  // now run python model to transpose the odr stream
  run_system_cmd(bash_cmd);
  `uvm_info(get_name(), $sformatf("create_transpose_data: done queue size of %0d", input_data_q.size()), UVM_MEDIUM)
endfunction

function sb_axis_data_q_t dmc_data_scoreboard::collect_transposed_data();
  // this function reads from the file that contains transposed data, to then compare to axi stream!
  sb_axis_data_q_t vtrsp_output_q;
  int file_handle;
  data_sb_axis_data_t current_data;
  data_sb_axis_addr_t current_addr;
  bit[AIC_DMC_PWORD_SIZE-1:0] current_mask;
  bit[15:0] intra_pad_value;
  string vtrsp_ifd_memory_path = $sformatf("./refmodel/%s/vtrsp_output.txt", model_name);
  `uvm_info(get_name(), $sformatf("Reading memory file: %s", vtrsp_ifd_memory_path), UVM_LOW)

  file_handle = $fopen(vtrsp_ifd_memory_path, "r");
  if (file_handle) begin
    while (!$feof(file_handle)) begin
      $fscanf(file_handle, "addr: %d mask: %b intra_pad_value: %h data: %h", current_addr, current_mask, intra_pad_value, current_data);  // the file contains address, mask, data
      if ($feof(file_handle)) break; // we can end the line after fscanf
      vtrsp_output_q.push_back(current_data);
      `uvm_info(get_name(), $sformatf("Assigning Addr: 0x%0x with Mask: 0x%0x, intra_pad_value: 0x%0x and Data: 0x%128h", current_addr, current_mask, intra_pad_value, current_data), UVM_MEDIUM)
    end
    $fclose(file_handle);
  end
  `uvm_info(get_name(), $sformatf("collect_transposed_data: done with queue size of %0d", vtrsp_output_q.size()), UVM_MEDIUM)
  return vtrsp_output_q;
endfunction

function data_sb_axis_data_t dmc_data_scoreboard::backdoor_read_l1(dpc_cmd_t dpc_cmd);
  data_sb_axis_data_t rdata;
  if (dpc_cmd.dpc_pad==1) begin
    rdata = apply_pad_value(.pad_val(dpc_cmd.dpc_pad_val), .int16_not_int8(dpc_cmd.dpc_config));
  end else begin
    rdata = hdl_read(dpc_cmd);
  end
  rdata = get_masked_data(.dpc_mask(dpc_cmd.dpc_msk), .pad_val(dpc_cmd.dpc_intra_pad_val), .int16_not_int8(dpc_cmd.dpc_config), .raw_data(rdata)); // in IFD case, mask format is the vector mode
  `uvm_info(get_name(), $sformatf("L1 Data for address: 0x%0x at path0 %s is 0x%0x", dpc_cmd.dpc_addr, m_mem_path_list[0], rdata), UVM_MEDIUM)
  return rdata;
endfunction

function void dmc_data_scoreboard::backdoor_read_l1_and_convert(dpc_cmd_t dpc_cmd, ref sb_axis_data_q_t backdoor_data_q, ref string data_source_q[$]);
  data_sb_axis_data_t pword64i8_data;
  data_sb_axis_half_data_t pword32i16_pre_extension;
  data_sb_axis_data_t pword32i16_data[2];
  data_sb_axis_data_t return_data_q[$];
  if (dpc_cmd.dpc_pad==1) begin
    pword64i8_data = '1;
    `uvm_info(get_name(), $sformatf("backdoor_read_l1_and_convert: padded data is 0x%0x", pword64i8_data), UVM_HIGH)
  end else begin
    pword64i8_data = hdl_read(dpc_cmd);
    `uvm_info(get_name(), $sformatf("backdoor_read_l1_and_convert: read from address 0x%0x data 0x%0x", dpc_cmd.dpc_addr, pword64i8_data), UVM_HIGH)
  end
  foreach (pword32i16_data[i]) begin
    bit[AIC_HT_AXI_DATA_WIDTH/8-1:0] extended_mask;  // we will write a value in case of no padding, and keep dpc_msk for the other case
    for (int cur_byte=0; cur_byte<(AIC_HT_AXI_DATA_WIDTH/2)/8; cur_byte++) begin // 0-32
      extended_mask[cur_byte*2 +: 2] = {2{dpc_cmd.dpc_msk[cur_byte+i*((AIC_HT_AXI_DATA_WIDTH/2)/8)]}};  // extending the mask
    end
    pword32i16_pre_extension = pword64i8_data[(AIC_HT_AXI_DATA_WIDTH/2)*i +: (AIC_HT_AXI_DATA_WIDTH/2)];  // 0-255, 256-512
    if (dpc_cmd.dpc_pad==1) pword32i16_data[i] = apply_pad_value(.pad_val(dpc_cmd.dpc_pad_val), .int16_not_int8(dpc_cmd.dpc_config));
    else begin
      for (int cur_byte=0; cur_byte<(AIC_HT_AXI_DATA_WIDTH/2)/8; cur_byte++) begin // 0-32
        pword32i16_data[i][cur_byte*16 +: 16] = { {8{pword32i16_pre_extension[(cur_byte*8)+7]}}, pword32i16_pre_extension[cur_byte*8 +: 8] };  // sign_extending
      end
    end
    `uvm_info(get_name(), $sformatf("backdoor_read_l1_and_convert: pre-extended mask 0x%0x and data 0x%0x. converted to mask 0x%x and data 0x%x", dpc_cmd.dpc_msk, pword32i16_pre_extension, extended_mask, pword32i16_data[i]), UVM_HIGH)
    pword32i16_data[i] = get_masked_data(.dpc_mask(extended_mask), .pad_val(dpc_cmd.dpc_intra_pad_val), .int16_not_int8(dpc_cmd.dpc_config), .raw_data(pword32i16_data[i]));
    `uvm_info(get_name(), $sformatf("backdoor_read_l1_and_convert: pushing to backdoor_data_q data 0x%x", pword32i16_data[i]), UVM_HIGH)
    backdoor_data_q.push_back(pword32i16_data[i]);
    data_source_q.push_back((dpc_cmd.dpc_pad) ? "CMDB_PAD_I16_DATA" : "CMDB_L1_I16");
  end
endfunction

function sb_axis_data_q_t dmc_data_scoreboard::transpose_ifd_axi_transcation(int axi_trans_size);
  // the way this function works is:
  // once we got the AXI stream with the IFD data, it's already transposed.
  // now we'll fetch all ifd data from L1 ourselves, transpose it, and then fo one by one with it and compare it to the AXI stream data
  sb_axis_data_q_t vtrsp_input_data_q, vtrsp_output_data_q;
  string data_source_q[$];  // not in use, just for simplicity
  int updated_trans_size = axi_trans_size;
  // get correct testname for file names!
  `uvm_info(get_name(), $sformatf("IFD transpose started!"), UVM_LOW)

  for (int i=0; i<updated_trans_size; i++) begin  // m_dpc_cmd_q might already contains the data for the next transactions as well, so we should only read the current data!
    data_sb_axis_data_t current_data;
    dpc_cmd_t dpc_cmd = m_dpc_cmd_q[i];
    if (dpc_cmd.dpc_config && !dpc_cmd.dpc_format) begin // format = 0 , vect_mode (config) = 1 means we have to turn one data line of 64 int8 numbers into two lines of 32 int16 numbers
      if (i == 0) updated_trans_size = axi_trans_size/2; // in case we're running int16 to int8 conversion, AXI transaction is twice as big as dpc_cmd size
      backdoor_read_l1_and_convert(dpc_cmd, vtrsp_input_data_q, data_source_q);
      `uvm_info(get_name(), $sformatf("Transpose data needs to be converted"), UVM_MEDIUM)
    end else begin
      // in case of VTRSP, we first drop and pad, and only then transpose
      current_data = backdoor_read_l1(dpc_cmd);
      vtrsp_input_data_q.push_back(current_data);
    end
  end
  `uvm_info(get_name(), $sformatf("transpose_ifd_axi_transcation: got a total transpose input queue size of %0d", vtrsp_input_data_q.size()), UVM_LOW)
  update_model_name(m_iterations_q.pop_front());  // need this trickery with iteration data because otherwise it's updated too early
  create_transpose_data(vtrsp_input_data_q, (updated_trans_size == axi_trans_size/2));  // create vtrsp input json
  vtrsp_output_data_q = collect_transposed_data();
  if (vtrsp_output_data_q.size() != vtrsp_input_data_q.size()) `uvm_error(get_name(), $sformatf("VTRSP size mismatch! input length: %0d, output length: %0d!", vtrsp_input_data_q.size(), vtrsp_output_data_q.size()))
  return vtrsp_output_data_q;
endfunction

function void dmc_data_scoreboard::check_ifd_stream(svt_axi_transaction axis_txn);
  int transaction_size = axis_txn.tdata.size;
  dpc_cmd_t dpc_cmd;
  bit[35:0] addr;
  bit pad;
  byte pad_val;
  data_sb_axis_data_t backdoor_data;
  sb_axis_data_q_t backdoor_data_q;
  string data_source;
  int delete_count;
  string data_source_q[$];

  if (m_vtrsp_active && m_ifdw_vtrsp_err_en) begin  // IFDW VTRSP - this function performs transpose. after that we just need to compare to AXI stream data.
    `uvm_info(get_name(), $sformatf("m_ifdw_vtrsp_err_en is on, ignoring data compare!"), UVM_MEDIUM)
    return;
  end else if (m_vtrsp_active && !m_ifdw_vtrsp_err_en) begin  // IFDW VTRSP - this function performs transpose. after that we just need to compare to AXI stream data.
    backdoor_data_q = transpose_ifd_axi_transcation(transaction_size);
  end
  if (m_dpc_cmd_q[0].dpc_config && !m_dpc_cmd_q[0].dpc_format) transaction_size = transaction_size/2;  // in case of IFD with casting, need to cut transaction size by 2
  for (int index = 0; index < transaction_size; index++) begin
    if (m_dpc_cmd_q.size()==0 && m_uncompressed_data_q.size()==0) begin
      if (m_dpc_cmd_q[0].dpc_config && !m_dpc_cmd_q[0].dpc_format) break;  // this is the expected behavior for extending int8 data to int16. we have twice the data.
      else `uvm_error(get_name(), $sformatf("Datapath Command Queue Size is Zero for txn[%0d] data: 0x%0x", index, axis_txn.tdata[index]))
    end else if (m_vtrsp_active) begin  // VTRSP!
      dpc_cmd = m_dpc_cmd_q.pop_front();
      data_source_q.push_back(dpc_cmd.dpc_pad ? "IFDW_PAD_DATA_VTRSP" : "IFDW_VTRSP");
    end else if (m_uncompressed_data_q.size() != 0) begin  // Compression!
      if (m_uncompressed_data_q.size() != transaction_size) `uvm_error(get_name(), $sformatf("Decompression Stream Length Mismatch! Exp: %0d Act: %0d", m_uncompressed_data_q.size(), transaction_size))
      else begin
        backdoor_data_q.push_back(m_uncompressed_data_q[index]);
        data_source_q.push_back("CMDB_UNCOMP_DATA");
      end
    end else begin  // simple case
      dpc_cmd = m_dpc_cmd_q.pop_front();
      if (is_outside_l1(dpc_cmd.dpc_addr) && !dpc_cmd.dpc_pad) `uvm_error(get_name(), $sformatf("Address out of L1 range: 0x%0x!", dpc_cmd.dpc_addr))
      else if (dpc_cmd.dpc_config && !dpc_cmd.dpc_format) begin // format = 0 , vect_mode (config) = 1 means we have to turn one data line of 64 int8 numbers into two lines of 32 int16 numbers
        backdoor_read_l1_and_convert(dpc_cmd, backdoor_data_q, data_source_q);
      end else begin
        backdoor_data_q.push_back(backdoor_read_l1(dpc_cmd)); // applies padding and masking
        data_source_q.push_back((dpc_cmd.dpc_pad) ? "CMDB_PAD_DATA" : "CMDB_L1");
      end
    end
  end
  if (backdoor_data_q.size() != axis_txn.tdata.size) `uvm_error(get_name(), $sformatf("Refmodel data length is different from AXI stream length. Ref length: %0d, AXI stream length: %0d", backdoor_data_q.size(), axis_txn.tdata.size))
  foreach(backdoor_data_q[index]) begin
    if (backdoor_data_q[index] != axis_txn.tdata[index]) begin
      if (m_ifd_compression_err_en==0) begin
        `uvm_error(get_name(), $sformatf("%s Data Mismatch for txn[%0d]!\nAddr: 0x%0x\nExp: 0x%0x\nAct: 0x%0x", data_source_q[index], index, dpc_cmd.dpc_addr, backdoor_data_q[index], axis_txn.tdata[index]))
        `uvm_info(get_name(), $sformatf("m_uncompressed_data_q.size(): %0d m_dpc_cmd_q.size(): %0d", m_uncompressed_data_q.size(), m_dpc_cmd_q.size()), UVM_LOW)
      end else begin
        `uvm_info(get_name(), $sformatf("Data compare ignored for txn[%0d]! Addr: 0x%0x Exp: 0x%0x Act: 0x%0x", index, dpc_cmd.dpc_addr, backdoor_data_q[index], axis_txn.tdata[index]), UVM_MEDIUM)
      end
    end else begin
      `uvm_info(get_name(), $sformatf("%s Match for txn[%0d/%0d]\naddr: 0x%0x\ndata: 0x%0x", data_source_q[index], index, transaction_size-1, dpc_cmd.dpc_addr, axis_txn.tdata[index]), UVM_MEDIUM)
    end
  end
endfunction

task dmc_data_scoreboard::sample_axi_stream ();
  svt_axi_transaction axis_txn;
  int fifo_sz;
  // Main code
  forever begin
    m_axis_tfifo.get(axis_txn);
    fifo_sz  = axis_txn.tdata.size;
    `uvm_info(get_name(), $sformatf("got a transaction of size %0d, in %s, VTRSP: %0d, DPC_CMD size is %0d", fifo_sz, m_is_ifd_not_odr ? "IFD" : "ODR", m_vtrsp_active, m_dpc_cmd_q.size()), UVM_LOW)
    if (m_is_ifd_not_odr==1) begin
      // Compare AXI stream output to L1 data
      check_ifd_stream(axis_txn);
    end else begin
      if (m_vtrsp_active==0) check_via_odr_stream(axis_txn); // Get AXI Stream input and wait for data to be written to memory
      else check_via_icdf_memory();
    end
    m_axis_tlast_count += 1;
    m_axis_word_index += fifo_sz;
  end // end forever
endtask : sample_axi_stream

function data_sb_axis_data_t dmc_data_scoreboard::odr_cast_int16_to_int8(dpc_cmd_t dpc_cmd, svt_axi_transaction axis_copy, int current_size);
  /*
  This function casts from int16 format data to int8 format data. it does so the following way:
  we read from file 2 lines of data, they have different data, with the same address/mask/intra_pad_value, because the later come from the address generation block, which function in the int8 format (in this case, i.e. when dpc_cmd.format=0)
  since the data is in pword32int16 format, it means we have a total of 64 words, each 16 bits. we have a mask of 64 bits, so each bit of mask represents whether corresponding word will be masked or not.
  so we split the mask into lower 32 bits and upper. we use the lower bits to mask the first data line, and the upper to mask the second data line. where we mask the data, we replace it with intra_pad_value.
  after that we cast it down from 16 bits to 8 bits in the following manner - if the value is [-128:127], we leave it as is (already 8 bit), if it's lower then -128, we use -128, and if it's higher then 127, we use 127.
  */
  data_sb_axis_data_t pword64i8_data;
  data_sb_axis_data_t pword32i16_data;
  data_sb_axis_half_addr_t mask[2];
  //we split the mask first, then extend it, then use it to turn two entries into one, then send to wait for l1.
  foreach (mask[i]) begin
    mask[i] = dpc_cmd.dpc_msk[i*(AIC_DMC_PWORD_SIZE/2) +: (AIC_DMC_PWORD_SIZE/2)];  // take 32 bit of the mask. each bit represents whether a 32 bit number is used or not
    pword32i16_data = axis_copy.tdata[current_size];
    `uvm_info(get_name(), $sformatf("odr_cast_int16_to_int8: AXI data is 0x%128x, mask is 0x%16x\ncopied data is 0x%128x, mask is 0x%8x", axis_copy.tdata[current_size], dpc_cmd.dpc_msk, pword32i16_data, mask[i]), UVM_MEDIUM)
    current_size ++;
    for (int curr_num=0; curr_num < 32; curr_num++) begin
      bit signed [7:0]  int_8bit;
      bit signed [15:0] int_16bit;
      int_16bit = mask[i][curr_num] ? pword32i16_data[curr_num*16 +: 16] : dpc_cmd.dpc_intra_pad_val;
      int_8bit = (int_16bit > 127) ? 127 : ((int_16bit < -128) ? -128 : int_16bit[7:0]);
      pword64i8_data[i*256 + curr_num*8 +: 8] = int_8bit;
      `uvm_info(get_name(), $sformatf("odr_cast_int16_to_int8: i is %0d, curr_num is %0d, Added 16/8 bit number 0x%0x/0x%0x!\nData is now 0x%0x", i, curr_num, int_16bit, int_8bit, pword64i8_data), UVM_HIGH)
    end
  end
  return pword64i8_data;
endfunction

task dmc_data_scoreboard::check_via_odr_stream(svt_axi_transaction axis_txn);
  int fifo_size  = axis_txn.tdata.size;
  int current_size = 0;
  svt_axi_transaction axis_copy;
  dpc_cmd_t dpc_cmd;
  axis_copy = svt_axi_transaction::type_id::create("axis_copy");
  axis_copy.copy(axis_txn);
  `uvm_info(get_name(), $sformatf("Debug axis_copy:\n%s", axis_copy.sprint()), UVM_MEDIUM)

  while (current_size != fifo_size) begin // we do a while statement because sometimes we fetch 2 entries and sometimes one
    `uvm_info(get_name(), $sformatf("Got AXI-S txn[%0d/%0d] data: 0x%0x", current_size, (fifo_size-1), axis_copy.tdata[current_size]), UVM_MEDIUM)
    dpc_cmd = m_dpc_cmd_q.pop_front();
    if (is_outside_l1(dpc_cmd.dpc_addr) && !dpc_cmd.dpc_pad) `uvm_error(get_name(), $sformatf("Address out of L1 range: 0x%0x!", dpc_cmd.dpc_addr))
    if (m_odr_axi_err_en==0) begin
      if (dpc_cmd.dpc_config && !dpc_cmd.dpc_format) begin // format = 0 , vect_mode (config) = 1 means we have to turn one data line of 64 int8 numbers into two lines of 32 int16 numbers
        data_sb_axis_data_t pword64i8_data;
        pword64i8_data = odr_cast_int16_to_int8(dpc_cmd, axis_copy, current_size);
        current_size = current_size + 2;  // when we're converting from int 16 to int 8, we receive an AXI transaction twice the size of what's actually written to L1
        m_mem[0].write_type = CASTED_DATA;  // do this to avoid masking the data again later.
        wait_l1_data(dpc_cmd, pword64i8_data, (current_size-1)/2, fifo_size); // cmdblk within L1
      end else begin
        wait_l1_data(dpc_cmd, axis_copy.tdata[current_size], current_size, fifo_size); // cmdblk within L1
        current_size ++;
      end
    end
  end
endtask

task dmc_data_scoreboard::check_via_icdf_memory();
  odr_stream_mem_t odr_item;
  dpc_cmd_t dpc_cmd;
  data_sb_axis_data_t backdoor_data;
  data_sb_axis_quarter_data_t data_list[L1_SUB_BANKS_PER_BANK];
  bit has_error;
  int counter = 0;
  if (m_has_vtrsp && m_vtrsp_active) begin
    while(m_vtrsp_in_fifo.try_get(odr_item)) begin
      `uvm_info(get_name(), $sformatf("Got icdf odr_item[%0d] | addr: 0x%0x, data: 0x%0x", counter, odr_item.addr, odr_item.data), UVM_MEDIUM)
      dpc_cmd.dpc_addr = odr_item.addr;
      has_error =1;
      if (is_outside_l1(dpc_cmd.dpc_addr) && !dpc_cmd.dpc_pad) `uvm_error(get_name(), $sformatf("Address out of L1 range: 0x%0x!", dpc_cmd.dpc_addr))
      `uvm_info(get_name(), $sformatf("Wait for Data of 0x%0x for address 0x%0x index: %0d  at path0/1 %s after 1us. started!", odr_item.data, odr_item.addr, counter, m_mem_path_list[0]), UVM_MEDIUM)
      fork
        begin
          repeat (m_timeout_multiplier) #1us;
          if (m_odr_axi_err_en==0) begin
            `uvm_error(get_name(), $sformatf("\n Data of 0x%0x for address 0x%0x index: %0d did not arrive at path0/1 %s after 1us. Instead, data is: 0x%0x", odr_item.data, odr_item.addr, counter, m_mem_path_list[0], backdoor_data))
          end
        end
        begin
          do begin
            backdoor_data = hdl_read(dpc_cmd);
            #10ps;
          end while (backdoor_data != odr_item.data);
          has_error = 0;
        end
      join_any
      disable fork;
      if (has_error==0 && m_odr_axi_err_en==0) begin
        `uvm_info(get_name(), $sformatf("ICDF Match for txn[%0d] addr: 0x%0x data: 0x%0x", counter, odr_item.addr, odr_item.data), UVM_MEDIUM)
      end
      counter += 1;
    end
    m_dpc_cmd_q.delete();
 end
endtask

task dmc_data_scoreboard:: wait_l1_data(dpc_cmd_t dpc_cmd, data_sb_axis_data_t exp_data, int indx, int size);
  data_sb_axis_data_t effective_exp_data;
  data_sb_axis_data_t backdoor_data;
  data_sb_axis_quarter_data_t data_list[L1_SUB_BANKS_PER_BANK];
  data_sb_mem_t mem_info;
  bit has_error =1;

  mem_info = m_mem.pop_front();
  if (mem_info.skip == 1) begin
    return; // skip does not necessarily mean data is invalid, it just mean that this is not the final address
  end
  case (mem_info.write_type)
    WRITE_INTRA_PAD: effective_exp_data = get_masked_data(.dpc_mask(0), .pad_val(dpc_cmd.dpc_intra_pad_val), .int16_not_int8(dpc_cmd.dpc_format), .raw_data(0));  // this is ODR case. we look at format.
    NORMAL_DATA: effective_exp_data = get_masked_data(.dpc_mask(dpc_cmd.dpc_msk), .pad_val(dpc_cmd.dpc_intra_pad_val), .int16_not_int8(dpc_cmd.dpc_format), .raw_data(exp_data));  // this is ODR case. we look at format.
    CASTED_DATA: effective_exp_data = exp_data;  // if it waas casted from int16 to int8, it's already masked.
    default:begin
      `uvm_info(get_name(), $sformatf("Expected Dropped Data! Addr: %0x Data: %0x Index: %0d", dpc_cmd.dpc_addr, exp_data, indx), UVM_MEDIUM)
      return; // when the data is dropped, it will not arrive into the memory, hence, skip the waiting for the data that will not arrive
    end
  endcase
  `uvm_info(get_name(), $sformatf("Wait for Data of 0x%0x for address 0x%0x index: %0d  at path0/1 %s after 1us. started!", effective_exp_data, dpc_cmd.dpc_addr, indx, m_mem_path_list[0]), UVM_MEDIUM)
  fork
    begin
      repeat (m_timeout_multiplier) #1us;
      if (m_odr_axi_err_en==0) begin
        `uvm_info(get_name(), $sformatf("mem_info.addr = 0x%0x Write Type: %s", mem_info.addr, mem_info.write_type.name()), UVM_LOW)
        `uvm_error(get_name(), $sformatf("\n Data of 0x%0x for address 0x%0x index: %0d did not arrive at path0/1 %s after 1us. Instead, data is: 0x%0x", effective_exp_data, dpc_cmd.dpc_addr, indx, m_mem_path_list[0], backdoor_data))
      end
    end
    begin
      do begin
        backdoor_data = hdl_read(dpc_cmd);
        #10ps;
      end while (backdoor_data != effective_exp_data);
      has_error = 0;
    end
  join_any
  disable fork;
  if (has_error==0 && m_odr_axi_err_en==0) begin
    `uvm_info(get_name(), $sformatf("Match for txn[%0d/%0d]\naddr: 0x%0x\ndata: 0x%0x", indx, size-1, dpc_cmd.dpc_addr, effective_exp_data), UVM_MEDIUM)
  end
endtask



task dmc_data_scoreboard::wait_tlast(int count =1);
  `uvm_info(get_name(), $sformatf("started waiting for count=%0d!",count), UVM_MEDIUM)
  fork
    begin
      wait (m_axis_tlast_count == count);
      `uvm_info(get_name(), $sformatf("received count=%0d!",count), UVM_MEDIUM)
    end
    begin
      #1ms;
      `uvm_fatal(get_name(), $sformatf("Timeout! Waiting for %0d TLAST did not happen! Current count: %0d", count, m_axis_tlast_count))
    end
  join_any
  disable fork;
endtask

`endif // _DMC_DATA_SCOREBOARD_SV

