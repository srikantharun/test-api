`ifndef MMIO_SCOREBOARD_SV
`define MMIO_SCOREBOARD_SV

// Simple scoreboard. compare reads/writes to what's actually happening in l1
class mmio_scoreboard#(int DATA_WIDTH = 128, int ADDR_WIDTH = 22) extends uvm_scoreboard;
  // Registration with the factory
  `uvm_component_param_utils(mmio_scoreboard#(DATA_WIDTH, ADDR_WIDTH))

  typedef mmio_item#(DATA_WIDTH, ADDR_WIDTH) mmio_item_t;
  typedef bit[ADDR_WIDTH-1:0]  m_addr_t;
  typedef bit[DATA_WIDTH-1:0]   data_sb_data_t;

  uvm_tlm_analysis_fifo#(mmio_item_t) mmio_item_tfifo;
  string                          m_mem_path;
  int unsigned                    banks_num;
  int unsigned                    sub_banks_num;
  string                          m_memory_path;
  data_sb_data_t                  backdoor_data;
  mmio_config                     m_cfg;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mmio_item_tfifo   = new ("mmio_item_tfifo", this);

    if ( ! uvm_config_db#( mmio_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "m_cfg" ), .value( m_cfg ) ) ) begin
      `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
    end
    banks_num = m_cfg.banks_num;
    sub_banks_num = m_cfg.sub_banks_num;
    m_memory_path = m_cfg.m_memory_path;
  endfunction: build_phase

  function l1_quarter_data_t hdl_read(m_addr_t addr);
    /* performs the write of one value to the memory. it does that by reading the whole cell, replacing the relevant bits, and then writing back */
    int index, offset, m_bank, s_bank, sram_index, sram_mux_l, sram_mux_r;
    string mem_location;
    l1_phys_data_t data_phys;
    l1_half_data_t data_l, data_r;
    l1_quarter_data_t backdoor_data;
    int addr_size = DATA_WIDTH/8;

    index = addr/addr_size;
    s_bank = index%sub_banks_num;
    index = index/sub_banks_num;
    m_bank = index%banks_num;
    offset = index/banks_num;
    sram_index = offset/AIC_LS_ENV_L1_SRAM_MUX;
    sram_mux_r = offset%AIC_LS_ENV_L1_SRAM_MUX;
    sram_mux_l = (AIC_LS_ENV_L1_SRAM_MUX-1)-sram_mux_r;

    `ifndef TARGET_DFT
      mem_location = $sformatf("%s.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.mem[%0d]", m_memory_path, s_bank, m_bank, sram_index);
    `else
      mem_location = $sformatf("%s.\\g_sbank[%0d].u_sub_bank .\\g_mini_bank[%0d].u_mini_bank .\\g_macro[0].u_macro .u_macro .\\gen_inst.i_sramspehd.u_mem.mem[%0d]", m_memory_path, s_bank, m_bank, sram_index);
    `endif

    if (!uvm_hdl_read(mem_location, data_phys)) begin
      `uvm_fatal(get_name(), $sformatf("Failed to read HDL path! %s", mem_location))
    end
    
    data_r = data_phys[AIC_LS_ENV_L1_SRAM_FULL_SIZE-1:(AIC_LS_ENV_L1_BANK_DATA_WIDTH/2)+(AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS*2)];	// WO redundancy bits - 256+8...512+8
    data_l = data_phys[AIC_LS_ENV_L1_BANK_DATA_WIDTH/2-1:0];

    `uvm_info(get_name(), $sformatf("Read data from %s:\nfull data: 0x%0x\nright: 0x%0x, left: 0x%0x", mem_location, data_phys, data_r, data_l), UVM_MEDIUM)

    for(int j=0; j<AIC_LS_ENV_L1_SRAM_WORD_SIZE/2; j++) begin	 // we ran from 0 to 63, filling both the lower and upper half in parallel. this is following the SRAM definitions
      backdoor_data[j] = data_l[(j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_l];
      backdoor_data[j+AIC_LS_ENV_L1_SRAM_WORD_SIZE/2] = data_r[(j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_r];
      `uvm_info(get_name(), $sformatf("More debug: backdoor_data[%0d] = temp_data_l[%0d]", j+(s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE), (j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_l), UVM_HIGH)
      `uvm_info(get_name(), $sformatf("More debug: backdoor_data[%0d] = temp_data_r[%0d]", j+AIC_LS_ENV_L1_SRAM_WORD_SIZE/2+(s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE), (j*AIC_LS_ENV_L1_SRAM_MUX) + sram_mux_r), UVM_HIGH)
    end
    `uvm_info(get_name(), $sformatf("More debug: backdoor_data for this iteration: 0x%x", backdoor_data[s_bank*AIC_LS_ENV_L1_SRAM_WORD_SIZE +: AIC_LS_ENV_L1_SRAM_WORD_SIZE]), UVM_MEDIUM)
    return backdoor_data;
  endfunction: hdl_read

  virtual task run_phase(uvm_phase phase);
    mmio_item_t     mon_item;
    data_sb_data_t  exp_data;
    int index;
    time test_timeout;

    if (!uvm_config_db#(time)::get(null, "", "TEST_TIMEOUT", test_timeout)) begin
      `uvm_info(get_name(), "Unable to get TEST_TIMEOUT from config db, setting 1ms!", UVM_LOW)
      test_timeout = 1ms;
    end

    super.run_phase(phase);
    fork
      forever begin
        mmio_item_tfifo.get(mon_item);
        `uvm_info(get_name, $sformatf("Got mon_item: %s", mon_item.convert2string()), UVM_HIGH)
        #10ps;
        backdoor_data=hdl_read(mon_item.m_addr);

        if (mon_item.m_we==1) begin
          exp_data = mon_item.m_wdata;
        end else begin
          exp_data = mon_item.m_rdata;
        end
        if (exp_data != backdoor_data) begin
          `uvm_error(get_name, $sformatf("Mismatch between mmio data and memory!\naddress: 0x%x\nexp: 0x%x\nact: 0x%x", mon_item.m_addr, exp_data, backdoor_data))
        end else begin
          `uvm_info(get_name, $sformatf("Match between mmio data and memory, for address 0x%x", mon_item.m_addr), UVM_MEDIUM)
        end
      end
      begin
        #test_timeout;
        `uvm_fatal(get_name(), $sformatf("Timeout! Waited to long for the test to end."))
      end
    join_any
    disable fork;
  endtask : run_phase
endclass
`endif // MMIO_SCOREBOARD_SV

