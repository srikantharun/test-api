
`ifndef GUARD_AIC_LS_ENV_CFG_SV
`define GUARD_AIC_LS_ENV_CFG_SV

// AI CORE LS environment configuration class
class aic_ls_env_cfg extends uvm_object;

  `uvm_object_utils(aic_ls_env_cfg)

  typedef bit[AIC_LS_ENV_AXI_HP_ADDR_W-1:0]  hp_addr_t;
  typedef bit[AIC_LS_ENV_AXI_CFG_ADDR_W-1:0] cfg_addr_t;

  function new(string name = "aic_ls_env_cfg");
    super.new(name);
  endfunction : new

  rand int unsigned m_cid;
  rand int unsigned m_pword_size;
  rand int unsigned m_l1_num_banks;
  rand int unsigned m_l1_ram_array_size;
  rand int unsigned m_l1_ram_dw;
  rand int unsigned m_l1_ram_size_kbytes;
  rand hp_addr_t    m_cid_offset;
  rand hp_addr_t    m_l1_start_addr;
  rand hp_addr_t    m_l1_end_addr;
  rand hp_addr_t    m_l1_full_start_addr;
  rand hp_addr_t    m_l1_full_end_addr;
  rand cfg_addr_t   m_mem_base_addr[AIC_LS_ENV_DMC_NUM_DEVICE];
  rand cfg_addr_t   m_mem_base_addr_offset[AIC_LS_ENV_DMC_NUM_DEVICE];
  rand hp_addr_t    m_hp_mst_target_addr[AIC_LS_ENV_DMC_NUM_DEVICE];

  `ifdef AI_CORE_TOP_ENV_CHECK
  string m_l1_mem_root_path = AI_CORE_TOP_ENV_L1_MEM_ROOT_PATH;
  `else
  string m_l1_mem_root_path = AIC_LS_ENV_L1_MEM_ROOT_PATH;
  `endif

  constraint C_CID {
    soft m_cid >= 1;
    soft m_cid <= 1; // EUROPA: 8 cores, but inside AIC LS only ever sees itself as core_0, so CID=1
  }

  constraint C_CID_OFFSET {
    soft m_cid_offset == AIC_LS_ENV_CID_ADDR_OFFSET;
  }

  constraint C_L1_ADDRESS_START_AND_END {
    soft m_l1_start_addr == AIC_LS_ENV_L1_MEM_OFFSET+AIC_LS_ENV_L1_ADDR_START;
    soft m_l1_end_addr   == AIC_LS_ENV_L1_MEM_OFFSET+AIC_LS_ENV_L1_ADDR_END;
  }

  constraint C_L1_FULL_ADDRESS {
    soft m_l1_full_start_addr == (m_cid_offset * m_cid) + m_l1_start_addr;
    soft m_l1_full_end_addr   == (m_cid_offset * m_cid) + m_l1_end_addr;
  }

  constraint C_L1_MEMORY {
    soft m_l1_num_banks       == DEFAULT_L1_NUM_BANKS;
    soft m_l1_ram_array_size  == DATA_SB_L1_RAM_ARRAY_SIZE;
    soft m_l1_ram_dw          == DATA_SB_L1_RAM_DW;
    soft m_l1_ram_size_kbytes == DATA_SB_L1_RAM_ARRAY_SIZE * DATA_SB_L1_RAM_DW / 8;
  }

  constraint C_PWORD_SIZE {
    soft m_pword_size == aic_common_pkg::AIC_PWORD_SIZE;
  }

  constraint C_SOLVER {
    solve m_cid_offset, m_cid, m_l1_start_addr, m_l1_end_addr before m_l1_full_start_addr, m_l1_full_end_addr;
  }

  bit m_has_coverage   = 1;
  bit m_has_scoreboard = 1;


  function void post_randomize();
    super.post_randomize();
    `uvm_info(get_name(), convert2string(), UVM_LOW)
  endfunction

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n----------- AI CORE LS Configuration ----------------") };
    s = {s, $sformatf("\n m_cid                : %0d", m_cid) };
    s = {s, $sformatf("\n m_cid_offset         : 0x%0x", m_cid_offset) };
    s = {s, $sformatf("\n m_pword_size         : %0d", m_pword_size) };
    s = {s, $sformatf("\n m_l1_num_banks       : %0d", m_l1_num_banks) };
    s = {s, $sformatf("\n m_l1_ram_dw          : %0d", m_l1_ram_dw) };
    s = {s, $sformatf("\n m_l1_ram_size_kbytes : %0d", m_l1_ram_size_kbytes) };
    s = {s, $sformatf("\n m_l1_start_addr      : 0x%0x", m_l1_start_addr) };
    s = {s, $sformatf("\n m_l1_end_addr        : 0x%0x", m_l1_end_addr) };
    s = {s, $sformatf("\n m_l1_full_start_addr : 0x%0x", m_l1_full_start_addr) };
    s = {s, $sformatf("\n m_l1_full_end_addr   : 0x%0x", m_l1_full_end_addr) };
    s = {s, $sformatf("\n m_has_coverage   :  %0d", m_has_coverage) };
    s = {s, $sformatf("\n m_has_scoreboard :  %0d", m_has_scoreboard) };
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;
  endfunction : convert2string
endclass : aic_ls_env_cfg

`endif  // GUARD_AIC_LS_ENV_CFG_SV
