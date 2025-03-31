
/**
 * Abstract:
 * This file defines a class that represents a customized AXI Master
 * transaction.  This class extends the AXI VIP's svt_axi_master_transaction
 * class.  It adds pre-defined distribution constraints for transaction
 * weighting, and adds constraints.
 */
`ifndef GUARD_CUST_SVT_LP_AXI_MASTER_READ_TRANSACTION_SV
`define GUARD_CUST_SVT_LP_AXI_MASTER_READ_TRANSACTION_SV

class cust_svt_lp_axi_master_read_transaction extends svt_axi_master_transaction;
  `uvm_object_utils(cust_svt_lp_axi_master_read_transaction)

  static bit m_is_rd_not_wr;

  typedef enum bit[3:0] { 
    AXI_ADDR_MIFD0,
    AXI_ADDR_MIFD1,
    AXI_ADDR_MIFD2,
    AXI_ADDR_MIFDW,
    AXI_ADDR_MODR,
    AXI_ADDR_DIFD0,
    AXI_ADDR_DIFD1,
    AXI_ADDR_DODR
  } aic_ls_axi_addr_enum_t;

  rand aic_ls_axi_addr_enum_t m_addr_type;

  int burst_type_fixed_wt = 33;
  int burst_type_incr_wt  = 34;
  int burst_type_wrap_wt  = 33;
  aic_ls_env m_env_h;
  
  bit[27:0] m_valid_addresses[8][$];

  constraint C_ADDRESS_DEV {
    soft addr[2:0] == 0; // 8 bytes aligned
    soft addr[15:12] != 4'h1; // Avoid Command block
    (m_addr_type == AXI_ADDR_MIFD0)   -> soft addr inside {m_valid_addresses[0]};
    (m_addr_type == AXI_ADDR_MIFD1)   -> soft addr inside {m_valid_addresses[1]};
    (m_addr_type == AXI_ADDR_MIFD2)   -> soft addr inside {m_valid_addresses[2]};
    (m_addr_type == AXI_ADDR_MIFDW)   -> soft addr inside {m_valid_addresses[3]};
    (m_addr_type == AXI_ADDR_MODR)    -> soft addr inside {m_valid_addresses[4]};
    (m_addr_type == AXI_ADDR_DIFD0)   -> soft addr inside {m_valid_addresses[5]};
    (m_addr_type == AXI_ADDR_DIFD1)   -> soft addr inside {m_valid_addresses[6]};
    (m_addr_type == AXI_ADDR_DODR)    -> soft addr inside {m_valid_addresses[7]};
  }

  constraint C_TXN_DIRECTION {
    (m_is_rd_not_wr) -> soft xact_type == READ;
    (!m_is_rd_not_wr) -> soft xact_type == WRITE;
  }

  constraint C_BURST_TYPE {
    soft burst_type dist {
      svt_axi_transaction::FIXED := burst_type_fixed_wt,
      svt_axi_transaction::INCR  := burst_type_incr_wt,
      svt_axi_transaction::WRAP  := burst_type_wrap_wt
    };
  }

  constraint C_BURST_SIZE {
    soft burst_size dist  { BURST_SIZE_8BIT:=10, BURST_SIZE_16BIT:=20, BURST_SIZE_32BIT:=30, BURST_SIZE_64BIT:=40};
  }

  constraint C_ATOMIC {
    soft atomic_type dist  { NORMAL:=80, EXCLUSIVE:=10, LOCKED:=10};
  }

  constraint C_DEFAULT_WDATA {
    (!m_is_rd_not_wr) -> foreach (data[i]) {
      soft data[i] == 0;
    }
  }

  constraint C_RREADY_DELAY {
    foreach (rready_delay[i]) {
      soft rready_delay[i] == 0; // min latency
    }
  }

  constraint C_SOLVER {
    solve m_addr_type before addr;
  }

  function new(string name = "cust_svt_lp_axi_master_read_transaction");
    super.new(name);
  endfunction : new

  function void pre_randomize();
    uvm_reg reg_list[$];
    super.pre_randomize();
    if (!uvm_config_db #(aic_ls_env)::get(null, "", "AIC_LS_ENV", m_env_h)) begin
        `uvm_fatal(get_name(), "Unable to get ENV AIC_LS_ENV")
    end
    m_env_h.m_ls_regmodel.get_registers(reg_list);
    foreach (reg_list[i]) begin
      `uvm_info(get_name(), $sformatf("REG LIST: Reg[%0d] %s Addr: 0x%0x", i, reg_list[i].get_full_name(), reg_list[i].get_address()), UVM_NONE)
      case (reg_list[i].get_address()) inside 
        [28'h200_0000:28'h200_FFFF]: m_valid_addresses[0].push_back(reg_list[i].get_address());
        [28'h201_0000:28'h201_FFFF]: m_valid_addresses[0].push_back(reg_list[i].get_address());
        [28'h202_0000:28'h202_FFFF]: m_valid_addresses[1].push_back(reg_list[i].get_address());
        [28'h203_0000:28'h203_FFFF]: m_valid_addresses[2].push_back(reg_list[i].get_address());
        [28'h204_0000:28'h204_FFFF]: m_valid_addresses[3].push_back(reg_list[i].get_address());
        [28'h205_0000:28'h205_FFFF]: m_valid_addresses[4].push_back(reg_list[i].get_address());
        [28'h206_0000:28'h206_FFFF]: m_valid_addresses[5].push_back(reg_list[i].get_address());
        [28'h207_0000:28'h207_FFFF]: m_valid_addresses[6].push_back(reg_list[i].get_address());
      endcase
    end
  endfunction

  function void post_randomize();
    super.post_randomize();
    `uvm_info(get_name(), $sformatf("%s", convert2string()), UVM_LOW)
  endfunction

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n----------- AXI LP TXN ITEM ----------------") };
    s = {s, $sformatf("\n Address Type      : %s",    m_addr_type.name())};
    s = {s, $sformatf("\n Address           : 0x%0x", addr)};
    s = {s, $sformatf("\n Transation Type   : %s", xact_type.name())};
    s = {s, $sformatf("\n Burst Type        : %s", burst_type)};
    s = {s, $sformatf("\n Burst Length      : %0d", burst_length)};
    s = {s, $sformatf("\n Burst Size        : %s", burst_size.name())};
    s = {s, $sformatf("\n Atomic Type       : %s", atomic_type.name())};
    s = {s, $sformatf("\n Cache             : %0d", cache_type)};
    return s;
  endfunction

endclass : cust_svt_lp_axi_master_read_transaction

`endif  // GUARD_CUST_SVT_LP_AXI_MASTER_READ_TRANSACTION_SV
