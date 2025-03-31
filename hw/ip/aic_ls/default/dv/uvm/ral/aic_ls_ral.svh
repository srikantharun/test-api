// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI CORE LS RAL.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

class aic_ls_ral#(int ADDR_W=36, int DATA_W=64) extends uvm_component;
    `uvm_component_param_utils(aic_ls_ral#(ADDR_W, DATA_W))

  typedef bit[ADDR_W-1:0] addr_t;
  typedef bit[DATA_W-1:0] data_t;

  // Register model Generic
  register_access #(uvm_reg_block, ADDR_W, DATA_W) m_reg_blocks[AIC_DMC_NUM_REGBLOCKS];
  aic_ls_subsys_reg_block                      m_regmodel;

  function new(string name="aic_ls_ral", uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (int i=0; i < AIC_DMC_NUM_REGBLOCKS; i++) begin
      m_reg_blocks[i] = new($sformatf("m_reg_blocks_%0d", i), this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if(!uvm_config_db#(aic_ls_subsys_reg_block)::get(this, "", "ls_regmodel", m_regmodel)) begin
      `uvm_fatal(get_name(), "Could not retrieve LS regmodel")
    end

    for (int i=0; i < AIC_DMC_NUM_REGBLOCKS; i++) begin
      m_reg_blocks[i].m_regmodel = m_regmodel.m_reg_blocks[i];
    end
  endfunction

  function void get_register(int regblock_num, string name = "", addr_t addr = 0, output uvm_reg curr_reg);
    uvm_reg     regs[$], local_reg;
    string      regname;

    regname  = name;

    if (name != "") begin
      local_reg = m_regmodel.m_reg_blocks[regblock_num].get_reg_by_name(regname);
    end else begin
      m_regmodel.m_reg_blocks[regblock_num].get_registers(regs);
      foreach(regs[i]) begin
        if (addr == regs[i].get_address()) begin
          local_reg = regs[i];
          break;
        end else begin
          local_reg = null;
        end
      end
    end
    curr_reg = local_reg;
    if (curr_reg==null) begin
      `uvm_fatal(get_name(), $sformatf("get_register(): register not found! address: 0x%0x name: %s", addr, name))
    end
    `uvm_info(get_name(), $sformatf("RAL access to register block %0d %s", regblock_num, regname), UVM_HIGH)
  endfunction

  task write_reg (int regblock_num,  data_t data, string name = "", string field = "", addr_t addr = 0);
    uvm_reg local_reg;
    get_register(.regblock_num(regblock_num), .name(name), .addr(addr), .curr_reg(local_reg));
    m_reg_blocks[regblock_num].write_reg(.data(data), .name(name), .addr(addr), .field(field), .path(UVM_FRONTDOOR));
  endtask

  task read_reg (int regblock_num, string name = "", string field = "", addr_t addr = 0, data_t exp_data = 0, bit compare=0, output data_t data);
    uvm_reg local_reg;
    get_register(.regblock_num(regblock_num), .name(name), .addr(addr), .curr_reg(local_reg));
    m_reg_blocks[regblock_num].read_reg(.name(name), .addr(addr), .field(field), .path(UVM_FRONTDOOR), .exp_data(exp_data), .compare(compare), .data(data));
  endtask
  
  task bkdr_write_reg (int regblock_num,  data_t data, string name = "", string field = "", addr_t addr = 0);
    uvm_reg local_reg;
    get_register(.regblock_num(regblock_num), .name(name), .addr(addr), .curr_reg(local_reg));
    m_reg_blocks[regblock_num].write_reg(.data(data), .name(name), .addr(addr), .field(field), .path(UVM_BACKDOOR));
  endtask

  task bkdr_read_reg (int regblock_num, string name = "", string field = "", addr_t addr = 0, data_t exp_data = 0, bit compare=0, output data_t data);
    uvm_reg local_reg;
    get_register(.regblock_num(regblock_num), .name(name), .addr(addr), .curr_reg(local_reg));
    m_reg_blocks[regblock_num].read_reg(.name(name), .addr(addr), .field(field), .path(UVM_BACKDOOR), .exp_data(exp_data), .compare(compare), .data(data));
  endtask

endclass
