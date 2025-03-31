`ifndef UVM_SW_IPC_IF_TOP_SV
`define UVM_SW_IPC_IF_TOP_SV

`define AIC_SPM_SRAM_WRITE(bank_index, minibank_index, sram_index, addr, data) \
    fork \
        hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[bank_index].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[minibank_index].u_spm_mem_mini_bank.g_sram_inst[sram_index].u_tc_sram.gen_macro.u_macro.u_mem.write_mem(addr, data); \
    join
`define AIC_SPM_SRAM_READ(bank_index, minibank_index, sram_index, addr, data) \
    fork \
        hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[bank_index].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[minibank_index].u_spm_mem_mini_bank.g_sram_inst[sram_index].u_tc_sram.gen_macro.u_macro.u_mem.read_mem(addr, data); \
    join

`define AIC_SPM_ACCESS_TYPE_CASE(bank_index, minibank_index, sram_index, rw, addr, data) \
    case(rw) \
        0: `AIC_SPM_SRAM_READ(bank_index, minibank_index, sram_index, addr, data) \
        1: `AIC_SPM_SRAM_WRITE(bank_index, minibank_index, sram_index, addr, data) \
        default: `uvm_fatal("AICORE_SW_IF", $sformatf("mem_access failed for rw: %0d", rw)) \
    endcase

`define AIC_SPM_SRAM_CASE(bank_index, minibank_index, sram_index, rw, addr, data) \
    case(sram_index) \
        0: `AIC_SPM_ACCESS_TYPE_CASE(bank_index, minibank_index, 0, rw, addr, data) \
        1: `AIC_SPM_ACCESS_TYPE_CASE(bank_index, minibank_index, 1, rw, addr, data) \
        default: `uvm_fatal("AICORE_SW_IF", $sformatf("mem_access failed for sram_index: %0d", sram_index)) \
    endcase

`define AIC_SPM_MINIBANK_CASE(bank_index, minibank_index, sram_index, rw, addr, data) \
    case(minibank_index) \
        0: `AIC_SPM_SRAM_CASE(bank_index, 0, sram_index, rw, addr, data) \
        1: `AIC_SPM_SRAM_CASE(bank_index, 1, sram_index, rw, addr, data) \
        default: `uvm_fatal("AICORE_SW_IF", $sformatf("mem_access failed for minibank_index: %0d", minibank_index)) \
    endcase

`define AIC_SPM_CASE(bank_index, minibank_index, sram_index, rw, addr, data) \
    case (bank_index) \
        0: `AIC_SPM_MINIBANK_CASE(0, minibank_index, sram_index, rw, addr, data) \
        1: `AIC_SPM_MINIBANK_CASE(1, minibank_index, sram_index, rw, addr, data) \
        default: `uvm_fatal("AICORE_SW_IF", $sformatf("mem_access failed for bank_index: %0d", bank_index)) \
    endcase



`define AIC_L1_SRAM_WRITE(subbank_index, minibank_index, addr, data) \
    fork \
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[subbank_index].u_sub_bank.g_mini_bank[minibank_index].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.write_mem(addr, data); \
    join
`define AIC_L1_SRAM_READ(subbank_index, minibank_index, addr, data) \
    fork \
        hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[subbank_index].u_sub_bank.g_mini_bank[minibank_index].u_mini_bank.g_macro[0].u_macro.gen_macro.u_macro.u_mem.read_mem(addr, data); \
    join

`define AIC_L1_ACCESS_TYPE_CASE(subbank_index, minibank_index, rw, addr, data) \
    case(rw) \
        0: `AIC_L1_SRAM_READ(subbank_index, minibank_index, addr, data) \
        1: `AIC_L1_SRAM_WRITE(subbank_index, minibank_index, addr, data) \
        default: `uvm_fatal("AICORE_SW_IF", $sformatf("mem_access failed for rw: %0d", rw)) \
    endcase

`define AIC_L1_MINIBANK_CASE(subbank_index, minibank_index, rw, addr, data) \
    case(minibank_index) \
        0: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 0, rw, addr, data) \
        1: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 1, rw, addr, data) \
        2: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 2, rw, addr, data) \
        3: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 3, rw, addr, data) \
        4: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 4, rw, addr, data) \
        5: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 5, rw, addr, data) \
        6: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 6, rw, addr, data) \
        7: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 7, rw, addr, data) \
        8: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 8, rw, addr, data) \
        9: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 9, rw, addr, data) \
        10: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 10, rw, addr, data) \
        11: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 11, rw, addr, data) \
        12: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 12, rw, addr, data) \
        13: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 13, rw, addr, data) \
        14: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 14, rw, addr, data) \
        15: `AIC_L1_ACCESS_TYPE_CASE(subbank_index, 15, rw, addr, data) \
        default: `uvm_fatal("AICORE_SW_IF", $sformatf("mem_access failed for minibank_index: %0d", minibank_index)) \
    endcase

`define AIC_L1_CASE(subbank_index, minibank_index, rw, addr, data) \
    case (subbank_index) \
        0: `AIC_L1_MINIBANK_CASE(0, minibank_index, rw, addr, data) \
        1: `AIC_L1_MINIBANK_CASE(1, minibank_index, rw, addr, data) \
        2: `AIC_L1_MINIBANK_CASE(2, minibank_index, rw, addr, data) \
        3: `AIC_L1_MINIBANK_CASE(3, minibank_index, rw, addr, data) \
        default: `uvm_fatal("AICORE_SW_IF", $sformatf("mem_access failed for subbank_index: %0d", subbank_index)) \
    endcase




interface uvm_sw_ipc_if ();
  timeunit 1ns; timeprecision 1ps;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import uvm_sw_ipc_pkg::*;


  wire clock;
  wire reset;
  wire cen;
  wire wen;
  wire [63:0] address;
  wire [63:0] rdata;
  wire [63:0] wdata;
  wire [7:0] byteen;


  clocking cb @(posedge clock);
    input reset;
    input cen;
    input wen;
    input address;
    input rdata;
    input wdata;
    input byteen;
  endclocking : cb

    typedef struct {
        int sb_idx;
        int mb_idx;
        bit msb_half;
        bit [11:0] addr;
    } aic_l1_indexes_t;
  //---------------------------------------------------------
  // functions
  //---------------------------------------------------------
  parameter logic [35:0] SYS_SPM_MEM_ST_ADDR  = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
  parameter logic [35:0] SYS_SPM_MEM_END_ADDR = aipu_addr_map_pkg::SYS_SPM_END_ADDR;
  parameter logic [63:0] AICORE0_SPM_ST_ADDR  = aipu_addr_map_pkg::AICORE_0_SPM_ST_ADDR;
  parameter logic [63:0] AICORE0_SPM_END_ADDR = aipu_addr_map_pkg::AICORE_0_SPM_END_ADDR;
  parameter logic [63:0] AICORE0_L1_ST_ADDR   = aipu_addr_map_pkg::AICORE_0_L1_ST_ADDR;
  parameter logic [63:0] AICORE0_L1_END_ADDR  = aipu_addr_map_pkg::AICORE_0_L1_END_ADDR;

  function static aic_l1_indexes_t get_l1_mem_idx(bit [63:0] addr);
    aic_l1_indexes_t l1_idxs;
    bit [63:0] temp;
    // removing base address
    temp = (addr - AICORE0_L1_ST_ADDR);

    // The addrs is composed like following:
    // [21:10] cell line address
    // [9:6] minibank sel
    // [5:4] subbank sel
    // [3:0] byte addressing inside the 128bline


    //if the address is in the first 64 or in the second 64 bits
    l1_idxs.msb_half = temp[3];

    // address used to define the line in the cell
    l1_idxs.addr = temp[21:10];

    // minib idx, 16 minibaks
    l1_idxs.mb_idx = temp[9:6];

    // bank idx, 4 banks
    l1_idxs.sb_idx = temp[5:4];

    return l1_idxs;
  endfunction : get_l1_mem_idx


  function static void backdoor_write(bit [63:0] addr, bit [63:0] wdata);
    spm_indexes_t spm_idxs;
    aic_l1_indexes_t l1_idxs;
    logic [127:0] rdata_l1, wdata_l1;
    logic [71:0] wdata_spm_w_ecc;
    bit rw;
    if ((addr >= AICORE0_SPM_ST_ADDR) && (addr <= AICORE0_SPM_END_ADDR)) begin
        // get indexes
        spm_idxs = get_aic_spm_mem_idx(addr);
        // add the ECC
        wdata_spm_w_ecc = add_spm_ecc(wdata);
        // write the value
        rw = 1;
`ifdef TARGET_SF5A
        `AIC_SPM_CASE(spm_idxs.b_idx, spm_idxs.mb_idx, spm_idxs.sr_idx, rw, spm_idxs.addr, wdata_spm_w_ecc)
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[%0d].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[%0d].u_spm_mem_mini_bank.g_sram_inst[%0d].u_tc_sram.memory_q[%0d]", spm_idxs.b_idx, spm_idxs.mb_idx, spm_idxs.sr_idx, spm_idxs.addr), wdata_spm_w_ecc);
`endif
    end
    else if ((addr >= SYS_SPM_MEM_ST_ADDR) && (addr <= SYS_SPM_MEM_END_ADDR)) begin
`ifndef DV_AXI_RAM_UNBOUNDED
        uvm_hdl_deposit($sformatf("hdl_top.i_fake_sys_spm.mem[%0d]",addr[39:0] >> 3), wdata);
`else
  automatic integer unsigned idx = addr[39:0] >> 3;
  i_fake_sys_spm.mem[idx] = wdata;
`endif
    end
    else if ((addr >= AICORE0_L1_ST_ADDR) && (addr <= AICORE0_L1_END_ADDR)) begin
        // get indexes
        l1_idxs = get_l1_mem_idx(addr);
        // read the value
        rw = 0;
`ifdef TARGET_SF5A
        `AIC_L1_CASE(l1_idxs.sb_idx, l1_idxs.mb_idx, rw, l1_idxs.addr, rdata_l1)
`else
        uvm_hdl_read($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", l1_idxs.sb_idx, l1_idxs.mb_idx, l1_idxs.addr), rdata_l1);
`endif
        wdata_l1 = rdata_l1;
        if(l1_idxs.msb_half) begin
            wdata_l1[127:64] = wdata;
        end else begin
            wdata_l1[63:0] = wdata;
        end
        // write the value
        rw = 1;
`ifdef TARGET_SF5A
        `AIC_L1_CASE(l1_idxs.sb_idx, l1_idxs.mb_idx, rw, l1_idxs.addr, wdata_l1)
`else
        uvm_hdl_deposit($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", l1_idxs.sb_idx, l1_idxs.mb_idx, l1_idxs.addr), wdata_l1);
`endif
    end
    `uvm_info("backdoor_write", $sformatf("0x%x -> [0x%x]", wdata, addr), UVM_DEBUG);
  endfunction : backdoor_write


  function static void backdoor_read(bit [63:0] addr, output bit [63:0] rdata);
    spm_indexes_t spm_idxs;
    aic_l1_indexes_t l1_idxs;
    logic [127:0] rdata_l1;
    bit rw;
    if ((addr >= AICORE0_SPM_ST_ADDR) && (addr <= AICORE0_SPM_END_ADDR)) begin
        // get indexes
        spm_idxs = get_aic_spm_mem_idx(addr);
        // read the value
        rw = 0;
`ifdef TARGET_SF5A
        `AIC_SPM_CASE(spm_idxs.b_idx, spm_idxs.mb_idx, spm_idxs.sr_idx, rw, spm_idxs.addr, rdata)
`else
        uvm_hdl_read($sformatf("hdl_top.dut.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[%0d].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[%0d].u_spm_mem_mini_bank.g_sram_inst[%0d].u_tc_sram.memory_q[%0d]", spm_idxs.b_idx, spm_idxs.mb_idx, spm_idxs.sr_idx, spm_idxs.addr), rdata);
`endif
    end
    else if ((addr >= SYS_SPM_MEM_ST_ADDR) && (addr <= SYS_SPM_MEM_END_ADDR)) begin
`ifndef DV_AXI_RAM_UNBOUNDED
        uvm_hdl_read($sformatf("hdl_top.i_fake_sys_spm.mem[%0d]",addr[39:0] >> 3), rdata);
`else
        automatic integer unsigned idx = addr[39:0] >> 3;
        rdata = i_fake_sys_spm.mem[idx];
`endif
    end
    else if ((addr >= AICORE0_L1_ST_ADDR) && (addr <= AICORE0_L1_END_ADDR)) begin
        // get indexes
        l1_idxs = get_l1_mem_idx(addr);
        // read the value
        rw = 0;
`ifdef TARGET_SF5A
        `AIC_L1_CASE(l1_idxs.sb_idx, l1_idxs.mb_idx, rw, l1_idxs.addr, rdata_l1)
`else
        uvm_hdl_read($sformatf("hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", l1_idxs.sb_idx, l1_idxs.mb_idx, l1_idxs.addr), rdata_l1);
`endif
        if(l1_idxs.msb_half) begin
            rdata = rdata_l1[127:64];
        end else begin
            rdata = rdata_l1[63:0];
        end
    end
    `uvm_info("backdoor_read", $sformatf("0x%x <- [0x%x]", rdata, addr), UVM_DEBUG);
  endfunction : backdoor_read




  function static string backdoor_get_string(bit [63:0] addr, int length = -1);
    string str;
    bit [7:0] char;
    int i;

    str = "";
    char = ".";
    i = 0;
    while (char != 0 && i != length) begin
      bit [63:0] rdata;
      int char_idx;
      char_idx = (i + addr) % 8;
      if (i == 0 || char_idx == 0) begin
        backdoor_read(addr + i, rdata);
      end
      char = rdata[char_idx*8+:8];
      str  = {str, string'(char)};
      i++;
    end

    return str;
  endfunction : backdoor_get_string


endinterface : uvm_sw_ipc_if

`endif  // UVM_SW_IPC_IF_TOP_SV
