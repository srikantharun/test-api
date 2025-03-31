`ifndef UVM_SW_IPC_IF_TOP_SV
`define UVM_SW_IPC_IF_TOP_SV

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


  //---------------------------------------------------------
  // functions
  //---------------------------------------------------------
`define gen_addr_params(mem_name) \
  parameter logic [63:0] ``mem_name``_ST_ADDR = aipu_addr_map_pkg::``mem_name``_ST_ADDR; \
  parameter logic [63:0] ``mem_name``_END_ADDR = aipu_addr_map_pkg::``mem_name``_END_ADDR

`define gen_err_msg(access_type, mem_name) \
  `uvm_fatal(`"access_type`", $sformatf("Failed to access %s, are you sure it hasn't been stubbed?", `"mem_name`"))

  `gen_addr_params(SYS_SPM);
  `gen_addr_params(AICORE_0_SPM);
  `gen_addr_params(AICORE_1_SPM);
  `gen_addr_params(AICORE_2_SPM);
  `gen_addr_params(AICORE_3_SPM);
  `gen_addr_params(AICORE_4_SPM);
  `gen_addr_params(AICORE_5_SPM);
  `gen_addr_params(AICORE_6_SPM);
  `gen_addr_params(AICORE_7_SPM);
  `gen_addr_params(PVE_0_SPM);
  `gen_addr_params(PVE_1_SPM);
  `gen_addr_params(AICORE_0_L1);
  `gen_addr_params(AICORE_1_L1);
  `gen_addr_params(AICORE_2_L1);
  `gen_addr_params(AICORE_3_L1);
  `gen_addr_params(AICORE_4_L1);
  `gen_addr_params(AICORE_5_L1);
  `gen_addr_params(AICORE_6_L1);
  `gen_addr_params(AICORE_7_L1);
  parameter logic [63:0] DDR_1_MEM_ST_ADDR = aipu_addr_map_pkg::DDR_1_ST_ADDR;
  parameter logic [63:0] DDR_1_MEM_END_ADDR = aipu_addr_map_pkg::DDR_1_END_ADDR;
  parameter logic [63:0] DDR_0_MEM_ST_ADDR = aipu_addr_map_pkg::DDR_0_ST_ADDR;
  parameter logic [63:0] DDR_0_MEM_END_ADDR = aipu_addr_map_pkg::DDR_0_END_ADDR;

  function static bit [255:0] lpddr_backdoor_read(bit [63:0] word_addr);
    bit [63:0] relative_word_addr;
    //TODO: support interleaving modes
    int ddr_idx;
    ddr_idx = word_addr[29:28];
    if(word_addr >= (DDR_0_MEM_ST_ADDR >> 5) && word_addr <= (DDR_0_MEM_END_ADDR >> 5)) begin
      relative_word_addr = word_addr - (DDR_0_MEM_ST_ADDR >> 5);
      case (ddr_idx)
        2'd0:
          `ifdef LPDDR_P_GRAPH_0_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
        2'd1:
          `ifdef LPDDR_P_GRAPH_1_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_1.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
        2'd2:
          `ifdef LPDDR_P_GRAPH_2_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_2.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
        2'd3:
          `ifdef LPDDR_P_GRAPH_3_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_3.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
        default:
          `ifdef LPDDR_P_GRAPH_0_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
      endcase
    end
    else if(word_addr >= (DDR_1_MEM_ST_ADDR >> 5) && word_addr <= (DDR_1_MEM_END_ADDR >> 5)) begin
      relative_word_addr = word_addr - (DDR_1_MEM_ST_ADDR >> 5);
      case (ddr_idx)
        2'd0:
          `ifdef LPDDR_P_PPP_0_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_0.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
        2'd1:
          `ifdef LPDDR_P_PPP_1_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_1.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
        2'd2:
          `ifdef LPDDR_P_PPP_2_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_2.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
        2'd3:
          `ifdef LPDDR_P_PPP_3_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_3.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
        default:
          `ifdef LPDDR_P_PPP_0_STUB
            return i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_0.i_fake_lpddr.mem[relative_word_addr];
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", word_addr<<5))
          `endif
      endcase
    end
    else begin
      `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is outside DDR_0 and DDR_1 ranges", word_addr<<5))
    end
  endfunction : lpddr_backdoor_read

  function static void lpddr_backdoor_write(bit [63:0] word_addr, bit [255:0] wdata_256);
    bit [63:0] relative_word_addr;
    //TODO: support interleaving modes
    int ddr_idx;
    ddr_idx = word_addr[29:28];
    if(word_addr >= (DDR_0_MEM_ST_ADDR >> 5) && word_addr <= (DDR_0_MEM_END_ADDR >> 5)) begin
      relative_word_addr = word_addr - (DDR_0_MEM_ST_ADDR >> 5);
      case (ddr_idx)
        2'd0:
          `ifdef LPDDR_P_GRAPH_0_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
        2'd1:
          `ifdef LPDDR_P_GRAPH_1_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_1.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
        2'd2:
          `ifdef LPDDR_P_GRAPH_2_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_2.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
        2'd3:
          `ifdef LPDDR_P_GRAPH_3_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_3.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
        default:
          `ifdef LPDDR_P_GRAPH_0_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
      endcase
    end
    else if(word_addr >= (DDR_1_MEM_ST_ADDR >> 5) && word_addr <= (DDR_1_MEM_END_ADDR >> 5)) begin
      relative_word_addr = word_addr - (DDR_1_MEM_ST_ADDR >> 5);
      case (ddr_idx)
        2'd0:
          `ifdef LPDDR_P_PPP_0_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_0.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
        2'd1:
          `ifdef LPDDR_P_PPP_1_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_1.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
        2'd2:
          `ifdef LPDDR_P_PPP_2_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_2.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
        2'd3:
          `ifdef LPDDR_P_PPP_3_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_3.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
        default:
          `ifdef LPDDR_P_PPP_0_STUB
            i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_0.i_fake_lpddr.mem[relative_word_addr] = wdata_256;
          `else
            `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet (real lpddr backdoor not yet supported)", word_addr<<5))
          `endif
      endcase
    end
    else begin
      `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is outside DDR_0 and DDR_1 ranges", word_addr<<5))
    end
  endfunction : lpddr_backdoor_write

  function static string get_sys_spm_mem_path(bit [63:0] addr);
    spm_indexes_t spm_idxs;

    spm_idxs = get_sys_spm_mem_idx(addr);

    return $sformatf("i_hdl_top.i_europa.u_aipu.u_sys_spm_p.u_sys_spm.u_spm.u_spm_mem.g_bank_inst[%0d].u_spm_mem_bank.g_sub_bank_inst[%0d].u_spm_mem_sub_bank.g_mini_bank_inst[%0d].u_spm_mem_mini_bank.g_sram_inst[%0d].u_tc_sram.memory_q[%0d]",
      spm_idxs.b_idx, spm_idxs.sb_idx, spm_idxs.mb_idx, spm_idxs.sr_idx, spm_idxs.addr);
  endfunction : get_sys_spm_mem_path

  function static string get_aicore_spm_mem_path(int aicore_idx, bit [63:0] addr);
    spm_indexes_t spm_idxs;

    spm_idxs = get_aic_spm_mem_idx(addr);
    return $sformatf("i_hdl_top.i_europa.u_aipu.u_ai_core_p_%0d.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm.u_spm_mem.g_bank_inst[%0d].u_spm_mem_bank.g_sub_bank_inst[0].u_spm_mem_sub_bank.g_mini_bank_inst[%0d].u_spm_mem_mini_bank.g_sram_inst[%0d].u_tc_sram.memory_q[%0d]", aicore_idx, spm_idxs.b_idx, spm_idxs.mb_idx, spm_idxs.sr_idx, spm_idxs.addr);
  endfunction : get_aicore_spm_mem_path

  function static string get_pve_spm_mem_path(int pve_idx, bit [63:0] addr);
    spm_indexes_t spm_idxs;

    spm_idxs = get_pve_spm_mem_idx(addr);
    return $sformatf("i_hdl_top.i_europa.u_aipu.u_pve_p_%0d.u_pve.u_spm.u_spm_mem.g_bank_inst[%0d].u_spm_mem_bank.g_sub_bank_inst[%0d].u_spm_mem_sub_bank.g_mini_bank_inst[%0d].u_spm_mem_mini_bank.g_sram_inst[%0d].u_tc_sram.memory_q[%0d]", pve_idx, spm_idxs.b_idx, spm_idxs.sb_idx, spm_idxs.mb_idx, spm_idxs.sr_idx, spm_idxs.addr);
  endfunction : get_pve_spm_mem_path

  function static string aic_l1_mem_path_hdl_read(int aicore_idx, bit [63:0] addr, output bit [63:0] rdata);
    aic_l1_indexes_t l1_idxs;
    logic [127:0] rdata_l1;
    // get indexes
    l1_idxs = get_l1_mem_idx(addr);

    assert (uvm_hdl_read($sformatf("i_hdl_top.i_europa.u_aipu.u_ai_core_p_%0d.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]",aicore_idx ,l1_idxs.sb_idx, l1_idxs.mb_idx, l1_idxs.addr), rdata_l1)) else `uvm_error("backdoor_read",$sformatf("ai_core_%0d",aicore_idx));

    if(l1_idxs.msb_half) begin
            rdata = rdata_l1[127:64];
    end else begin
            rdata = rdata_l1[63:0];
    end
    `uvm_info("backdoor_read l1 aicore", $sformatf("0x%x <- [0x%x]", rdata, addr), UVM_DEBUG);
  endfunction : aic_l1_mem_path_hdl_read

  function static string aic_l1_mem_path_hdl_deposit(int aicore_idx, bit [63:0] addr, bit [63:0] wdata);
    logic [127:0] rdata_l1, wdata_l1;
    bit rw;

    aic_l1_indexes_t l1_idxs;
    // get indexes
    l1_idxs = get_l1_mem_idx(addr);
    // read the value
    rw = 0;
    uvm_hdl_read($sformatf("i_hdl_top.i_europa.u_aipu.u_ai_core_p_%0d.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]",aicore_idx, l1_idxs.sb_idx, l1_idxs.mb_idx, l1_idxs.addr), rdata_l1);
    wdata_l1 = rdata_l1;
    if(l1_idxs.msb_half) begin
        wdata_l1[127:64] = wdata;
    end else begin
        wdata_l1[63:0] = wdata;
    end
    // write the value
    rw = 1;
    assert (uvm_hdl_deposit($sformatf("i_hdl_top.i_europa.u_aipu.u_ai_core_p_%0d.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem.g_sbank[%0d].u_sub_bank.g_mini_bank[%0d].u_mini_bank.g_macro[0].u_macro.memory_q[%0d]", aicore_idx, l1_idxs.sb_idx, l1_idxs.mb_idx, l1_idxs.addr), wdata_l1))else `uvm_error("backdoor_read",$sformatf("ai_core_%0d",aicore_idx));
  endfunction : aic_l1_mem_path_hdl_deposit


  function static void backdoor_write(bit [63:0] addr, bit [63:0] wdata);
    bit [63:0] relative_addr, word_addr;
    int unsigned bit_offset;
    logic [71:0] wdata_spm_w_ecc;
    if (addr >= SYS_SPM_ST_ADDR && addr <= SYS_SPM_END_ADDR) begin
      // word size = 64 bit
      relative_addr = addr - SYS_SPM_ST_ADDR;
      word_addr     = relative_addr >> 3;
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_sys_spm_mem_path(addr), wdata_spm_w_ecc));
    end
    else if (addr >= AICORE_0_SPM_ST_ADDR && addr <= AICORE_0_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_aicore_spm_mem_path(0, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, AICORE_0);
    end
    else if (addr >= AICORE_1_SPM_ST_ADDR && addr <= AICORE_1_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_aicore_spm_mem_path(1, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, AICORE_1);
    end
    else if (addr >= AICORE_2_SPM_ST_ADDR && addr <= AICORE_2_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_aicore_spm_mem_path(2, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, AICORE_2);
    end
    else if (addr >= AICORE_3_SPM_ST_ADDR && addr <= AICORE_3_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_aicore_spm_mem_path(3, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, AICORE_3);
    end
    else if (addr >= AICORE_4_SPM_ST_ADDR && addr <= AICORE_4_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_aicore_spm_mem_path(4, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, AICORE_4);
    end
    else if (addr >= AICORE_5_SPM_ST_ADDR && addr <= AICORE_5_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_aicore_spm_mem_path(5, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, AICORE_5);
    end
    else if (addr >= AICORE_6_SPM_ST_ADDR && addr <= AICORE_6_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_aicore_spm_mem_path(6, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, AICORE_6);
    end
    else if (addr >= AICORE_7_SPM_ST_ADDR && addr <= AICORE_7_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_aicore_spm_mem_path(7, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, AICORE_7);
    end
    else if (addr >= PVE_0_SPM_ST_ADDR && addr <= PVE_0_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_pve_spm_mem_path(0, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, PVE_0);
    end
    else if (addr >= PVE_1_SPM_ST_ADDR && addr <= PVE_1_SPM_END_ADDR) begin
      // add the ECC
      wdata_spm_w_ecc = add_spm_ecc(wdata);
      assert (uvm_hdl_deposit(get_pve_spm_mem_path(1, addr), wdata_spm_w_ecc)) else `gen_err_msg(backdoor_write, PVE_1);
    end
    else if (addr >= AICORE_0_L1_ST_ADDR && addr <= AICORE_0_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_deposit(0, addr, wdata);
    end
    else if (addr >= AICORE_1_L1_ST_ADDR && addr <= AICORE_1_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_deposit(1, addr, wdata);
    end
    else if (addr >= AICORE_2_L1_ST_ADDR && addr <= AICORE_2_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_deposit(2, addr, wdata);
    end
    else if (addr >= AICORE_3_L1_ST_ADDR && addr <= AICORE_3_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_deposit(3, addr, wdata);
    end
    else if (addr >= AICORE_4_L1_ST_ADDR && addr <= AICORE_4_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_deposit(4, addr, wdata);
    end
    else if (addr >= AICORE_5_L1_ST_ADDR && addr <= AICORE_5_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_deposit(5, addr, wdata);
    end
    else if (addr >= AICORE_6_L1_ST_ADDR && addr <= AICORE_6_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_deposit(6, addr, wdata);
    end
    else if (addr >= AICORE_7_L1_ST_ADDR && addr <= AICORE_7_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_deposit(7, addr, wdata);
    end
    else if (addr >= DDR_0_MEM_ST_ADDR && addr <= DDR_1_MEM_END_ADDR) begin
      // word size = 256 bit
      bit [255:0] wdata_256;
      word_addr     = addr >> 5;
      bit_offset    = addr[4:0] * 8;
      wdata_256 = lpddr_backdoor_read(word_addr);
      wdata_256[bit_offset +: 64] = wdata;
      lpddr_backdoor_write(word_addr, wdata_256);
    end
    else begin
      `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", addr))
    end
    `uvm_info("backdoor_write", $sformatf("0x%x -> [0x%x]", wdata, addr), UVM_DEBUG);
  endfunction : backdoor_write


  function static void backdoor_read(bit [63:0] addr, output bit [63:0] rdata);
    bit [63:0] relative_addr, word_addr;
    int unsigned bit_offset;
    if (addr >= SYS_SPM_ST_ADDR && addr <= SYS_SPM_END_ADDR) begin
      // word size = 64 bit
      relative_addr = addr - SYS_SPM_ST_ADDR;
      word_addr     = relative_addr >> 3;
        assert (uvm_hdl_read(get_sys_spm_mem_path(addr), rdata));
    end
    else if (addr >= AICORE_0_SPM_ST_ADDR && addr <= AICORE_0_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_aicore_spm_mem_path(0, addr), rdata)) else `gen_err_msg(backdoor_read, AICORE_0);
    end
    else if (addr >= AICORE_1_SPM_ST_ADDR && addr <= AICORE_1_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_aicore_spm_mem_path(1, addr), rdata)) else `gen_err_msg(backdoor_read, AICORE_1);
    end
    else if (addr >= AICORE_2_SPM_ST_ADDR && addr <= AICORE_2_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_aicore_spm_mem_path(2, addr), rdata)) else `gen_err_msg(backdoor_read, AICORE_2);
    end
    else if (addr >= AICORE_3_SPM_ST_ADDR && addr <= AICORE_3_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_aicore_spm_mem_path(3, addr), rdata)) else `gen_err_msg(backdoor_read, AICORE_3);
    end
    else if (addr >= AICORE_4_SPM_ST_ADDR && addr <= AICORE_4_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_aicore_spm_mem_path(4, addr), rdata)) else `gen_err_msg(backdoor_read, AICORE_4);
    end
    else if (addr >= AICORE_5_SPM_ST_ADDR && addr <= AICORE_5_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_aicore_spm_mem_path(5, addr), rdata)) else `gen_err_msg(backdoor_read, AICORE_5);
    end
    else if (addr >= AICORE_6_SPM_ST_ADDR && addr <= AICORE_6_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_aicore_spm_mem_path(6, addr), rdata)) else `gen_err_msg(backdoor_read, AICORE_6);
    end
    else if (addr >= AICORE_7_SPM_ST_ADDR && addr <= AICORE_7_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_aicore_spm_mem_path(7, addr), rdata)) else `gen_err_msg(backdoor_read, AICORE_7);
    end
    else if (addr >= PVE_0_SPM_ST_ADDR && addr <= PVE_0_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_pve_spm_mem_path(0, addr), rdata));
    end
    else if (addr >= PVE_1_SPM_ST_ADDR && addr <= PVE_1_SPM_END_ADDR) begin
      assert (uvm_hdl_read(get_pve_spm_mem_path(1, addr), rdata));
    end
    else if (addr >= AICORE_0_L1_ST_ADDR && addr <= AICORE_0_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_read(0, addr, rdata);
    end
    else if (addr >= AICORE_1_L1_ST_ADDR && addr <= AICORE_1_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_read(1, addr, rdata);
    end
    else if (addr >= AICORE_2_L1_ST_ADDR && addr <= AICORE_2_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_read(2, addr, rdata);
    end
    else if (addr >= AICORE_3_L1_ST_ADDR && addr <= AICORE_3_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_read(3, addr, rdata);
    end
    else if (addr >= AICORE_4_L1_ST_ADDR && addr <= AICORE_4_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_read(4, addr,rdata);
    end
    else if (addr >= AICORE_5_L1_ST_ADDR && addr <= AICORE_5_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_read(5, addr,rdata);
    end
    else if (addr >= AICORE_6_L1_ST_ADDR && addr <= AICORE_6_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_read(6, addr, rdata);
    end
    else if (addr >= AICORE_7_L1_ST_ADDR && addr <= AICORE_7_L1_END_ADDR) begin
      aic_l1_mem_path_hdl_read(7, addr,rdata);
    end
    else if (addr >= DDR_0_MEM_ST_ADDR && addr <= DDR_1_MEM_END_ADDR) begin
      // word size = 256 bit
      bit [255:0] rdata_256;
      word_addr     = addr >> 5;
      bit_offset    = addr[4:0] * 8;
      rdata_256 = lpddr_backdoor_read(word_addr);
      rdata = rdata_256[bit_offset +: 64];
    end
    else begin
      `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", addr))
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
