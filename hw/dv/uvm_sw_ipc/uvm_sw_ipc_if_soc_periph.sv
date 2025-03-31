`ifndef UVM_SW_IPC_IF_SOC_PERIPH_SV
`define UVM_SW_IPC_IF_SOC_PERIPH_SV

interface uvm_sw_ipc_if ();
  timeunit 1ns; timeprecision 1ps;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import uvm_sw_ipc_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;


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
  parameter logic [63:0] SYS_SPM_MEM_ST_ADDR = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
  parameter logic [63:0] SYS_SPM_MEM_END_ADDR = aipu_addr_map_pkg::SYS_SPM_END_ADDR;
  parameter logic [63:0] AXI_VIP_SLAVE_ST_ADDR = 'hF0000000;
  parameter logic [63:0] AXI_VIP_SLAVE_END_ADDR = 'hF0400000;


  function static string get_mem_path(bit [63:0] addr);
    return $sformatf("spike_top_tb.th.u_dv_axi_ram.mem[%0d]", addr >> 3);
  endfunction : get_mem_path


  function static void backdoor_write(bit [63:0] addr, bit [63:0] wdata);
    if (addr >= SYS_SPM_MEM_ST_ADDR && addr <= SYS_SPM_MEM_END_ADDR) begin
`ifndef DV_AXI_RAM_UNBOUNDED
      assert (uvm_hdl_deposit(get_mem_path(addr), wdata));
`else
      automatic integer unsigned idx = addr >> 3;
      u_dv_axi_ram.mem[idx] = wdata;
`endif
    end else begin
      `uvm_fatal("uvm_sw_ipc_if", $sformatf("address 0x%x is not supported yet", addr))
    end
    `uvm_info("backdoor_write", $sformatf("0x%x -> [0x%x]", wdata, addr), UVM_DEBUG);
  endfunction : backdoor_write


  function static void backdoor_read(bit [63:0] addr, output bit [63:0] rdata);
    if (addr >= SYS_SPM_MEM_ST_ADDR && addr <= SYS_SPM_MEM_END_ADDR) begin
`ifndef DV_AXI_RAM_UNBOUNDED
      assert (uvm_hdl_read(get_mem_path(addr), rdata));
`else
      automatic integer unsigned idx = addr >> 3;
      rdata = u_dv_axi_ram.mem[idx];
`endif
    end else if (addr >= AXI_VIP_SLAVE_ST_ADDR && addr <= AXI_VIP_SLAVE_END_ADDR) begin
      automatic uvm_component comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env.slave[0]");
      automatic svt_axi_slave_agent slave_agent;
      $cast(slave_agent, comp);
      rdata = slave_agent.axi_slave_mem.read(addr);
    end else begin
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

`endif  // UVM_SW_IPC_IF_SOC_PERIPH_SV
