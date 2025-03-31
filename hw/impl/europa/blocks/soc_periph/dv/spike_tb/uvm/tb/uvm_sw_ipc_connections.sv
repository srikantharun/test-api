`ifndef UVM_SW_IPC_CONNECTIONS_SV
`define UVM_SW_IPC_CONNECTIONS_SV

import uvm_pkg::*;
import uvm_sw_ipc_pkg::uvm_sw_ipc_config;

parameter logic [35:0] SYS_SPM_MEM_ST_ADDR = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
parameter logic [35:0] SYS_SPM_MEM_END_ADDR = aipu_addr_map_pkg::SYS_SPM_END_ADDR;
parameter logic [35:0] SYS_SPM_MEM_SIZE = SYS_SPM_MEM_END_ADDR - SYS_SPM_MEM_ST_ADDR + 1'b1;

uvm_sw_ipc_config m_uvm_sw_ipc_spike_config;
uvm_sw_ipc_if uvm_sw_ipc_mem_if();

`define SYS_SPM_MEM_PATH u_dv_axi_ram
assign uvm_sw_ipc_mem_if.clock   = `SYS_SPM_MEM_PATH.clk;
assign uvm_sw_ipc_mem_if.reset   = `SYS_SPM_MEM_PATH.rst;
assign uvm_sw_ipc_mem_if.cen     = `SYS_SPM_MEM_PATH.mem_wr_en || `SYS_SPM_MEM_PATH.mem_rd_en;
assign uvm_sw_ipc_mem_if.wen     = `SYS_SPM_MEM_PATH.mem_wr_en;
assign uvm_sw_ipc_mem_if.address = ((`SYS_SPM_MEM_PATH.mem_wr_en ? `SYS_SPM_MEM_PATH.write_addr_valid : `SYS_SPM_MEM_PATH.read_addr_valid) << 3);
assign uvm_sw_ipc_mem_if.rdata   = `SYS_SPM_MEM_PATH.s_axi_rdata;
assign uvm_sw_ipc_mem_if.wdata   = `SYS_SPM_MEM_PATH.s_axi_wdata;
assign uvm_sw_ipc_mem_if.byteen  = `SYS_SPM_MEM_PATH.s_axi_wstrb;

initial begin
  m_uvm_sw_ipc_spike_config = new(
      .name("m_uvm_sw_ipc_spike_config"),
      .base_address(SYS_SPM_MEM_ST_ADDR + SYS_SPM_MEM_SIZE - uvm_sw_ipc_pkg::UVM_SW_IPC_MEM_SIZE),
      .handle_end_of_test(1)
  );
  m_uvm_sw_ipc_spike_config.vif = uvm_sw_ipc_mem_if;

  uvm_config_db#(uvm_sw_ipc_config)::set(null, "uvm_test_top.m_uvm_sw_ipc", "config", m_uvm_sw_ipc_spike_config);
end

// dummy: for uvm_sw_ipc_hdl_*() test purpose
wire [63:0] dummy_uvm_sw_ipc_hdl_test_wire = 64'h12345678abcdef90;
reg [63:0] dummy_uvm_sw_ipc_hdl_test_reg;

`endif // UVM_SW_IPC_CONNECTIONS_SV
