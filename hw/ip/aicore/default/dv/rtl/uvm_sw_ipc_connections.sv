import uvm_sw_ipc_pkg::uvm_sw_ipc_config;

parameter logic [32:0] AICORE_0_HARTID = 6;
parameter logic [35:0] SYS_SPM_MEM_ST_ADDR           = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
parameter logic [35:0] SYS_SPM_MEM_END_ADDR          = aipu_addr_map_pkg::SYS_SPM_END_ADDR;
parameter logic [35:0] SYS_SPM_MEM_SIZE              = SYS_SPM_MEM_END_ADDR - SYS_SPM_MEM_ST_ADDR + 1'b1;

uvm_sw_ipc_config m_uvm_sw_ipc_aicore_config;
uvm_sw_ipc_if uvm_sw_ipc_aicore_if();

bit uvm_sw_ipc_handle_end_of_test = $test$plusargs("UVM_SW_IPC_HANDLE_END_OF_TEST");
`define SYS_SPM_VELOCE_SRAM i_fake_sys_spm
assign uvm_sw_ipc_aicore_if.clock   = `SYS_SPM_VELOCE_SRAM.clk;
assign uvm_sw_ipc_aicore_if.reset   = `SYS_SPM_VELOCE_SRAM.rst;
assign uvm_sw_ipc_aicore_if.cen     = `SYS_SPM_VELOCE_SRAM.mem_wr_en || `SYS_SPM_VELOCE_SRAM.mem_rd_en;
assign uvm_sw_ipc_aicore_if.wen     = `SYS_SPM_VELOCE_SRAM.mem_wr_en;
assign uvm_sw_ipc_aicore_if.address = ((`SYS_SPM_VELOCE_SRAM.mem_wr_en ? `SYS_SPM_VELOCE_SRAM.write_addr_valid : `SYS_SPM_VELOCE_SRAM.read_addr_valid) << 3);
assign uvm_sw_ipc_aicore_if.rdata   = `SYS_SPM_VELOCE_SRAM.s_axi_rdata;
assign uvm_sw_ipc_aicore_if.wdata   = `SYS_SPM_VELOCE_SRAM.s_axi_wdata;
assign uvm_sw_ipc_aicore_if.byteen  = `SYS_SPM_VELOCE_SRAM.s_axi_wstrb;

initial begin

    // initialize UVW_SW_IPC configurations
    automatic bit [63:0] base_address = SYS_SPM_MEM_ST_ADDR + SYS_SPM_MEM_SIZE - ((AICORE_0_HARTID+1) * uvm_sw_ipc_pkg::UVM_SW_IPC_MEM_SIZE);
    m_uvm_sw_ipc_aicore_config= new(
      .name               ("m_uvm_sw_ipc_aicore_config"),
      .base_address       (base_address),
      .handle_end_of_test (uvm_sw_ipc_handle_end_of_test) // handle end of test
    );
    m_uvm_sw_ipc_aicore_config.vif = uvm_sw_ipc_aicore_if;

    uvm_config_db#(uvm_sw_ipc_config)::set(null, "uvm_test_top.m_uvm_sw_ipc_aicore", "config", m_uvm_sw_ipc_aicore_config);
 
end

// dummy: for uvm_sw_ipc_hdl_*() test purpose
wire [63:0] dummy_uvm_sw_ipc_hdl_test_wire = 64'h12345678abcdef90;
reg [63:0] dummy_uvm_sw_ipc_hdl_test_reg;
