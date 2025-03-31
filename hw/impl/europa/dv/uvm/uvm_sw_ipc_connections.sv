import uvm_sw_ipc_pkg::uvm_sw_ipc_config;

parameter logic [35:0] SYS_SPM_MEM_ST_ADDR = aipu_addr_map_pkg::SYS_SPM_ST_ADDR;
parameter logic [35:0] SYS_SPM_MEM_END_ADDR = aipu_addr_map_pkg::SYS_SPM_END_ADDR;
parameter logic [35:0] SYS_SPM_MEM_SIZE = SYS_SPM_MEM_END_ADDR - SYS_SPM_MEM_ST_ADDR + 1'b1;

uvm_sw_ipc_config m_uvm_sw_ipc_config[top_level_test_pkg::CORE_NUMBER];

uvm_sw_ipc_if uvm_sw_ipc_if();

generate
  for (genvar i=0; i< top_level_test_pkg::CORE_NUMBER; i++) begin
    initial begin
      // initialize UVW_SW_IPC configurations
      // One per HART
      // IPC memory regions for the different HARTs are "densely" packed in memory
      // sys_spm start                                                                sys_spm end
      //      +----------------------------------------------------------------------------+
      //      |                                     | pve_1 | pve_0 | aicore 7-0 | apu 5-0 |
      //      +----------------------------------------------------------------------------+
      automatic bit [63:0] base_address = SYS_SPM_MEM_ST_ADDR + SYS_SPM_MEM_SIZE - ((i+1) * uvm_sw_ipc_pkg::UVM_SW_IPC_MEM_SIZE);
      m_uvm_sw_ipc_config[i] = new(
        .name               ($sformatf("m_uvm_sw_ipc_config[%0d]", i)),
        .base_address       (base_address),
        .handle_end_of_test (i == 0 ? 1 : 0) // handle end of test on apu0 only
      );
      m_uvm_sw_ipc_config[i].vif = uvm_sw_ipc_if;
      if (base_address[22:16] != {7{1'b1}}) begin
          `uvm_fatal("uvm_sw_ipc_connections", $sformatf(
            "base_address=0x%x; regions needs to be located in sys_spm's bank=3,minibank=3,subbank=3,inst_nb=1",
            base_address))
      end
      uvm_config_db#(uvm_sw_ipc_config)::set(null, $sformatf("uvm_test_top.m_uvm_sw_ipc[%0d]", i), "config", m_uvm_sw_ipc_config[i]);
    end
  end
endgenerate

`define SYS_SPM_UVM_SW_IPC_SRAM_INST \
  i_hdl_top.i_europa.u_aipu.u_sys_spm_p.u_sys_spm.u_spm.u_spm_mem.g_bank_inst[3].u_spm_mem_bank.g_sub_bank_inst[3].u_spm_mem_sub_bank.g_mini_bank_inst[3].u_spm_mem_mini_bank.g_sram_inst[1].u_tc_sram
assign uvm_sw_ipc_if.clock   = `SYS_SPM_UVM_SW_IPC_SRAM_INST.i_clk;
assign uvm_sw_ipc_if.reset   = !`SYS_SPM_UVM_SW_IPC_SRAM_INST.i_rst_n;
assign uvm_sw_ipc_if.cen     = `SYS_SPM_UVM_SW_IPC_SRAM_INST.i_req;
assign uvm_sw_ipc_if.wen     = `SYS_SPM_UVM_SW_IPC_SRAM_INST.i_wr_enable;
assign uvm_sw_ipc_if.address = aipu_addr_map_pkg::SYS_SPM_ST_ADDR + {7'b111_1111, `SYS_SPM_UVM_SW_IPC_SRAM_INST.i_addr, 3'b000};;
assign uvm_sw_ipc_if.rdata   = `SYS_SPM_UVM_SW_IPC_SRAM_INST.o_rd_data;
assign uvm_sw_ipc_if.wdata   = `SYS_SPM_UVM_SW_IPC_SRAM_INST.i_wr_data;
assign uvm_sw_ipc_if.byteen  = `SYS_SPM_UVM_SW_IPC_SRAM_INST.i_wr_mask;

// dummy: for uvm_sw_ipc_hdl_*() test purpose
reg [63:0] dummy_uvm_sw_ipc_hdl_test_reg;
