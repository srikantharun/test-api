// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS L1 MMIO Connection.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

// Macros for assigning DMC MMIO if connections
`define assign_dmc_read_mmio_if(port_name, index) \
  /* request */ \
  assign ``port_name``_mmio_if.req.addr      = `LS_DUT_PATH.u_l1.i_dmc_ro_req[index].payload.addr; \
  assign ``port_name``_mmio_if.req.valid     = `LS_DUT_PATH.u_l1.i_dmc_ro_req[index].valid; \
  assign ``port_name``_mmio_if.req.rsp_ready = `LS_DUT_PATH.u_l1.i_dmc_ro_req[index].rsp_ready; \
  /* response */ \
  assign ``port_name``_mmio_if.rsp.data      = `LS_DUT_PATH.u_l1.o_dmc_ro_rsp[index].payload.data; \
  assign ``port_name``_mmio_if.rsp.error     = `LS_DUT_PATH.u_l1.o_dmc_ro_rsp[index].payload.error; \
  assign ``port_name``_mmio_if.rsp.ack       = `LS_DUT_PATH.u_l1.o_dmc_ro_rsp[index].ack; \
  assign ``port_name``_mmio_if.rsp.ready     = `LS_DUT_PATH.u_l1.o_dmc_ro_rsp[index].ready;

`define assign_dmc_write_mmio_if(port_name, index) \
  /* request */ \
  assign ``port_name``_mmio_if.req.addr      = `LS_DUT_PATH.u_l1.i_dmc_wo_req[index].payload.addr; \
  assign ``port_name``_mmio_if.req.we        = `LS_DUT_PATH.u_l1.i_dmc_wo_req[index].payload.wbe; \
  assign ``port_name``_mmio_if.req.data      = `LS_DUT_PATH.u_l1.i_dmc_wo_req[index].payload.data; \
  assign ``port_name``_mmio_if.req.valid     = `LS_DUT_PATH.u_l1.i_dmc_wo_req[index].valid; \
  assign ``port_name``_mmio_if.req.rsp_ready = `LS_DUT_PATH.u_l1.i_dmc_wo_req[index].rsp_ready; \
  /* response */ \
  assign ``port_name``_mmio_if.rsp.error     = `LS_DUT_PATH.u_l1.o_dmc_wo_rsp[index].payload.error; \
  assign ``port_name``_mmio_if.rsp.ack       = `LS_DUT_PATH.u_l1.o_dmc_wo_rsp[index].ack; \
  assign ``port_name``_mmio_if.rsp.ready     = `LS_DUT_PATH.u_l1.o_dmc_wo_rsp[index].ready;


//LS_DUT_PATH defined in ls_dmc_connections.sv
`ifdef AI_CORE_TOP_ENV_CHECK
  string LS_ENV_PATH="uvm_test_top.env.m_ls_env";
`else
  string LS_ENV_PATH="uvm_test_top.m_env";
`endif
  
typedef virtual mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH) mmio_if_t;
// L1 DMC Fabric MMIO Interface
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  dmc_mifd0_mmio_if (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  dmc_mifd1_mmio_if (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  dmc_mifd2_mmio_if (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  dmc_mifdw_mmio_if (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  dmc_modr_mmio_if  (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  dmc_difd0_mmio_if (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  dmc_difd1_mmio_if (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  dmc_dodr_mmio_if  (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);

mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  axi_wr_mmio_if  (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);
mmio_if#(MMIO_DMC_DATA_WIDTH, MMIO_DMC_ADDR_WIDTH)  axi_rd_mmio_if  (`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);

// READ Connection
// DMC 
`assign_dmc_read_mmio_if(dmc_mifd0, 0)
`assign_dmc_read_mmio_if(dmc_mifd1, 1)
`assign_dmc_read_mmio_if(dmc_mifd2, 2)
`assign_dmc_read_mmio_if(dmc_mifdw, 3)
`assign_dmc_read_mmio_if(dmc_difd0, 4)
`assign_dmc_read_mmio_if(dmc_difd1, 5)
// AXI
`assign_dmc_read_mmio_if(axi_rd, 6)

// WRITE Connection
// DMC 
`assign_dmc_write_mmio_if(dmc_modr, 0)
`assign_dmc_write_mmio_if(dmc_dodr, 1)
// AXI
`assign_dmc_write_mmio_if(axi_wr, 2)

initial begin
  // Adding to config db
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_dmc_m_ifd0"}, "vif", dmc_mifd0_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_dmc_m_ifd1"}, "vif", dmc_mifd1_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_dmc_m_ifd2"}, "vif", dmc_mifd2_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_dmc_m_ifdw"}, "vif", dmc_mifdw_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_dmc_m_odr"},  "vif", dmc_modr_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_dmc_d_ifd0"}, "vif", dmc_difd0_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_dmc_d_ifd1"}, "vif", dmc_difd1_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_dmc_d_odr"},  "vif", dmc_dodr_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_axi_wr"}, "vif", axi_wr_mmio_if);
  uvm_config_db#(mmio_if_t)::set(null, {LS_ENV_PATH, ".mmio_axi_rd"}, "vif", axi_rd_mmio_if);
end

