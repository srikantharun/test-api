// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AIC LS L1 RVV Connections.
// Owner: Rafael Frangulyan Polyak <rafael.frangulian@axelera.ai>

// Macro for assigning RVV if connections
`define assign_rvv_if(index) \
    /* request */ \
    assign i_rvv_``index``_req_addr  = rvv_mmio_if[index].req.addr; \
    assign i_rvv_``index``_req_we    = rvv_mmio_if[index].req.we; \
    assign i_rvv_``index``_req_be    = rvv_mmio_if[index].req.wbe; \
    assign i_rvv_``index``_req_wdata = rvv_mmio_if[index].req.data; \
    assign i_rvv_``index``_req_valid = rvv_mmio_if[index].req.valid; \
    assign i_rvv_``index``_req_size  = 0; \
    /* response */ \
    assign rvv_mmio_if[index].rsp.data  = o_rvv_``index``_res_rdata; \
    assign rvv_mmio_if[index].rsp.error = o_rvv_``index``_res_err; \
    assign rvv_mmio_if[index].rsp.ack   = o_rvv_``index``_res_valid; \
    assign rvv_mmio_if[index].rsp.ready = o_rvv_``index``_req_ready; 

import rvv_agent_pkg::*;

mmio_if#(MMIO_RVV_DATA_WIDTH, MMIO_RVV_ADDR_WIDTH)  rvv_mmio_if[cva6v_ai_core_pkg::MemPortCount](`LS_DUT_PATH.i_clk, `LS_DUT_PATH.i_rst_n);

// RVV 0:
`assign_rvv_if(0);
// RVV 1:
`assign_rvv_if(1);
// RVV 2:
`assign_rvv_if(2);
// RVV 3:
`assign_rvv_if(3);
// RVV 4:
`assign_rvv_if(4);
// RVV 5:
`assign_rvv_if(5);
// RVV 6:
`assign_rvv_if(6);
// RVV 7:
`assign_rvv_if(7);
// RVV connections are just a series of mmio connections (they do have different fields then DMC mmio connections)
for (genvar i=0;i<8;i++) begin
  initial uvm_config_db#(virtual mmio_if#(MMIO_RVV_DATA_WIDTH, MMIO_RVV_ADDR_WIDTH))::set(null, $sformatf("%s.%s",LS_ENV_PATH, "m_rvv"), $sformatf("m_mmio_vif_%0d", i), rvv_mmio_if[i]);
end
