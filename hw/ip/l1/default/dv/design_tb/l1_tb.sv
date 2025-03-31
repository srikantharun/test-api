// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>


/// Simple L1 TB, currently only for instantiating the IP
///
module l1_tb;

  // Set to 1.2 GHz
  localparam realtime TbCycleTime = 0.8333ns;

  // Setup AT timing
  localparam realtime TbApplTime = 0.1 * TbCycleTime;
  localparam realtime TbTestTime = 0.9 * TbCycleTime;

  // Clock / Reset genereration and stop of simulation
  logic tb_clk;
  logic tb_rst_n;

  localparam int unsigned ResetCycles = 5;

  initial begin : proc_clk_rst_gen
    tb_clk   = 1'b0;
    tb_rst_n = 1'b0;
    fork
      begin : fork_clk_gen
        forever begin
          #(TbCycleTime/2);
          tb_clk = ~tb_clk;
        end
      end
      begin : fork_rst_gen
        repeat (ResetCycles) @(negedge tb_clk);
        tb_rst_n = 1'b1;
      end
    join
  end

  // Stimuli generation
  // TODO: Add some stimulies


  // Design Under Test (DUT)
  import axe_tcl_sram_pkg::*, mmio_pkg::*, l1_pkg::*;
  
  localparam uint_t L1_NUM_BANKS           = DEFAULT_L1_NUM_BANKS;
  localparam uint_t L1_NUM_DMC_WO_REQUESTS = DEFAULT_L1_NUM_DMC_WO_REQUESTS;
  localparam uint_t L1_NUM_DMC_RO_REQUESTS = DEFAULT_L1_NUM_DMC_RO_REQUESTS;
  localparam uint_t L1_NUM_RVV_REQUESTS    = DEFAULT_L1_NUM_RVV_REQUESTS;
  // =====================================================
  // DMC MMIO
  // =====================================================
  mmio_dmc_wo_req_t [L1_NUM_DMC_WO_REQUESTS-1:0] dmc_wo_req;
  mmio_dmc_wo_rsp_t [L1_NUM_DMC_WO_REQUESTS-1:0] dmc_wo_rsp;
  mmio_dmc_ro_req_t [L1_NUM_DMC_RO_REQUESTS-1:0] dmc_ro_req;
  mmio_dmc_ro_rsp_t [L1_NUM_DMC_RO_REQUESTS-1:0] dmc_ro_rsp;

  // =====================================================
  // RVV MMIO
  // =====================================================
  mmio_rvv_req_t [L1_NUM_RVV_REQUESTS-1:0] rvv_req;
  mmio_rvv_rsp_t [L1_NUM_RVV_REQUESTS-1:0] rvv_rsp;

  impl_inp_t mem_impl_inp;
  impl_oup_t mem_impl_oup;

  l1 u_l1_dut (
    .i_clk (tb_clk),
    .i_rst_n(tb_rst_n),

    .i_dmc_wo_req(dmc_wo_req),
    .o_dmc_wo_rsp(dmc_wo_rsp),
    .i_dmc_ro_req(dmc_ro_req),
    .o_dmc_ro_rsp(dmc_ro_rsp),

    .i_rvv_req(rvv_req),
    .o_rvv_rsp(rvv_rsp),

    .i_mem_impl(mem_impl_inp),
    .o_mem_impl(mem_impl_oup)
  );

  initial begin
    mem_impl_inp = '0;

    dmc_wo_req = '0;
    dmc_ro_req = '0;
    rvv_req = '0;

    for (int i=0; i<L1_NUM_DMC_WO_REQUESTS; i++) begin
      dmc_wo_req[i].payload.wbe = '1;
      dmc_wo_req[i].payload.data = {64{'hABCD+i}};
      dmc_wo_req[i].rsp_ready = '1;
    end
    for (int i=0; i<L1_NUM_DMC_RO_REQUESTS; i++) begin
      dmc_ro_req[i].rsp_ready = '1;
    end

    for (int i=0; i<L1_NUM_RVV_REQUESTS; i++) begin
      rvv_req[i].payload.wbe = '1;
      rvv_req[i].payload.data = {16{'hBAE2+i}};
      rvv_req[i].rsp_ready = '1;
    end

    wait (tb_rst_n);

    @(posedge tb_clk);
    wait (!mem_impl_oup.prn);

    @(posedge tb_clk);
    #0.01ns;
    dmc_wo_req[0].valid = 1'b1;
    dmc_wo_req[0].payload.addr = 'h0000;

    @(posedge tb_clk);
    #0.01ns;
    dmc_wo_req[0].valid = 1'b0;

    @(posedge tb_clk);
    #0.01ns;
    dmc_wo_req[0].valid = 1'b1;
    dmc_wo_req[0].payload.addr = 'h0040;
    dmc_wo_req[1].valid = 1'b1;
    dmc_wo_req[1].payload.addr = 'h100040;

    dmc_ro_req[0].valid = 1'b1;
    dmc_ro_req[0].payload.addr = 'h0000;

    dmc_ro_req[3].valid = 1'b1;
    dmc_ro_req[3].payload.addr = 'h0040;

    repeat (20) @(posedge tb_clk);
    #0.01ns;
    dmc_wo_req[0].valid = 1'b0;
    dmc_wo_req[1].valid = 1'b0;
    dmc_ro_req[0].valid = 1'b0;
    dmc_ro_req[3].valid = 1'b0;

    repeat (20) @(posedge tb_clk);

    #0.01ns;
    rvv_req[0].valid = 1'b1;
    rvv_req[0].payload.addr = 'h10040;
    rvv_req[0].payload.we = 1'b1;
    rvv_req[1].valid = 1'b1;
    rvv_req[1].payload.addr = 'h10050;
    rvv_req[1].payload.we = 1'b1;

    @(posedge tb_clk);
    #0.01ns;
    dmc_wo_req[0].valid = 1'b1;
    dmc_wo_req[0].payload.addr = 'h20040;

    @(posedge tb_clk);
    #0.01ns;
    dmc_wo_req[0].valid = 1'b0;

    repeat (2) @(posedge tb_clk);
    #0.01ns;
    rvv_req[0].valid = 1'b0;
    rvv_req[1].valid = 1'b0;
    repeat (20) @(posedge tb_clk);


  end

endmodule
