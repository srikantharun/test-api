// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Anonymous <anonymous@axelera.ai>


/// TODO:__one_line_summary_of_pve_tb__
///
module pve_tb;
  import axi_pkg::*;

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

  // Design Under Test (DUT)
  pve i_pve_dut (
    .i_clk (tb_clk),
    .i_rst_n (tb_rst_n),
    .i_timer_irq ('0),
    .i_hart_base ('0),
    .o_ctrlo_axi_m_awvalid (),
    .i_ctrlo_axi_m_awready ('0),
    .o_ctrlo_axi_m_awaddr (),
    .o_ctrlo_axi_m_awid (),
    .o_ctrlo_axi_m_awuser (),
    .o_ctrlo_axi_m_awlen (),
    .o_ctrlo_axi_m_awsize (),
    .o_ctrlo_axi_m_awburst (),
    .o_ctrlo_axi_m_awlock (),
    .o_ctrlo_axi_m_awcache (),
    .o_ctrlo_axi_m_awprot (),
    .o_ctrlo_axi_m_wvalid (),
    .i_ctrlo_axi_m_wready ('0),
    .o_ctrlo_axi_m_wuser (),
    .o_ctrlo_axi_m_wdata (),
    .o_ctrlo_axi_m_wstrb (),
    .o_ctrlo_axi_m_wlast (),
    .i_ctrlo_axi_m_bvalid ('0),
    .o_ctrlo_axi_m_bready (),
    .i_ctrlo_axi_m_bid ('0),
    .i_ctrlo_axi_m_buser ('0),
    .i_ctrlo_axi_m_bresp (axi_resp_e'(AXI_RESP_OKAY)),
    .o_ctrlo_axi_m_arvalid (),
    .i_ctrlo_axi_m_arready ('0),
    .o_ctrlo_axi_m_araddr (),
    .o_ctrlo_axi_m_arid (),
    .o_ctrlo_axi_m_aruser (),
    .o_ctrlo_axi_m_arlen (),
    .o_ctrlo_axi_m_arsize (),
    .o_ctrlo_axi_m_arburst (),
    .o_ctrlo_axi_m_arlock (),
    .o_ctrlo_axi_m_arcache (),
    .o_ctrlo_axi_m_arprot (),
    .i_ctrlo_axi_m_rvalid ('0),
    .o_ctrlo_axi_m_rready (),
    .i_ctrlo_axi_m_rid ('0),
    .i_ctrlo_axi_m_ruser ('0),
    .i_ctrlo_axi_m_rdata ('0),
    .i_ctrlo_axi_m_rresp (axi_resp_e'(AXI_RESP_OKAY)),
    .i_ctrlo_axi_m_rlast ('0),

    .i_ctrli_axi_s_awvalid ('0),
    .o_ctrli_axi_s_awready (),
    .i_ctrli_axi_s_awaddr ('0),
    .i_ctrli_axi_s_awid ('0),
    .i_ctrli_axi_s_awuser ('0),
    .i_ctrli_axi_s_awlen ('0),
    .i_ctrli_axi_s_awsize (axi_size_e'(AXI_BYTES_1)),
    .i_ctrli_axi_s_awburst (axi_burst_e'(AXI_BURST_FIXED)),
    .i_ctrli_axi_s_awlock ('0),
    .i_ctrli_axi_s_awcache (axi_cache_e'(CACHE_BUFFERABLE)),
    .i_ctrli_axi_s_awprot ('0),
    .i_ctrli_axi_s_wvalid ('0),
    .o_ctrli_axi_s_wready (),
    .i_ctrli_axi_s_wuser ('0),
    .i_ctrli_axi_s_wdata ('0),
    .i_ctrli_axi_s_wstrb ('0),
    .i_ctrli_axi_s_wlast ('0),
    .o_ctrli_axi_s_bvalid (),
    .i_ctrli_axi_s_bready ('0),
    .o_ctrli_axi_s_bid (),
    .o_ctrli_axi_s_buser (),
    .o_ctrli_axi_s_bresp (),
    .i_ctrli_axi_s_arvalid ('0),
    .o_ctrli_axi_s_arready (),
    .i_ctrli_axi_s_araddr ('0),
    .i_ctrli_axi_s_arid ('0),
    .i_ctrli_axi_s_aruser ('0),
    .i_ctrli_axi_s_arlen ('0),
    .i_ctrli_axi_s_arsize (axi_size_e'(AXI_BYTES_1)),
    .i_ctrli_axi_s_arburst (axi_burst_e'(AXI_BURST_FIXED)),
    .i_ctrli_axi_s_arlock ('0),
    .i_ctrli_axi_s_arcache (axi_cache_e'(CACHE_BUFFERABLE)),
    .i_ctrli_axi_s_arprot ('0),
    .o_ctrli_axi_s_rvalid (),
    .i_ctrli_axi_s_rready ('0),
    .o_ctrli_axi_s_rid (),
    .o_ctrli_axi_s_ruser (),
    .o_ctrli_axi_s_rdata (),
    .o_ctrli_axi_s_rresp (),
    .o_ctrli_axi_s_rlast (),
    .o_dma_axi_m_awvalid (),
    .i_dma_axi_m_awready ('0),
    .o_dma_axi_m_awaddr (),
    .o_dma_axi_m_awid (),
    .o_dma_axi_m_awuser (),
    .o_dma_axi_m_awlen (),
    .o_dma_axi_m_awsize (),
    .o_dma_axi_m_awburst (),
    .o_dma_axi_m_awlock (),
    .o_dma_axi_m_awcache (),
    .o_dma_axi_m_awprot (),
    .o_dma_axi_m_wvalid (),
    .i_dma_axi_m_wready ('0),
    .o_dma_axi_m_wuser (),
    .o_dma_axi_m_wdata (),
    .o_dma_axi_m_wstrb (),
    .o_dma_axi_m_wlast (),
    .i_dma_axi_m_bvalid ('0),
    .o_dma_axi_m_bready (),
    .i_dma_axi_m_bid ('0),
    .i_dma_axi_m_buser ('0),
    .i_dma_axi_m_bresp (axi_resp_e'(AXI_RESP_OKAY)),
    .o_dma_axi_m_arvalid (),
    .i_dma_axi_m_arready ('0),
    .o_dma_axi_m_araddr (),
    .o_dma_axi_m_arid (),
    .o_dma_axi_m_aruser (),
    .o_dma_axi_m_arlen (),
    .o_dma_axi_m_arsize (),
    .o_dma_axi_m_arburst (),
    .o_dma_axi_m_arlock (),
    .o_dma_axi_m_arcache (),
    .o_dma_axi_m_arprot (),
    .i_dma_axi_m_rvalid ('0),
    .o_dma_axi_m_rready (),
    .i_dma_axi_m_rid ('0),
    .i_dma_axi_m_ruser ('0),
    .i_dma_axi_m_rdata ('0),
    .i_dma_axi_m_rresp (axi_resp_e'(AXI_RESP_OKAY)),
    .i_dma_axi_m_rlast ('0),
    .i_mem_impl ('0),
    .o_mem_impl ()
  );

endmodule
