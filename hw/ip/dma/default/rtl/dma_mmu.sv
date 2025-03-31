// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA MMU
// Owner: Matt Morris <matt.morris@axelera.ai>


module dma_mmu
  import dma_pkg::*;
  import dma_mmu_reg_pkg::*;
#( parameter type dma_axi_addr_t = logic[39:0]
)
(
  input  wire             i_clk,
  input  wire             i_rst_n,
  input  logic            i_stall,

  input  dma_addr_t       i_addr,
  output dma_addr_t       o_addr,

  input  logic            i_en,
  input  dma_mmu_reg2hw_t i_cfg,

  output logic            o_irq

);

  logic [N_MMU_ENTRIES-1:0]         hit;
  logic                             irq, irq_q;
  logic [$clog2(N_MMU_ENTRIES)-1:0] idx, idx_q;
  dma_axi_addr_t                        addr_q;
  dma_axi_addr_t                        remapped_addr;


  for (genvar I=0; I < N_MMU_ENTRIES; I++) begin: g_per_region
    always_comb hit[I] = i_cfg.ch_mmu_cfg[I] &&
                         (i_addr[$bits(dma_axi_addr_t)-1:DMA_PAGE_SIZE_BITS] >= i_cfg.ch_mmu_first[I]) &&
                         (i_addr[$bits(dma_axi_addr_t)-1:DMA_PAGE_SIZE_BITS] <= i_cfg.ch_mmu_last[I]);
  end: g_per_region


  always_comb begin
    idx = 0;
    for (int unsigned I = 0; I < N_MMU_ENTRIES; I++)
      if (hit[I]) idx = I;
  end

  always_comb irq = i_en && !(|hit);

  always_ff @ ( posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      irq_q <= 1'b0;
      idx_q <= '0;
      addr_q <= '0;
    end
    else if (!i_stall) begin
      irq_q <= irq;
      idx_q <= idx;
      addr_q <= i_addr;
    end
  end

  always_comb remapped_addr = {(addr_q[$bits(dma_axi_addr_t)-1:DMA_PAGE_SIZE_BITS] - i_cfg.ch_mmu_first[idx_q] + i_cfg.ch_mmu_base[idx_q]),
                                addr_q[DMA_PAGE_SIZE_BITS-1:0]};

  always_comb o_addr = i_en ? remapped_addr : addr_q;



endmodule

