// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: SVA of l2
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_SVA_SV
`define L2_SVA_SV

module l2_sva
  import l2_pkg::*;
  import l2_cfg_pkg::*;
  (
  // Clock and reset signals
  input wire              i_clk,
  input wire              i_rst_n,

  // SRAM configuration
  axe_tcl_sram_pkg::impl_inp_t i_impl,
  axe_tcl_sram_pkg::impl_oup_t o_impl


  );
  // =====================================================
  // Local parameters
  // =====================================================
  localparam int unsigned N_MACROS = L2_NUM_BANKS*L2_NUM_RAMS*L2_NUM_SRAMS;

  // =====================================================
  // Type definition
  // =====================================================

  // =====================================================
  // Signal declarations
  // =====================================================

  // =====================================================
  // Bind signals
  // =====================================================

  // =====================================================
  // Properties
  // =====================================================

  property p_ram_cfg(bit       tc_sram_se
                    ,bit       tc_sram_ret
                    ,bit [1:0] tc_sram_mcs
                    ,bit       tc_sram_mcsw
                    ,bit [2:0] tc_sram_adme);
  @(posedge i_clk) disable iff (~i_rst_n)
    (
      i_impl.se     == tc_sram_se     &&
      i_impl.ret    == tc_sram_ret    &&
      i_impl.mcs    == tc_sram_mcs    &&
      i_impl.mcsw   == tc_sram_mcsw   &&
      i_impl.adme   == tc_sram_adme
    );
  endproperty

  property p_pde_prn_macro(int unsigned latency, bit prn);
    bit pde;
    @(posedge i_clk) disable iff (~i_rst_n)
      (
        (('1, pde=i_impl.pde) |-> ##(latency) (prn==pde))
      );
  endproperty

  // =====================================================
  // Assumes
  // =====================================================

  // =====================================================
  // Assertions
  // =====================================================
  for (genvar bank = 0; bank < L2_NUM_BANKS; bank++) begin : g_bank
    for (genvar ram = 0; ram < L2_NUM_RAMS; ram++) begin : g_ram
      for (genvar sram = 0; sram < L2_NUM_SRAMS; sram++) begin : g_sram
        ap_ram_cfg      : assert property (p_ram_cfg(l2.u_l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.g_sram[sram].u_l2_ram_wrapper.i_impl.se
                                                    ,l2.u_l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.g_sram[sram].u_l2_ram_wrapper.i_impl.ret
                                                    ,l2.u_l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.g_sram[sram].u_l2_ram_wrapper.i_impl.mcs
                                                    ,l2.u_l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.g_sram[sram].u_l2_ram_wrapper.i_impl.mcsw
                                                    ,l2.u_l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.g_sram[sram].u_l2_ram_wrapper.i_impl.adme
                                                    ));
        ap_pde_prn_macro: assert property (p_pde_prn_macro(L2_ARB_CHAIN_ORDER[bank][ram][sram]+1
                                                          ,l2.u_l2_mem.g_bank[bank].u_l2_bank.g_ram[ram].u_l2_ram.g_sram[sram].u_l2_ram_wrapper.o_impl.prn));
      end
    end
  end

  ap_pde_prn_end_to_end: assert property (p_pde_prn_macro(N_MACROS, o_impl.prn));

  // =====================================================
  // Covers
  // =====================================================

endmodule

`endif  // L2_SVA_SV
