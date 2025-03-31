module sim_top ();
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `include "memory_preloading_macros.svh"
  import memory_preloading_pkg::*;

  import uvm_sw_ipc_pkg::*;
  import top_level_test_pkg::*;

  `define SYS_SPM_PATH i_hdl_top.i_europa.u_aipu.u_sys_spm_p.i_dv_axi_ram
  `include "./uvm_sw_ipc_connections.sv"

  bit clk;
  bit ref_clk;
  bit clk_enable;
  bit spi_clk2x;


  axe_clk_generator i_axe_clk_generator (
      .i_enable(clk_enable),
      .o_clk(clk)
  );
  axe_clk_generator i_axe_clk_generator_ref (
      .i_enable(clk_enable),
      .o_clk(ref_clk)
  );

  axe_clk_generator i_axe_clk_generator_spi_clk2x (
      .i_enable(clk_enable),
      .o_clk(spi_clk2x)
  );

  // TODO: @rodrigo.borges - remove when https://git.axelera.ai/prod/europa/-/issues/2367 is fixed
  bit lpddr_clk;
  axe_clk_generator i_axe_clk_generator_lpddr (
      .i_enable(clk_enable),
      .o_clk(lpddr_clk)
  );

  assign i_hdl_top.i_ref_clk = ref_clk;
  assign i_hdl_top.i_tck = clk;

  // 115200 baud * 4 CLK_SAMPLES => uart_clk_4x = 460800 Hz
  bit uart_clk_4x;
  always #1085ns uart_clk_4x = ~uart_clk_4x;
  assign i_hdl_top.uart_clk_4x = uart_clk_4x;

  function static void enable_instruction_dumping();
    logic dump_ax65_instructions;
    logic dump_cva6v_instructions;
    if (!$value$plusargs("dump_ax65_instructions=%d", dump_ax65_instructions)) begin
      dump_ax65_instructions = 0;
    end
    if (!$value$plusargs("dump_cva6v_instructions=%d", dump_cva6v_instructions)) begin
      dump_cva6v_instructions = 0;
    end
    force i_hdl_top.enable_ax65_instruction_dump = dump_ax65_instructions;
    force i_hdl_top.new_file_ax65_instruction_dump = dump_ax65_instructions;
`ifndef NO_CVA6V_MONITOR
    force i_hdl_top.enable_cva6v_instruction_dump = dump_cva6v_instructions;
    force i_hdl_top.new_file_cva6v_instruction_dump = dump_cva6v_instructions;
`endif
  endfunction

   string hex_path;
   bit preload_sys_spm_start = 1'b0;
   `MEMORY_PRELOADING_SYS_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_sys_spm_p.u_sys_spm.u_spm, hex_path, preload_sys_spm_start)
   bit preload_aicore_0_spm_start = 1'b0;
   bit preload_aicore_1_spm_start = 1'b0;
   bit preload_aicore_2_spm_start = 1'b0;
   bit preload_aicore_3_spm_start = 1'b0;
   bit preload_aicore_4_spm_start = 1'b0;
   bit preload_aicore_5_spm_start = 1'b0;
   bit preload_aicore_6_spm_start = 1'b0;
   bit preload_aicore_7_spm_start = 1'b0;
   bit preload_aicore0_l1_start = 1'b0;
   bit preload_aicore1_l1_start = 1'b0;
   bit preload_aicore2_l1_start = 1'b0;
   bit preload_aicore3_l1_start = 1'b0;
   bit preload_aicore4_l1_start = 1'b0;
   bit preload_aicore5_l1_start = 1'b0;
   bit preload_aicore6_l1_start = 1'b0;
   bit preload_aicore7_l1_start = 1'b0;
`ifndef AI_CORE_P_0_STUB
   `MEMORY_PRELOADING_AICORE_0_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_0.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm, hex_path, preload_aicore_0_spm_start)
   `MEMORY_PRELOADING_AICORE0_L1_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_0.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem, hex_path, preload_aicore0_l1_start)
`endif
`ifndef AI_CORE_P_1_STUB
   `MEMORY_PRELOADING_AICORE_1_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_1.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm, hex_path, preload_aicore_1_spm_start)
   `MEMORY_PRELOADING_AICORE1_L1_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_1.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem, hex_path, preload_aicore1_l1_start)
`endif
`ifndef AI_CORE_P_2_STUB
   `MEMORY_PRELOADING_AICORE_2_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_2.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm, hex_path, preload_aicore_2_spm_start)
   `MEMORY_PRELOADING_AICORE2_L1_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_2.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem, hex_path, preload_aicore2_l1_start)
`endif
`ifndef AI_CORE_P_3_STUB
   `MEMORY_PRELOADING_AICORE_3_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_3.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm, hex_path, preload_aicore_3_spm_start)
   `MEMORY_PRELOADING_AICORE3_L1_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_3.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem, hex_path, preload_aicore3_l1_start)
`endif
`ifndef AI_CORE_P_4_STUB
   `MEMORY_PRELOADING_AICORE_4_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_4.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm, hex_path, preload_aicore_4_spm_start)
   `MEMORY_PRELOADING_AICORE4_L1_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_4.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem, hex_path, preload_aicore4_l1_start)
`endif
`ifndef AI_CORE_P_5_STUB
   `MEMORY_PRELOADING_AICORE_5_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_5.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm, hex_path, preload_aicore_5_spm_start)
   `MEMORY_PRELOADING_AICORE5_L1_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_5.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem, hex_path, preload_aicore5_l1_start)
`endif
`ifndef AI_CORE_P_6_STUB
   `MEMORY_PRELOADING_AICORE_6_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_6.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm, hex_path, preload_aicore_6_spm_start)
   `MEMORY_PRELOADING_AICORE6_L1_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_6.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem, hex_path, preload_aicore6_l1_start)
`endif
`ifndef AI_CORE_P_7_STUB
   `MEMORY_PRELOADING_AICORE_7_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_7.u_ai_core.u_aic_infra_p.u_aic_infra.u_aic_spm, hex_path, preload_aicore_7_spm_start)
   `MEMORY_PRELOADING_AICORE7_L1_FILE(i_hdl_top.i_europa.u_aipu.u_ai_core_p_7.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem, hex_path, preload_aicore7_l1_start)
`endif
`ifndef PVE_P_0_STUB
  bit preload_pve_0_spm_start = 1'b0;
  bit preload_pve_0_l1_start = 1'b0;
  `MEMORY_PRELOADING_PVE_0_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_pve_p_0.u_pve.u_spm, hex_path, preload_pve_0_spm_start)
  `MEMORY_PRELOADING_PVE_0_L1_FILE(i_hdl_top.i_europa.u_aipu.u_pve_p_0.u_pve, hex_path, preload_pve_0_l1_start)
`endif
`ifndef PVE_P_1_STUB
  bit preload_pve_1_spm_start = 1'b0;
  bit preload_pve_1_l1_start = 1'b0;
  `MEMORY_PRELOADING_PVE_1_SPM_FILE(i_hdl_top.i_europa.u_aipu.u_pve_p_1.u_pve.u_spm, hex_path, preload_pve_1_spm_start)
  `MEMORY_PRELOADING_PVE_1_L1_FILE(i_hdl_top.i_europa.u_aipu.u_pve_p_1.u_pve, hex_path, preload_pve_1_l1_start)
`endif
  bit preload_l2_start = 1'b0;
`ifndef L2_P_0_STUB
  `MEMORY_PRELOADING_L2_FILE(i_hdl_top.i_europa.u_aipu.u_l2_p_0, 0, hex_path, preload_l2_start)
`endif
`ifndef L2_P_1_STUB
  `MEMORY_PRELOADING_L2_FILE(i_hdl_top.i_europa.u_aipu.u_l2_p_1, 1, hex_path, preload_l2_start)
`endif
`ifndef L2_P_2_STUB
  `MEMORY_PRELOADING_L2_FILE(i_hdl_top.i_europa.u_aipu.u_l2_p_2, 2, hex_path, preload_l2_start)
`endif
`ifndef L2_P_3_STUB
  `MEMORY_PRELOADING_L2_FILE(i_hdl_top.i_europa.u_aipu.u_l2_p_3, 3, hex_path, preload_l2_start)
`endif
`ifndef L2_P_4_STUB
  `MEMORY_PRELOADING_L2_FILE(i_hdl_top.i_europa.u_aipu.u_l2_p_4, 4, hex_path, preload_l2_start)
`endif
`ifndef L2_P_5_STUB
  `MEMORY_PRELOADING_L2_FILE(i_hdl_top.i_europa.u_aipu.u_l2_p_5, 5, hex_path, preload_l2_start)
`endif
`ifndef L2_P_6_STUB
  `MEMORY_PRELOADING_L2_FILE(i_hdl_top.i_europa.u_aipu.u_l2_p_6, 6, hex_path, preload_l2_start)
`endif
`ifndef L2_P_7_STUB
  `MEMORY_PRELOADING_L2_FILE(i_hdl_top.i_europa.u_aipu.u_l2_p_7, 7, hex_path, preload_l2_start)
`endif

  initial begin
    enable_instruction_dumping();
    fork
      begin : fork_start_uvm_test
        i_axe_clk_generator.set_clock(.freq_mhz(50), .duty(50));
        i_axe_clk_generator_spi_clk2x.set_clock(.freq_mhz(20), .duty(50));
        // TODO: @rodrigo.borges - remove when https://git.axelera.ai/prod/europa/-/issues/2367 is fixed
        `ifdef REAL_LPDDR
          i_axe_clk_generator_ref.set_clock(.freq_mhz(1200), .duty(50));
          i_axe_clk_generator_lpddr.set_clock(.freq_mhz(800), .duty(50));
        `else
          i_axe_clk_generator_ref.set_clock(.freq_mhz(50), .duty(50));
          i_axe_clk_generator_lpddr.set_clock(.freq_mhz(33.333), .duty(50));
        `endif  // !REAL_LPDDR
        clk_enable = 1;
        run_test();
      end
      begin : fork_preload_memories
        if ($value$plusargs("HEX_PATH=%s", hex_path)) begin
          $display("Preloading SYS SPM...");
          preload_sys_spm_start = 1'b1;
          $display("Preloading AICORE 0 SPM...");
          preload_aicore_0_spm_start = 1'b1;
          $display("Preloading AICORE 1 SPM...");
          preload_aicore_1_spm_start = 1'b1;
          $display("Preloading AICORE 2 SPM...");
          preload_aicore_2_spm_start = 1'b1;
          $display("Preloading AICORE 3 SPM...");
          preload_aicore_3_spm_start = 1'b1;
          $display("Preloading AICORE 4 SPM...");
          preload_aicore_4_spm_start = 1'b1;
          $display("Preloading AICORE 5 SPM...");
          preload_aicore_5_spm_start = 1'b1;
          $display("Preloading AICORE 6 SPM...");
          preload_aicore_6_spm_start = 1'b1;
          $display("Preloading AICORE 7 SPM...");
          preload_aicore_7_spm_start = 1'b1;
`ifndef PVE_P_0_STUB
          $display("Preloading PVE0 SPM...");
          preload_pve_0_spm_start = 1'b1;
          $display("Preloading PVE0 L1...");
          preload_pve_0_l1_start = 1'b1;
`endif
`ifndef PVE_P_1_STUB
          $display("Preloading PVE1 SPM...");
          preload_pve_1_spm_start = 1'b1;
          $display("Preloading PVE1 L1...");
          preload_pve_1_l1_start = 1'b1;
`endif
          $display("Preloading L2 ...");
          preload_l2_start = 1'b1;
`ifdef LPDDR_P_PPP_0_STUB
          `MEMORY_PRELOADING_FAKE_LPPDR_FILE(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_0.i_fake_lpddr.mem, hex_path,
                                             (~i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_0.i_fake_lpddr.rst))
`endif  // LPDDR_P_PPP_0_STUB
          $display("Preloading AICORE0 L1...");
          preload_aicore0_l1_start = 1'b1;
          $display("Preloading AICORE1 L1...");
          preload_aicore1_l1_start = 1'b1;
          $display("Preloading AICORE2 L1...");
          preload_aicore2_l1_start = 1'b1;
          $display("Preloading AICORE3 L1...");
          preload_aicore3_l1_start = 1'b1;
          $display("Preloading AICORE4 L1...");
          preload_aicore4_l1_start = 1'b1;
          $display("Preloading AICORE5 L1...");
          preload_aicore5_l1_start = 1'b1;
          $display("Preloading AICORE6 L1...");
          preload_aicore6_l1_start = 1'b1;
          $display("Preloading AICORE7 L1...");
          preload_aicore7_l1_start = 1'b1;
        end else begin
          $fatal(1, "HEX_PATH plusarg not set, cannot preload memories");
        end
      end
    join
  end

  //copy ROM code to secure enclave
`ifndef SOC_MGMT_P_STUB
  initial
    begin   : rom_initl_blk
      string sec_rom;
      if (!$value$plusargs("SEC_ROM_FILE=%s", sec_rom))
        `uvm_fatal("top_th", "SEC_ROM_FILE plusarg is not set !")
      $readmemh(sec_rom, i_hdl_top.i_europa.u_aipu.u_soc_mgmt_p.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kudelski_kse3_rom.memory_q);
    end
`endif

  // LPDDR PHY Bring up power supplies
  // As done in /data/foundry/LIB/synopsys/lpddr5x/ss4/ws_snps_ddr_subsystem/sim/testbench/modules/dwc_ddrctl_ddr_chip_wrapper.sv
`define LPDDR_PHY_BRING_UP_POWER_SUPPLIES(lpddr_path)  \
  begin  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDD           = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_ZCAL     = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB0_DX0  = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB0_DX1  = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB1_DX0  = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB1_DX1  = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB2_DX0  = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB2_DX1  = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB3_DX0  = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB3_DX1  = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_ACX0 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_ACX1 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_ACX2 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_ACX3 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_CKX0 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_ACX0 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_ACX1 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_ACX2 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_ACX3 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_CKX0 = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDD2H         = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VAA           = 0;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VSS           = 0;  \
    #100;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDD           = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_ZCAL     = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB0_DX0  = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB0_DX1  = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB1_DX0  = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB1_DX1  = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB2_DX0  = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB2_DX1  = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB3_DX0  = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_DB3_DX1  = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_ACX0 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_ACX1 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_ACX2 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_ACX3 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC0_CKX0 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_ACX0 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_ACX1 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_ACX2 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_ACX3 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDDQ_AC1_CKX0 = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VDD2H         = 1;  \
    force ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.VAA           = 1;  \
  end

  initial begin

    fork
      `ifndef LPDDR_P_PPP_0_STUB
        `LPDDR_PHY_BRING_UP_POWER_SUPPLIES(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_0)
      `endif
      `ifndef LPDDR_P_PPP_1_STUB
        `LPDDR_PHY_BRING_UP_POWER_SUPPLIES(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_1)
      `endif
      `ifndef LPDDR_P_PPP_2_STUB
        `LPDDR_PHY_BRING_UP_POWER_SUPPLIES(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_2)
      `endif
      `ifndef LPDDR_P_PPP_3_STUB
        `LPDDR_PHY_BRING_UP_POWER_SUPPLIES(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_3)
      `endif
      `ifndef LPDDR_P_GRAPH_0_STUB
        // TODO: @rodrigo.borges - remove when https://git.axelera.ai/prod/europa/-/issues/2367 is fixed
        force i_hdl_top.i_europa.u_aipu.u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk = lpddr_clk;
        `LPDDR_PHY_BRING_UP_POWER_SUPPLIES(i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0)
      `endif
      `ifndef LPDDR_P_GRAPH_1_STUB
        `LPDDR_PHY_BRING_UP_POWER_SUPPLIES(i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_1)
      `endif
      `ifndef LPDDR_P_GRAPH_2_STUB
        `LPDDR_PHY_BRING_UP_POWER_SUPPLIES(i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_2)
      `endif
      `ifndef LPDDR_P_GRAPH_3_STUB
        `LPDDR_PHY_BRING_UP_POWER_SUPPLIES(i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_3)
      `endif
    join

    `ifndef LPDDR_P_PPP_0_STUB
      `LPDDR_PHY_SRAM_PRELOADING(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_0)
    `endif
    `ifndef LPDDR_P_PPP_1_STUB
      `LPDDR_PHY_SRAM_PRELOADING(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_1)
    `endif
    `ifndef LPDDR_P_PPP_2_STUB
      `LPDDR_PHY_SRAM_PRELOADING(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_2)
    `endif
    `ifndef LPDDR_P_PPP_3_STUB
      `LPDDR_PHY_SRAM_PRELOADING(i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_3)
    `endif
    `ifndef LPDDR_P_GRAPH_0_STUB
      `LPDDR_PHY_SRAM_PRELOADING(i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0)
    `endif
    `ifndef LPDDR_P_GRAPH_1_STUB
      `LPDDR_PHY_SRAM_PRELOADING(i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_1)
    `endif
    `ifndef LPDDR_P_GRAPH_2_STUB
      `LPDDR_PHY_SRAM_PRELOADING(i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_2)
    `endif
    `ifndef LPDDR_P_GRAPH_3_STUB
      `LPDDR_PHY_SRAM_PRELOADING(i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_3)
    `endif

  end


  // preload emmc registers
`ifdef TARGET_EMMC_SOFTMODEL
  `include "preload_emmc_softmodel.sv"

  initial begin
    preload_emmc_softmodel();
  end
`endif

`ifdef TARGET_SPINOR_S25FS512S
  assign i_hdl_top.spi_clk2x = spi_clk2x;
  initial begin
    string spinor_mem_filename;
    string spinor_reg_filename;
    if (!$value$plusargs("SPINOR_MEMFILE=%s", spinor_mem_filename)) begin
        `uvm_warning("spinor_preload", "SPINOR_MEMFILE was not provided!")
    end else begin
      `uvm_info("spinor_preload", $sformatf("Loading spinor mem from: %s", spinor_mem_filename), UVM_LOW)
      $readmemh(spinor_mem_filename, i_hdl_top.i_spi_softmodel.sf_core.mem_0.i_memArray);
    end

    if (!$value$plusargs("SPINOR_REGFILE=%s", spinor_reg_filename)) begin
        `uvm_fatal("spinor_preload", "SPINOR_REGFILE was not provided!")
    end else begin
      `uvm_info("spinor_preload", $sformatf("Loading spinor regs from: %s", spinor_reg_filename), UVM_LOW)
      $readmemh(spinor_reg_filename, i_hdl_top.i_spi_softmodel.sf_core.sf_ID_mem.SFDP_CFI_ARRAY);
    end

  end
`endif

  // use same dut as Veloce, reset happens inside hdl_top
  hdl_top i_hdl_top ();

endmodule
