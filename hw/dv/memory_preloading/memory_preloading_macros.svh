// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner:

// memory_preloading_macros.svh
`ifndef MEMORY_PRELOADING_MACROS_SVH
`define MEMORY_PRELOADING_MACROS_SVH

//----------------------------------
// SPM preloading macros
//----------------------------------

// SPM memory path macro
`define SPM_MINIBANK_PATH(mem_path, bk, sb, mb,
                          inst) \
  ``mem_path``.u_spm_mem.g_bank_inst[``bk``].u_spm_mem_bank.g_sub_bank_inst[``sb``].u_spm_mem_sub_bank.g_mini_bank_inst[``mb``].u_spm_mem_mini_bank.g_sram_inst[``inst``].u_tc_sram.memory_q

`define PRELOAD_SPM_MINIBANK_FILE(mem_name, elf_file, mem_path, bk, sb, mb, inst)                                                          \
  begin                                                                                                                                    \
    string mem_file;                                                                                                                       \
    string mem_desc = $sformatf("%s[BK: %0d, SB: %0d, MB: %0d, INST: %0d]", ``mem_name``, ``bk``, ``sb``, ``mb``, ``inst``);               \
    $display("Preload: %s", mem_desc);                                                                                                     \
    `SPM_MINIBANK_PATH(``mem_path``, ``bk``, ``sb``, ``mb``, ``inst``) = '{default: '0};                                                   \
    mem_file = $sformatf("%s.%s.bk_%0d.sb_%0d.mb_%0d.inst_%0d.64b.texthex", ``elf_file``, ``mem_name``, ``bk``, ``sb``, ``mb``, ``inst``); \
    if (file_exists(mem_file)) begin                                                                                                       \
      $readmemh(mem_file, `SPM_MINIBANK_PATH(``mem_path``, ``bk``, ``sb``, ``mb``, ``inst``));                                             \
    end else begin                                                                                                                         \
      $fatal(1, "Preload %s: file does not exist: %s", mem_desc, mem_file);                                                                \
    end                                                                                                                                    \
  end

// Preload SPM functional model using a hex file
// Iterate over all banks (bk), sub-banks (sb), mini-banks (mb) and instances(inst) for SPM preloading
`define MEMORY_PRELOADING_SPM_FILE(mem_name, elf_file, mem_path, nb_bk, nb_sb, nb_mb, nb_inst,
                                   preload_en) \
  for (genvar bk = 0; bk < ``nb_bk``; bk++) begin                                       \
    for (genvar sb = 0; sb < ``nb_sb``; sb++) begin                                     \
      for (genvar mb = 0; mb < ``nb_mb``; mb++) begin                                   \
        for (genvar inst = 0; inst < ``nb_inst``; inst++) begin                         \
          initial begin                                                                                   \
            wait (``preload_en`` === 1'b1);                                                               \
            `PRELOAD_SPM_MINIBANK_FILE(``mem_name``,``elf_file``, ``mem_path``, bk, sb, mb, inst);        \
          end                                                                                             \
        end                                                                                               \
      end                                                                                                 \
    end                                                                                                   \
  end

// Preload SYS-SPM for static memory arrays like i_hdl_top.i_dv_axi_ram.mem
`define MEMORY_PRELOADING_FAKE_SYS_SPM_FILE(mem_path, elf_file, preload_en, start_offset)  \
  begin                                                                                    \
    string mem_file;                                                                       \
    wait(``preload_en``==1'b1);                                                            \
    $display("Preloading SYS-SPM...");                                                     \
    ``mem_path`` = '{default: '0};                                                         \
    mem_file = $sformatf("%s.sys_spm.64b.texthex", ``elf_file``);                          \
    if (file_exists(mem_file)) begin                                                       \
      $display("Preloading from file: %s", mem_file);                                      \
      $readmemh(mem_file, ``mem_path``, ``start_offset``);                                 \
    end else begin                                                                         \
      $fatal(1, "Preload failed: file does not exist: %s", mem_file);                      \
    end                                                                                    \
  end

// Preload AICORE-SPM for static memory arrays
`define MEMORY_PRELOADING_FAKE_AICORE_SPM_FILE(mem_path, elf_file, preload_en)  \
  begin                                                                         \
    string mem_file;                                                            \
    wait(``preload_en``==1'b1);                                                 \
    $display("Preloading AICORE-SPM...");                                       \
    ``mem_path`` = '{default: '0};                                              \
    mem_file = $sformatf("%s.aicore_0.spm.64b.texthex", ``elf_file``);          \
    if (file_exists(mem_file)) begin                                            \
      $display("Preloading from file: %s", mem_file);                           \
      $readmemh(mem_file, ``mem_path``);                                        \
    end else begin                                                              \
      $fatal(1, "Preload failed: file does not exist: %s", mem_file);           \
    end                                                                         \
  end

// Preload SYS SPM loop macro
// Iterate over all banks (bk), sub-banks (sb), mini-banks (mb) and instances(inst) for SYS SPM preloading
`define MEMORY_PRELOADING_SYS_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("sys_spm", ``elf_file``, ``mem_path``, 4, 4, 4, 2, ``preload_en``)


// Preload PVE SPM loop macro
// Iterate over all banks (bk), sub-banks (sb), mini-banks (mb) and instances(inst) for PVE SPM preloading
`define MEMORY_PRELOADING_PVE_0_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("pve_0.spm", ``elf_file``, ``mem_path``, 2, 2, 2, 2, ``preload_en``)
`define MEMORY_PRELOADING_PVE_1_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("pve_1.spm", ``elf_file``, ``mem_path``, 2, 2, 2, 2, ``preload_en``)

// Preload AICORE SPM loop macro
// Iterate over all banks (bk), sub-banks (sb), mini-banks (mb) and instances(inst) for AICORE SPM preloading
`define MEMORY_PRELOADING_AICORE_0_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("aicore_0.spm", ``elf_file``, ``mem_path``, 2, 1, 2, 2, ``preload_en``)
`define MEMORY_PRELOADING_AICORE_1_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("aicore_1.spm", ``elf_file``, ``mem_path``, 2, 1, 2, 2, ``preload_en``)
`define MEMORY_PRELOADING_AICORE_2_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("aicore_2.spm", ``elf_file``, ``mem_path``, 2, 1, 2, 2, ``preload_en``)
`define MEMORY_PRELOADING_AICORE_3_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("aicore_3.spm", ``elf_file``, ``mem_path``, 2, 1, 2, 2, ``preload_en``)
`define MEMORY_PRELOADING_AICORE_4_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("aicore_4.spm", ``elf_file``, ``mem_path``, 2, 1, 2, 2, ``preload_en``)
`define MEMORY_PRELOADING_AICORE_5_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("aicore_5.spm", ``elf_file``, ``mem_path``, 2, 1, 2, 2, ``preload_en``)
`define MEMORY_PRELOADING_AICORE_6_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("aicore_6.spm", ``elf_file``, ``mem_path``, 2, 1, 2, 2, ``preload_en``)
`define MEMORY_PRELOADING_AICORE_7_SPM_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_SPM_FILE("aicore_7.spm", ``elf_file``, ``mem_path``, 2, 1, 2, 2, ``preload_en``)

//----------------------------------
// L1 preloading macros
//----------------------------------

// L1 memory path macro
`define L1_MINIBANK_PATH(mem_path, sb,
                         mb) \
    ``mem_path``.g_sbank[``sb``].u_sub_bank.g_mini_bank[``mb``].u_mini_bank.g_macro[0].u_macro.memory_q

// Preload a single l1 minibank from a file
`define PRELOAD_L1_MINIBANK_FILE(mem_name, elf_file, mem_path, sb, mb)                                    \
  begin                                                                                                   \
    string mem_file;                                                                                      \
    string mem_desc = $sformatf("%s[SB: %0d, MB: %0d]", ``mem_name``, ``sb``, ``mb``);                    \
    $display("Preload: %s", mem_desc);                                                                    \
    `L1_MINIBANK_PATH(``mem_path``, ``sb``, ``mb``) = '{default: '0};                                     \
    mem_file = $sformatf("%s.%s.sb_%0d.mb_%0d.128b.texthex", ``elf_file``, ``mem_name``, ``sb``, ``mb``); \
    if (file_exists(mem_file)) begin                                                                      \
      $readmemh(mem_file, `L1_MINIBANK_PATH(``mem_path``, ``sb``, ``mb``));                               \
    end else begin                                                                                        \
      $fatal(1, "Preload %s: file does not exist: %s", mem_desc, mem_file);                               \
    end                                                                                                   \
  end

// Preload PVE L1 functional model
// Iterate over all sub-banks (sb) and mini-banks (mb) for L1 preloading
`define MEMORY_PRELOADING_L1_FILE(mem_name, elf_file, mem_path, nb_sb, nb_mb, preload_en) \
  for (genvar sb = 0; sb < ``nb_sb``; sb++) begin                                         \
    for (genvar mb = 0; mb < ``nb_mb``; mb++) begin                                       \
      initial begin                                                                       \
        wait (``preload_en`` === 1'b1);                                                   \
        `PRELOAD_L1_MINIBANK_FILE(``mem_name``, ``elf_file``, ``mem_path``, sb, mb);      \
      end                                                                                 \
    end                                                                                   \
  end

// Preload PVE_0 L1_0 macro
`define MEMORY_PRELOADING_PVE_0_L1_0_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("pve_0.l1_0", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)

// Preload PVE_0 L1 macro
// For all clusters we preload the same data as the execute the same workload.
`define MEMORY_PRELOADING_PVE_0_L1_FILE(core_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("pve_0.l1_0", ``elf_file``, core_path``.g_cluster[0].u_cluster.u_pve_l1.u_pve_l1.u_l1.u_l1_mem, 4, 16, ``preload_en``) \
  `MEMORY_PRELOADING_L1_FILE("pve_0.l1_0", ``elf_file``, core_path``.g_cluster[1].u_cluster.u_pve_l1.u_pve_l1.u_l1.u_l1_mem, 4, 16, ``preload_en``) \
  `MEMORY_PRELOADING_L1_FILE("pve_0.l1_0", ``elf_file``, core_path``.g_cluster[2].u_cluster.u_pve_l1.u_pve_l1.u_l1.u_l1_mem, 4, 16, ``preload_en``) \
  `MEMORY_PRELOADING_L1_FILE("pve_0.l1_0", ``elf_file``, core_path``.g_cluster[3].u_cluster.u_pve_l1.u_pve_l1.u_l1.u_l1_mem, 4, 16, ``preload_en``) \

// Preload PVE_1 L1 macro
// For all clusters we preload the same data as the execute the same workload.
`define MEMORY_PRELOADING_PVE_1_L1_FILE(core_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("pve_1.l1_0", ``elf_file``, core_path``.g_cluster[0].u_cluster.u_pve_l1.u_pve_l1.u_l1.u_l1_mem, 4, 16, ``preload_en``) \
  `MEMORY_PRELOADING_L1_FILE("pve_1.l1_0", ``elf_file``, core_path``.g_cluster[1].u_cluster.u_pve_l1.u_pve_l1.u_l1.u_l1_mem, 4, 16, ``preload_en``) \
  `MEMORY_PRELOADING_L1_FILE("pve_1.l1_0", ``elf_file``, core_path``.g_cluster[2].u_cluster.u_pve_l1.u_pve_l1.u_l1.u_l1_mem, 4, 16, ``preload_en``) \
  `MEMORY_PRELOADING_L1_FILE("pve_1.l1_0", ``elf_file``, core_path``.g_cluster[3].u_cluster.u_pve_l1.u_pve_l1.u_l1.u_l1_mem, 4, 16, ``preload_en``) \

// Preload AICORE L1 macro
`define MEMORY_PRELOADING_AICORE0_L1_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("aicore_0.l1", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)
`define MEMORY_PRELOADING_AICORE1_L1_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("aicore_1.l1", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)
`define MEMORY_PRELOADING_AICORE2_L1_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("aicore_2.l1", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)
`define MEMORY_PRELOADING_AICORE3_L1_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("aicore_3.l1", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)
`define MEMORY_PRELOADING_AICORE4_L1_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("aicore_4.l1", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)
`define MEMORY_PRELOADING_AICORE5_L1_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("aicore_5.l1", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)
`define MEMORY_PRELOADING_AICORE6_L1_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("aicore_6.l1", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)
`define MEMORY_PRELOADING_AICORE7_L1_FILE(mem_path, elf_file, preload_en) \
  `MEMORY_PRELOADING_L1_FILE("aicore_7.l1", ``elf_file``, ``mem_path``, 4, 16, ``preload_en``)

//----------------------------------
// L2 preloading macros
//----------------------------------

// L2 memory path macro
`define L2_SRAM_PATH(mem_path, bank, ram, sram) \
  ``mem_path``.u_l2_impl.u_l2_gdr.u_l2_mem.g_bank[``bank``].u_l2_bank.g_ram[``ram``].u_l2_ram.g_sram[``sram``].u_l2_ram_wrapper.memory_q

// Preload a single l2 sram from a file
`define PRELOAD_L2_SRAM_FILE(elf_file, mem_path, l2_module, bank, ram, sram)                                                                   \
  begin                                                                                                                                        \
    string mem_file;                                                                                                                           \
    string mem_desc = $sformatf("L2[module: %0d, bank: %0d, ram: %0d, sram: %0d]", ``l2_module``, ``bank``, ``ram``, ``sram``);                \
    $display("Preload: %s", mem_desc);                                                                                                         \
    `L2_SRAM_PATH(``mem_path``, ``bank``, ``ram``, ``sram``) = '{default: '0};                                                  \
    mem_file = $sformatf("%s.l2.module_%0d.bank_%0d.ram_%0d.sram_%0d.128b.texthex", ``elf_file``, ``l2_module``, ``bank``, ``ram``, ``sram``); \
    if (file_exists(mem_file)) begin                                                                                                           \
      $readmemh(mem_file, `L2_SRAM_PATH(``mem_path``, ``bank``, ``ram``, ``sram``));                                            \
    end else begin                                                                                                                             \
      $fatal(1, "Preload %s: file does not exist: %s", mem_desc, mem_file);                                                                    \
    end                                                                                                                                        \
  end

// Preload top L2 functional model
// Iterate over all bank/ram/sram
`define MEMORY_PRELOADING_L2_FILE(mem_path, l2_module, elf_file, preload_en)                 \
  for (genvar bank = 0; bank < 16; bank++) begin                                             \
    for (genvar ram = 0; ram < 4; ram++) begin                                               \
      for (genvar sram = 0; sram < 4; sram++) begin                                          \
        initial begin                                                                        \
          wait (``preload_en`` === 1'b1);                                                    \
          `PRELOAD_L2_SRAM_FILE(``elf_file``, ``mem_path``, ``l2_module``, bank, ram, sram); \
        end                                                                                  \
      end                                                                                    \
    end                                                                                      \
  end

//----------------------------------
// LPDDR preloading macros
//----------------------------------

// Preload FAKE_LPDDR for static memory arrays like i_hdl_top.i_fake_lpddr_ppp_0.mem
// TODO: add preloading for other lpddr modules as they come in to the top-level.
`define MEMORY_PRELOADING_FAKE_LPPDR_FILE(mem_path, elf_file, preload_en) \
  begin                                                                   \
    string mem_file;                                                      \
    wait(``preload_en``==1'b1);                                           \
    $display("Preloading FAKE LPDDR...");                                 \
    ``mem_path`` = '{default: '0};                                        \
    mem_file = $sformatf("%s.ddr_1.256b.texthex", ``elf_file``);          \
    if (file_exists(mem_file)) begin                                      \
      $display("Preloading from file: %s", mem_file);                     \
      $readmemh(mem_file, ``mem_path``);                                  \
    end else begin                                                        \
      $fatal(1, "Preload failed: file does not exist: %s", mem_file);     \
    end                                                                   \
  end

`endif  // MEMORY_PRELOADING_MACROS_SVH

  // LPDDR PHY SRAMs preloading
  // TODO: Currently this is not in use since PRELOAD_LPDDR_ICCM is not used and still confirming backdoor implementation/confirmation with Synospys
  // Desire is for file to be defined by PRELOAD_LPDDR_ICCM instead of using absolute paths that we have now.
`define LPDDR_PHY_SRAM_PRELOADING(lpddr_path)  \
begin  \
    string iccm_mem;  \
    wait(``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.Reset == 1'b0 && ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.BP_PWROK == 1'b1 );  \
    if ($value$plusargs("PRELOAD_LPDDR_ICCM=%s", iccm_mem)) begin  \
      repeat (70) begin  \
        @(posedge ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DfiClk);  \
      end  \
      $display("LPDDR PHY SRAMs [ICCM]: Loading file %s", "$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank0_ecc_0.txt");  \
      ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_ddrphy_mem_wrap.genblock_iccm0[0].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.u_mem.load_mem("$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank0_ecc_0.txt");  \
      $display("LPDDR PHY SRAMs [ICCM]: Loading file %s", "$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank0_ecc_1.txt");  \
      ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_ddrphy_mem_wrap.genblock_iccm0[1].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.u_mem.load_mem("$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank0_ecc_1.txt");  \
      $display("LPDDR PHY SRAMs [ICCM]: Loading file %s", "$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank0_ecc_2.txt");  \
      ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_ddrphy_mem_wrap.genblock_iccm0[2].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.u_mem.load_mem("$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank0_ecc_2.txt");  \
      $display("LPDDR PHY SRAMs [ICCM]: Loading file %s", "$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank0_ecc_3.txt");  \
      ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_ddrphy_mem_wrap.genblock_iccm0[3].i_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.u_mem.load_mem("$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank0_ecc_3.txt");  \
      $display("LPDDR PHY SRAMs [ICCM]: Loading file %s", "$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank1_ecc_0.txt");  \
      ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_ddrphy_mem_wrap.genblock_iccm1[0].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.u_mem.load_mem("$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank1_ecc_0.txt");  \
      $display("LPDDR PHY SRAMs [ICCM]: Loading file %s", "$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank1_ecc_1.txt");  \
      ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_ddrphy_mem_wrap.genblock_iccm1[1].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.u_mem.load_mem("$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank1_ecc_1.txt");  \
      $display("LPDDR PHY SRAMs [ICCM]: Loading file %s", "$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank1_ecc_2.txt");  \
      ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_ddrphy_mem_wrap.genblock_iccm1[2].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.u_mem.load_mem("$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank1_ecc_2.txt");  \
      $display("LPDDR PHY SRAMs [ICCM]: Loading file %s", "$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank1_ecc_3.txt");  \
      ``lpddr_path``.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_ddrphy_mem_wrap.genblock_iccm1[3].i_iccm1_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.u_mem.load_mem("$REPO_ROOT/sw/src/lib/ax65/drv/lpddr/iccm_preload_fw/lpddr5_pmu_train_imem_bank1_ecc_3.txt");  \
    end  \
  end
