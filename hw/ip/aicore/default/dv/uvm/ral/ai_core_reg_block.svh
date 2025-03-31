class ai_core_top_reg_block extends dv_base_reg_block;
    // Registration with factory
    `uvm_object_utils(ai_core_top_reg_block)
    // RAL models objects
    //rand ai_core_cfg_csr_reg_block csr_regmod;
    rand ifd_csr_reg_block                   m_ifd0_regmod;
    rand ifd_csr_reg_block                   m_ifd1_regmod;
    rand ifd_csr_reg_block                   m_ifd2_regmod;
    rand ifd_csr_reg_block                   m_ifdw_regmod;
    rand odr_csr_reg_block                   m_odr_regmod;
    rand ifd_csr_reg_block                   d_ifd0_regmod;
    rand ifd_csr_reg_block                   d_ifd1_regmod;
    rand odr_csr_reg_block                   d_odr_regmod;
    rand mvmexe_csr_reg_block                m_mvmexe_regmod;
    rand mvmprg_csr_reg_block                m_mvmprg_regmod;
    rand iau_csr_reg_block                   m_iau_regmod;
    rand iau_csr_reg_block                   d_iau_regmod;
    rand dpu_csr_reg_block                   m_dpu_regmod;
    rand dpu_csr_reg_block                   d_dpu_regmod;
    rand dwpu_csr_reg_block                  d_dwpu_regmod;
    rand axi_mailbox_csr_reg_block           axi4_mbox_regmod;
    rand token_manager_aic_csr_reg_block     tkn_manager_regmod;
    rand aic_csr_reg_block                   infra_periph_regmod;
    rand aic_csr_mid_part_reg_block          mid_periph_regmod;
    rand timestamp_logger_csr_reg_block      timestamp_logger_regmod;
    rand aic_lt_dw_axi_dmac_reg_block        aic_lp_dma_regmod;
    //rand aic_ht_dw_axi_dmac_reg_block      aic_hp_dma0_regmod;
    //rand aic_ht_dw_axi_dmac_reg_block      aic_hp_dma1_regmod;
    rand aic_ht_dw_axi_dmac_reg_block        aic_hp_dma_regmod;
    rand aic_rv_plic_reg_block               aic_rv_plic_regmod;
    rand aic_cd_csr_reg_block                aic_acd_regmod;


    uvm_reg_block                  m_reg_blocks[`AI_CORE_REGMOD_NUM]; 

    // Reg map object
    uvm_reg_map ai_core_top_map;

    // Class construcotr
    function new(string name = "ai_core_top_reg_block");
      super.new(name);
    endfunction: new

   // Provide build function to supply base addr
   function void build(uvm_reg_addr_t base_addr, csr_excl_item csr_excl = null);

      // Map definition
      ai_core_top_map = create_map(
        .name           ("default_map"),
        .base_addr      (0),
        .n_bytes        (8),
        .endian         (UVM_LITTLE_ENDIAN),
        .byte_addressing(0)
      );
      default_map    = ai_core_top_map;
      $display("KSC RAL =%0h",base_addr);
      
       // AI Core Token Manager RAL model Build
      //this.csr_regmod = ai_core_cfg_csr_reg_block::type_id::create("csr_regmod",,get_full_name());
      //this.csr_regmod.configure(this, "AI_CORE_CSR_CSR");
      //this.csr_regmod.build(null);
      //// Map definition
      //ai_core_top_map.add_submap(csr_regmod.default_map, base_addr + `AI_CORE_CSR_BASE_ADDR);
      //this.csr_regmod.lock_model();
      //m_reg_blocks[0] = csr_regmod;
      // AI Core  M_IFD0 RAL model Build
      this.m_ifd0_regmod = ifd_csr_reg_block::type_id::create("m_ifd0_regmod",,get_full_name());
      this.m_ifd0_regmod.configure(this, "AI_CORE_TOP_M_IFD0_CSR");
      this.m_ifd0_regmod.build(null);
      ai_core_top_map.add_submap(m_ifd0_regmod.default_map, base_addr + `M_IFD0_CSR_BASE_ADDR);
      this.m_ifd0_regmod.lock_model();
      m_reg_blocks[0] = m_ifd0_regmod;

      // AI Core  M_IFD1 RAL model Build
      this.m_ifd1_regmod = ifd_csr_reg_block::type_id::create("m_ifd1_regmod",,get_full_name());
      this.m_ifd1_regmod.configure(this, "AI_CORE_TOP_M_IFD1_CSR");
      this.m_ifd1_regmod.build(null);
      // Map definition
      ai_core_top_map.add_submap(m_ifd1_regmod.default_map, base_addr +  `M_IFD1_CSR_BASE_ADDR);
      this.m_ifd1_regmod.lock_model();
      m_reg_blocks[1] = m_ifd1_regmod;

      // AI Core  M_IFD2 RAL model Build
      this.m_ifd2_regmod = ifd_csr_reg_block::type_id::create("m_ifd2_regmod",,get_full_name());
      this.m_ifd2_regmod.configure(this, "AI_CORE_TOP_M_IFD2_CSR");
      this.m_ifd2_regmod.build(null);
      // Map definition
      ai_core_top_map.add_submap(m_ifd2_regmod.default_map, base_addr +  `M_IFD2_CSR_BASE_ADDR);
      this.m_ifd2_regmod.lock_model();
      m_reg_blocks[2] = m_ifd2_regmod;


      // AI Core  M_IFDW RAL model Build
      this.m_ifdw_regmod = ifd_csr_reg_block::type_id::create("m_ifdw_regmod",,get_full_name());
      this.m_ifdw_regmod.configure(this, "AI_CORE_TOP_M_IFDW_CSR");
      this.m_ifdw_regmod.build(null);
      // Map definition
      ai_core_top_map.add_submap(m_ifdw_regmod.default_map, base_addr + `M_IFDW_CSR_BASE_ADDR);
      this.m_ifdw_regmod.lock_model();
      m_reg_blocks[3] = m_ifdw_regmod;

      // AI Core  D_IFD0 RAL model Build
      this.d_ifd0_regmod = ifd_csr_reg_block::type_id::create("d_ifd0_regmod",,get_full_name());
      this.d_ifd0_regmod.configure(this, "AI_CORE_TOP_D_IFD0_CSR");
      this.d_ifd0_regmod.build(null);
      // Map definition
      ai_core_top_map.add_submap(d_ifd0_regmod.default_map, base_addr + `D_IFD0_CSR_BASE_ADDR);
      this.d_ifd0_regmod.lock_model();
      m_reg_blocks[4] = d_ifd0_regmod;

      // AI Core  D_IFD1 RAL model Build
      this.d_ifd1_regmod = ifd_csr_reg_block::type_id::create("d_ifd1_regmod",,get_full_name());
      this.d_ifd1_regmod.configure(this, "AI_CORE_TOP_IFD1_CSR");
      this.d_ifd1_regmod.build(null);
      // Map definition
      ai_core_top_map.add_submap(d_ifd1_regmod.default_map, base_addr + `D_IFD1_CSR_BASE_ADDR);
      this.d_ifd1_regmod.lock_model();
      m_reg_blocks[5] = d_ifd1_regmod;

      // AI Core  M_ODR RAL model Build
      this.m_odr_regmod = odr_csr_reg_block::type_id::create("m_odr_regmod",,get_full_name());
      this.m_odr_regmod.configure(this, "AI_CORE_TOP_M_ODR_CSR");
      this.m_odr_regmod.build(null);
      // Map definition
      ai_core_top_map.add_submap(m_odr_regmod.default_map, base_addr + `M_ODR_CSR_BASE_ADDR);
      this.m_odr_regmod.lock_model();
      m_reg_blocks[6] = m_odr_regmod;

      // AI Core  D_ODR RAL model Build
      this.d_odr_regmod = odr_csr_reg_block::type_id::create("d_odr_regmod",,get_full_name());
      this.d_odr_regmod.configure(this, "AI_CORE_TOP_D_ODR_CSR");
      this.d_odr_regmod.build(null);
      // Map definition
      ai_core_top_map.add_submap(d_odr_regmod.default_map, base_addr + `D_ODR_CSR_BASE_ADDR);
      this.d_odr_regmod.lock_model();
      m_reg_blocks[7] = d_odr_regmod;

      this.m_mvmexe_regmod = mvmexe_csr_reg_block::type_id::create("m_mvmexe_regmod",,get_full_name());
      this.m_mvmexe_regmod.configure(this, "AI_CORE_TOP_MVMEXE_CSR");
      this.m_mvmexe_regmod.build(null);
      ai_core_top_map.add_submap(m_mvmexe_regmod.default_map, base_addr + `M_MVMEXE_CSR_BASE_ADDR);
      this.m_mvmexe_regmod.lock_model();
      m_reg_blocks[8] = m_mvmexe_regmod;

      this.m_mvmprg_regmod = mvmprg_csr_reg_block::type_id::create("m_mvmprg_regmod",,get_full_name());
      this.m_mvmprg_regmod.configure(this, "AI_CORE_TOP_MVMPRG_CSR");
      this.m_mvmprg_regmod.build(null);
      ai_core_top_map.add_submap(m_mvmprg_regmod.default_map, base_addr + `M_MVMPRG_CSR_BASE_ADDR);
      this.m_mvmprg_regmod.lock_model();
      m_reg_blocks[9] = m_mvmprg_regmod;

      this.m_iau_regmod = iau_csr_reg_block::type_id::create("m_iau_regmod",,get_full_name());
      this.m_iau_regmod.configure(this, "AI_CORE_TOP_M_IAU_CSR");
      this.m_iau_regmod.build(null);
      ai_core_top_map.add_submap(m_iau_regmod.default_map, base_addr + `M_IAU_CSR_BASE_ADDR);
      this.m_iau_regmod.lock_model();
      m_reg_blocks[10] = m_iau_regmod;

      this.d_iau_regmod = iau_csr_reg_block::type_id::create("d_iau_regmod",,get_full_name());
      this.d_iau_regmod.configure(this, "AI_CORE_TOP_D_IAU_CSR");
      this.d_iau_regmod.build(null);
      ai_core_top_map.add_submap(d_iau_regmod.default_map, base_addr + `D_IAU_CSR_BASE_ADDR);
      this.d_iau_regmod.lock_model();
      m_reg_blocks[11] = d_iau_regmod;

      this.m_dpu_regmod = dpu_csr_reg_block::type_id::create("m_dpu_regmod",,get_full_name());
      this.m_dpu_regmod.configure(this, "AI_CORE_TOP_M_DPU_CSR");
      this.m_dpu_regmod.build(null);
      ai_core_top_map.add_submap(m_dpu_regmod.default_map, base_addr + `M_DPU_CSR_BASE_ADDR);
      this.m_dpu_regmod.lock_model();
      m_reg_blocks[12] = m_dpu_regmod;

      this.d_dpu_regmod = dpu_csr_reg_block::type_id::create("d_dpu_regmod",,get_full_name());
      this.d_dpu_regmod.configure(this, "AI_CORE_TOP_D_DPU_CSR");
      this.d_dpu_regmod.build(null);
      ai_core_top_map.add_submap(d_dpu_regmod.default_map, base_addr + `D_DPU_CSR_BASE_ADDR);
      this.d_iau_regmod.lock_model();
      m_reg_blocks[13] = d_dpu_regmod;

      this.d_dwpu_regmod = dwpu_csr_reg_block::type_id::create("d_dwpu_regmod",,get_full_name());
      this.d_dwpu_regmod.configure(this, "AI_CORE_TOP_D_DWPU_CSR");
      this.d_dwpu_regmod.build(null);
      ai_core_top_map.add_submap(d_dwpu_regmod.default_map, base_addr + `D_DWPU_CSR_BASE_ADDR);
      this.d_dwpu_regmod.lock_model();
      m_reg_blocks[14] = d_dwpu_regmod;

      //axi4 mailbox
      this.axi4_mbox_regmod = axi_mailbox_csr_reg_block::type_id::create("axi4_mbox_regmod",,get_full_name());
      this.axi4_mbox_regmod.configure(this, "AI_CORE_TOP_MBOX_CSR");
      this.axi4_mbox_regmod.build(null);
      ai_core_top_map.add_submap(axi4_mbox_regmod.default_map, base_addr + `AIC_MBOX_BASE_ADDR);
      this.axi4_mbox_regmod.lock_model();
      m_reg_blocks[15] = axi4_mbox_regmod;

      //token manager //TODO https://git.axelera.ai/prod/europa/-/issues/1371
      this.tkn_manager_regmod = token_manager_aic_csr_reg_block::type_id::create("tkn_manager_regmod",,get_full_name());
      this.tkn_manager_regmod.configure(this, "AI_CORE_TOP_TKN_MANAGER_CSR");
      this.tkn_manager_regmod.build(null);
      ai_core_top_map.add_submap(tkn_manager_regmod.default_map, base_addr + `AIC_TKN_MANAGER_BASE_ADDR);
      this.tkn_manager_regmod.lock_model();
      m_reg_blocks[16] = tkn_manager_regmod;

      //aicore mid csr
      this.mid_periph_regmod = aic_csr_mid_part_reg_block::type_id::create("mid_periph_regmod",,get_full_name());
      this.mid_periph_regmod.configure(this, "AI_CORE_TOP_MID_PERIPHERALS_CSR");
      this.mid_periph_regmod.build(null);
      ai_core_top_map.add_submap(mid_periph_regmod.default_map, base_addr + `AIC_MID_PERIPH_CSR_BASE_ADDR);
      this.mid_periph_regmod.lock_model();
      m_reg_blocks[17] = mid_periph_regmod;

      //aicore mid csr
      this.infra_periph_regmod = aic_csr_reg_block::type_id::create("infra_periph_regmod",,get_full_name());
      this.infra_periph_regmod.configure(this, "AI_CORE_TOP_INFRA_PERIPHERALS_CSR");
      this.infra_periph_regmod.build(null);
      ai_core_top_map.add_submap(infra_periph_regmod.default_map, base_addr + `AIC_INFRA_PERIPH_CSR_BASE_ADDR);
      this.infra_periph_regmod.lock_model();
      m_reg_blocks[18] = infra_periph_regmod;


      //timestamp logger
      this.timestamp_logger_regmod = timestamp_logger_csr_reg_block::type_id::create("timestamp_logger_regmod",,get_full_name());
      this.timestamp_logger_regmod.configure(this, "AI_CORE_TIMESTAMP_LOGGER_CSR");
      this.timestamp_logger_regmod.build(null);
      ai_core_top_map.add_submap(timestamp_logger_regmod.default_map, base_addr + `AIC_TIMESTAMP_BASE_ADDR);
      this.timestamp_logger_regmod.lock_model();
      m_reg_blocks[19] = timestamp_logger_regmod;

      //LPDMA //PRGDMA
      this.aic_lp_dma_regmod = aic_lt_dw_axi_dmac_reg_block::type_id::create("aic_lp_dma_regmod",,get_full_name());
      this.aic_lp_dma_regmod.configure(this, "AI_CORE_LP_DMA_CSR");
      this.aic_lp_dma_regmod.build(null);
      ai_core_top_map.add_submap(aic_lp_dma_regmod.default_map, base_addr + `AIC_LP_DMA_BASE_ADDR);
      this.aic_lp_dma_regmod.lock_model();
      m_reg_blocks[20] = aic_lp_dma_regmod;

      ////HPDMA0 //Currently using synopsys dma, add when axelera dma comes in place
      //this.aic_hp_dma0_regmod = aic_ht_dw_axi_dmac_reg_block::type_id::create("aic_hp_dma0_regmod",,get_full_name());
      //this.aic_hp_dma0_regmod.configure(this, "AI_CORE_HP_DMA0_CSR");
      //this.aic_hp_dma0_regmod.build(null);
      //ai_core_top_map.add_submap(aic_hp_dma0_regmod.default_map, base_addr + `AIC_HP_DMA0_CSR_BASE_ADDR);
      //this.aic_hp_dma0_regmod.lock_model();
      //m_reg_blocks[19] = aic_hp_dma0_regmod;

      ////HPDMA1 //Currently using synopsys dma
      //this.aic_hp_dma1_regmod = aic_ht_dw_axi_dmac_reg_block::type_id::create("aic_hp_dma1_regmod",,get_full_name());
      //this.aic_hp_dma1_regmod.configure(this, "AI_CORE_HP_DMA1_CSR");
      //this.aic_hp_dma1_regmod.build(null);
      //ai_core_top_map.add_submap(aic_hp_dma1_regmod.default_map, base_addr + `AIC_HP_DMA1_CSR_BASE_ADDR);
      //this.aic_hp_dma1_regmod.lock_model();
      //m_reg_blocks[20] = aic_hp_dma1_regmod;

      this.aic_hp_dma_regmod = aic_ht_dw_axi_dmac_reg_block::type_id::create("aic_hp_dma_regmod",,get_full_name());
      this.aic_hp_dma_regmod.configure(this, "AI_CORE_HP_DMA0_CSR");
      this.aic_hp_dma_regmod.build(null);
      ai_core_top_map.add_submap(aic_hp_dma_regmod.default_map, base_addr + `AIC_HP_DMA_BASE_ADDR);
      this.aic_hp_dma_regmod.lock_model();
      m_reg_blocks[21] = aic_hp_dma_regmod;

      this.aic_rv_plic_regmod = aic_rv_plic_reg_block::type_id::create("aic_rv_plic_regmod",,get_full_name());
      this.aic_rv_plic_regmod.configure(this, "AI_CORE_RV_PLIC_CSR");
      this.aic_rv_plic_regmod.build(null);
      ai_core_top_map.add_submap(aic_rv_plic_regmod.default_map, base_addr + `AIC_RV_PLIC_BASE_ADDR);
      this.aic_rv_plic_regmod.lock_model();
      m_reg_blocks[22] = aic_rv_plic_regmod;
      //TODO : Currently acd connection to fabric is not done. everything is tied to zero. Check after it is connected.
      //this.aic_acd_regmod = aic_cd_csr_reg_block::type_id::create("aic_acd_regmod",,get_full_name());
      //this.aic_acd_regmod.configure(this, "AI_CORE_ACD_CSR");
      //this.aic_acd_regmod.build(null);
      //ai_core_top_map.add_submap(aic_acd_regmod.default_map, base_addr + `AIC_ACD_CSR_BASE_ADDR);
      //this.aic_acd_regmod.lock_model();
      //m_reg_blocks[23] = aic_acd_regmod;

      endfunction : build
  endclass : ai_core_top_reg_block

