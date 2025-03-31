// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI CORE LS RAL. (But strictly the regmodels
//   combining to form the LS regmodel).
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

// Manually created RAL model block for AI Core LS Sub-system
class aic_ls_subsys_reg_block extends dv_base_reg_block;
  // Registration with factory
  `uvm_object_utils(aic_ls_subsys_reg_block)
  // RAL models objects
  ifd_csr_reg_block        m_ifd0_regmod;
  ifd_csr_reg_block        m_ifd1_regmod;
  ifd_csr_reg_block        m_ifd2_regmod;
  ifd_csr_reg_block        m_ifdw_regmod;
  ifd_csr_reg_block        d_ifd0_regmod;
  ifd_csr_reg_block        d_ifd1_regmod;
  odr_csr_reg_block        m_odr_regmod;
  odr_csr_reg_block        d_odr_regmod;
  // Reg map object
  uvm_reg_map             aic_ls_map;
  uvm_reg_block           m_reg_blocks[AIC_DMC_NUM_REGBLOCKS];

  // Class construcotr
  function new(string name = "aic_ls_subsys_reg_block");
    super.new(name);
  endfunction: new

  // Provide build function to supply base addr
  function void build(uvm_reg_addr_t base_addr, csr_excl_item csr_excl = null);

    // Map definition
    aic_ls_map = create_map(
      .name("default_map"),
      .base_addr(base_addr),
      .n_bytes(8),
      .endian(UVM_LITTLE_ENDIAN),
      .byte_addressing(0)
    );
    default_map    = aic_ls_map;

    // AI Core LS M_IFD0 RAL model Build
    m_ifd0_regmod = ifd_csr_reg_block::type_id::create("m_ifd0_regmod",,get_full_name());
    m_ifd0_regmod.configure(this, "g_ifd[0].u_ifd.i_ifd_csr");
    m_ifd0_regmod.build(null);
    aic_ls_map.add_submap(m_ifd0_regmod.default_map, `M_IFD0_BASE_ADDR);
    m_ifd0_regmod.lock_model();
    m_reg_blocks[0] = m_ifd0_regmod;

    // AI Core LS M_IFD1 RAL model Build
    m_ifd1_regmod = ifd_csr_reg_block::type_id::create("m_ifd1_regmod",,get_full_name());
    m_ifd1_regmod.configure(this, "g_ifd[1].u_ifd.i_ifd_csr");
    m_ifd1_regmod.build(null);
    // Map definition
    aic_ls_map.add_submap(m_ifd1_regmod.default_map, `M_IFD1_BASE_ADDR);
    m_ifd1_regmod.lock_model();
    m_reg_blocks[1] = m_ifd1_regmod;

    // AI Core LS M_IFD2 RAL model Build
    m_ifd2_regmod = ifd_csr_reg_block::type_id::create("m_ifd2_regmod",,get_full_name());
    m_ifd2_regmod.configure(this, "g_ifd[2].u_ifd.i_ifd_csr");
    m_ifd2_regmod.build(null);
    // Map definition
    aic_ls_map.add_submap(m_ifd2_regmod.default_map, `M_IFD2_BASE_ADDR);
    m_ifd2_regmod.lock_model();
    m_reg_blocks[2] = m_ifd2_regmod;

    // AI Core LS M_IFDW RAL model Build
    m_ifdw_regmod = ifd_csr_reg_block::type_id::create("m_ifdw_regmod",,get_full_name());
    m_ifdw_regmod.configure(this, "g_ifd[3].u_ifd.i_ifd_csr");
    m_ifdw_regmod.build(null);
    // Map definition
    aic_ls_map.add_submap(m_ifdw_regmod.default_map, `M_IFDW_BASE_ADDR);
    m_ifdw_regmod.lock_model();
    m_reg_blocks[3] = m_ifdw_regmod;

    // AI Core LS D_IFD0 RAL model Build
    d_ifd0_regmod = ifd_csr_reg_block::type_id::create("d_ifd0_regmod",,get_full_name());
    d_ifd0_regmod.configure(this, "g_ifd[4].u_ifd.i_ifd_csr");
    d_ifd0_regmod.build(null);
    // Map definition
    aic_ls_map.add_submap(d_ifd0_regmod.default_map, `D_IFD0_BASE_ADDR);
    d_ifd0_regmod.lock_model();
    m_reg_blocks[4] = d_ifd0_regmod;

    // AI Core LS D_IFD1 RAL model Build
    d_ifd1_regmod = ifd_csr_reg_block::type_id::create("d_ifd1_regmod",,get_full_name());
    d_ifd1_regmod.configure(this, "g_ifd[5].u_ifd.i_ifd_csr");
    d_ifd1_regmod.build(null);
    // Map definition
    aic_ls_map.add_submap(d_ifd1_regmod.default_map, `D_IFD1_BASE_ADDR);
    d_ifd1_regmod.lock_model();
    m_reg_blocks[5] = d_ifd1_regmod;

    // AI Core LS M_ODR RAL model Build
    m_odr_regmod = odr_csr_reg_block::type_id::create("m_odr_regmod",,get_full_name());
    m_odr_regmod.configure(this, "g_odr[6].u_odr.i_odr_csr");
    m_odr_regmod.build(null);
    // Map definition
    aic_ls_map.add_submap(m_odr_regmod.default_map, `M_ODR_BASE_ADDR);
    m_odr_regmod.lock_model();
    m_reg_blocks[6] = m_odr_regmod;

    // AI Core LS D_ODR RAL model Build
    d_odr_regmod = odr_csr_reg_block::type_id::create("d_odr_regmod",,get_full_name());
    d_odr_regmod.configure(this, "g_odr[7].u_odr.i_odr_csr");
    d_odr_regmod.build(null);
    // Map definition
    aic_ls_map.add_submap(d_odr_regmod.default_map, `D_ODR_BASE_ADDR);
    d_odr_regmod.lock_model();
    m_reg_blocks[7] = d_odr_regmod;

  endfunction : build
endclass : aic_ls_subsys_reg_block
