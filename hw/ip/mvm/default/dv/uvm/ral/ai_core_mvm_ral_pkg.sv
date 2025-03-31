// Manually created RAL model package for AI Core MVM Sub-system
package ai_core_mvm_ral_pkg;
  // Packages import
  import uvm_pkg::*;
  // Macro includes
  `include "uvm_macros.svh"
  import dv_base_reg_pkg::*;
  import aic_addr_map_pkg::*;
  import mvmprg_csr_ral_pkg::*;
  import mvmexe_csr_ral_pkg::*;

  `ifndef EUROPA_ADDR_MAP
  localparam MVMEXE_CSR_BASE_ADDR = 28'h009_0000;
  localparam MVMPRG_CSR_BASE_ADDR = 28'h00A_0000;
  `else
  localparam MVMEXE_CSR_BASE_ADDR = aic_addr_map_pkg::AIC_LOC_M_MVM_EXE_CSR_ST_ADDR;
  localparam MVMPRG_CSR_BASE_ADDR = aic_addr_map_pkg::AIC_LOC_M_MVM_PRG_CSR_ST_ADDR;
  `endif


  // Manually created RAL model block for AI Core MVM Sub-system
  class ai_core_mvm_reg_block extends dv_base_reg_block;
    // Registration with factory
    `uvm_object_utils(ai_core_mvm_reg_block)
    // RAL models objects
    rand mvmexe_csr_reg_block         m_mvmexe_regmod;
    rand mvmprg_csr_reg_block         m_mvmprg_regmod;
    // Reg map object
    uvm_reg_map ai_core_mvm_map;

    // Class construcotr
    function new(string name = "ai_core_mvm_reg_block");
      super.new(name);
    endfunction: new

   // Provide build function to supply base addr
   function void build(uvm_reg_addr_t base_addr, csr_excl_item csr_excl = null);

      // Map definition
      ai_core_mvm_map = create_map(base_addr, 0, 8, UVM_LITTLE_ENDIAN, 0);
      default_map    = ai_core_mvm_map;

      this.m_mvmexe_regmod = mvmexe_csr_reg_block::type_id::create("m_mvmexe_regmod",,get_full_name());
      this.m_mvmexe_regmod.configure(this, "AI_MVMEXE_CSR");
      this.m_mvmexe_regmod.build(null);
      ai_core_mvm_map.add_submap(m_mvmexe_regmod.default_map, MVMEXE_CSR_BASE_ADDR);
      this.m_mvmexe_regmod.lock_model();

      // AI Core MVM CSR RAL model Build
      this.m_mvmprg_regmod = mvmprg_csr_reg_block::type_id::create("m_mvmprg_regmod",,get_full_name());
      this.m_mvmprg_regmod.configure(this, "AI_MVMPRG_CSR");
      this.m_mvmprg_regmod.build(null);
      ai_core_mvm_map.add_submap(m_mvmprg_regmod.default_map, MVMPRG_CSR_BASE_ADDR);
      this.m_mvmprg_regmod.lock_model();
   endfunction : build
  endclass : ai_core_mvm_reg_block

endpackage:ai_core_mvm_ral_pkg
