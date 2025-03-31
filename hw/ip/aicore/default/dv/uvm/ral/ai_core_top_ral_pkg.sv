// memory map-> https://git.axelera.ai/prod/europa/-/blob/main/docs/europa/europa_detailed_memory_map.md
`define M_IFD0_CSR_BASE_ADDR 	      'h200_0000 
`define M_IFD1_CSR_BASE_ADDR 	      'h201_0000 
`define M_IFD2_CSR_BASE_ADDR 	      'h202_0000 
`define M_IFDW_CSR_BASE_ADDR 	      'h203_0000 
`define M_ODR_CSR_BASE_ADDR  	      'h204_0000 
`define D_IFD0_CSR_BASE_ADDR 	      'h205_0000 
`define D_IFD1_CSR_BASE_ADDR 	      'h206_0000 
`define D_ODR_CSR_BASE_ADDR  	      'h207_0000 

`define M_MVMEXE_CSR_BASE_ADDR	      'h220_0000 
`define M_MVMPRG_CSR_BASE_ADDR	      'h221_0000 
`define M_IAU_CSR_BASE_ADDR		      'h222_0000 
`define M_DPU_CSR_BASE_ADDR		      'h223_0000 

`define D_DWPU_CSR_BASE_ADDR 	      'h240_0000 
`define D_IAU_CSR_BASE_ADDR		      'h241_0000 
`define D_DPU_CSR_BASE_ADDR		      'h242_0000 

`define AIC_MBOX_BASE_ADDR             'h000_0000 
`define AIC_TKN_MANAGER_BASE_ADDR      'h001_0000
`define AIC_INFRA_PERIPH_CSR_BASE_ADDR 'h002_0000
`define AIC_MID_PERIPH_CSR_BASE_ADDR   'h003_0000
`define AIC_TIMESTAMP_BASE_ADDR        'h004_0000
`define AIC_RV_PLIC_BASE_ADDR          'h006_0000
`define AIC_ACD_CSR_BASE_ADDR          'h100_0000
`define AIC_LP_DMA_BASE_ADDR           'h102_0000
`define AIC_HP_DMA0_CSR_BASE_ADDR      'h260_0000
`define AIC_HP_DMA1_CSR_BASE_ADDR      'h261_0000
`define AIC_HP_DMA_BASE_ADDR           'h262_0000
`define AI_CORE_REGMOD_NUM             24  //used in ai_core_ral


package ai_core_top_ral_pkg;
  // Packages import
  import uvm_pkg::*;
  import dv_base_reg_pkg::*;
  import v_utils_pkg::*;
  import ai_core_cfg_csr_ral_pkg::*;
  import ifd_csr_ral_pkg::*;
  import odr_csr_ral_pkg::*;
  import mvmprg_csr_ral_pkg::*;
  import mvmexe_csr_ral_pkg::*;
  import iau_csr_ral_pkg::*;
  import dpu_csr_ral_pkg::*;
  import dwpu_csr_ral_pkg::*;
  import axi_mailbox_csr_ral_pkg::*;
  import token_manager_aic_csr_ral_pkg::*;
  import aic_csr_ral_pkg::*;
  import aic_csr_mid_part_ral_pkg::*;
  import timestamp_logger_csr_ral_pkg::*;
  import aic_lt_dw_axi_dmac_ral_pkg::*;
  import aic_ht_dw_axi_dmac_ral_pkg::*;
  import aic_rv_plic_ral_pkg::*;
  import aic_cd_csr_ral_pkg::*;

  `include "uvm_macros.svh"
  `include "ai_core_reg_block.svh"
  `include "ai_core_ral.sv"

endpackage:ai_core_top_ral_pkg
