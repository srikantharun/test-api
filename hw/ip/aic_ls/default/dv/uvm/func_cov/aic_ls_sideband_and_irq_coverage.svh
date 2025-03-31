// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Sideband and IRQ Function Coverage
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

/** Cover all the interrupt conditions for each sub-block. */
covergroup aic_ls_irq_cg with function sample(aic_ls_seq_item item);
  option.per_instance = 1'b1;
  option.name         = "aic_ls_irq_cg";

  cp_irq : coverpoint item.irq_out {
    bins M_IFD0_IRQ  = {'d1   };
    bins M_IFD1_IRQ  = {'d2   };
    bins M_IFD2_IRQ  = {'d4   };
    bins M_IFDW_IRQ  = {'d8   };
    bins D_IFD0_IRQ  = {'d16  };
    bins D_IFD1_IRQ  = {'d32  };
    bins M_ODR_IRQ   = {'d64  };
    bins D_ODR_IRQ   = {'d128 };
  }
endgroup : aic_ls_irq_cg

covergroup aic_ls_sideband_cg with function sample(aic_ls_seq_item item);
  option.per_instance = 1'b1;
  option.name         = "aic_ls_sideband_cg";

  /** Drive sideband CID signal via virtual interface. Verify by accessing L1. */
  cp_cid : coverpoint item.cid {
    bins AI_CORE_1 = {1};
    bins AI_CORE_2 = {2};
    bins AI_CORE_3 = {3};
    bins AI_CORE_4 = {4};
    bins AI_CORE_5 = {5};
    bins AI_CORE_6 = {6};
    bins AI_CORE_7 = {7};
    bins AI_CORE_8 = {8};
  }

  /** This is verified in conjunction with AI_CORE_LS_L1 req_id. The sideband signal will be driven for all valid 2-bit combinations and */

  cp_light_sleep : coverpoint item.l1_mem_ls {
    bins DISABLED = {0};
    bins ENABLED  = {1};
  }

  cp_deep_sleep : coverpoint item.l1_mem_ds {
    bins DISABLED = {0};
    bins ENABLED  = {1};
  }

  cp_shutdown : coverpoint item.l1_mem_sd {
    bins DISABLED = {0};
    bins ENABLED  = {1};
  }

endgroup : aic_ls_sideband_cg
