// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS ODR Sequence
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_DMC_TOKEN_DELAY_SEQ_ITEM_SV
`define GUARD_AIC_DMC_TOKEN_DELAY_SEQ_ITEM_SV

class aic_ls_token_delay_seq_item extends token_agent_seq_item;
  `uvm_object_utils(aic_ls_token_delay_seq_item)

  constraint c_huge_delay {
    m_bv_delay inside {[100:1000]};
  }
  constraint c_huge_delay_dist {
    m_bv_delay dist {
      [100:700] :/ 10,
      [700:1000] :/ 90
    };
  }

  function new(string name = "aic_ls_token_delay_seq_item");
    super.new(name);
    `uvm_info (get_name(), $sformatf("New from aic_ls_token_delay_seq_item"), UVM_HIGH)
  endfunction

endclass : aic_ls_token_delay_seq_item

`endif 
