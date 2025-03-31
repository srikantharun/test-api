
`ifndef AI_CORE_CD_REF_MODEL_CFG_SV
`define AI_CORE_CD_REF_MODEL_CFG_SV

// AI CORE DWPU environment configuration class
class ai_core_cd_ref_model_cfg extends uvm_object; // 

  `uvm_object_utils(ai_core_cd_ref_model_cfg)

  //check enable:
  bit tkn_consume_produce_parity_en;


  //
  int local_token_line_num;
  int global_token_line_num;

  int fill_counter_num;

  /** Class Constructor */
  function new(string name = "ai_core_cd_ref_model_cfg");
    super.new(name);
  endfunction : new

endclass : ai_core_cd_ref_model_cfg

`endif  // AI_CORE_CD_REF_MODEL_CFG_SV
