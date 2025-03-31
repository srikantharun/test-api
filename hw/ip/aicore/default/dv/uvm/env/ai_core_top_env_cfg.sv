
`ifndef GUARD_AI_CORE_ENV_CFG_SV
`define GUARD_AI_CORE_ENV_CFG_SV

// ai_core memory module environment configuration class
class ai_core_top_env_cfg extends uvm_object;
 int uvm_sw_ipc_handle_end_of_test = 0;
 `uvm_object_utils(ai_core_top_env_cfg)
 aic_ls_env_cfg              m_ls_env_cfg;

  /** Class Constructor */
  function new (string name="ai_core_top_env_cfg");
    super.new (name);
    uvm_sw_ipc_handle_end_of_test = $test$plusargs("UVM_SW_IPC_HANDLE_END_OF_TEST");
    m_ls_env_cfg    = aic_ls_env_cfg::type_id::create("m_ls_env_cfg");

  endfunction:new

  // Objects handles
  //top_blk ral_model;

  bit has_coverage   = 1'b0;
  bit has_scoreboard = 1'b1;
  int ai_core_cid    = $test$plusargs("AI_CORE_1") ? 'd1 :
                      ($test$plusargs("AI_CORE_2") ? 'd2 :
                      ($test$plusargs("AI_CORE_3") ? 'd3 :
                      ($test$plusargs("AI_CORE_4") ? 'd4 : 'd1)));


endclass:ai_core_top_env_cfg

`endif // GUARD_AI_CORE_ENV_CFG_SV
