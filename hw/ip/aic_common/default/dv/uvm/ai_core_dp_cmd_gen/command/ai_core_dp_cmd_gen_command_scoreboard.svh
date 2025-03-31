// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_COMMAND_SCOREBOARD_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_COMMAND_SCOREBOARD_SVH

class ai_core_dp_cmd_gen_command_scoreboard extends axe_uvm_scoreboard #(ai_core_dp_cmd_gen_command#(aic_dp_cmd_gen_pkg::dummy_dp_command_t), ai_core_dp_cmd_gen_command#(aic_dp_cmd_gen_pkg::dummy_dp_command_t));

    `uvm_component_utils(ai_core_dp_cmd_gen_command_scoreboard)

    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

endclass : ai_core_dp_cmd_gen_command_scoreboard
`endif // GUARD_AI_CORE_DP_CMD_GEN_COMMAND_SCOREBOARD_SVH
