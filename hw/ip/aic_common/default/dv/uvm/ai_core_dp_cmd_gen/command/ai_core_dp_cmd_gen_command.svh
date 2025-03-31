// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_COMMAND_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_COMMAND_SVH

class ai_core_dp_cmd_gen_command#(type dp_command_t) extends uvm_sequence_item;

    dp_command_t                                             data;
    aic_dp_cmd_gen_pkg::cmd_format_e                          format;
    aic_dp_cmd_gen_pkg::command_extra_t                       extra;
    logic                                                     last;
    logic                                                     overall_last;
    aic_dp_cmd_gen_pkg::loop_iteration_t                      nested_1;
    aic_dp_cmd_gen_pkg::loop_iteration_t                      nested_0;
    aic_dp_cmd_gen_pkg::loop_iteration_t                      main;
    aic_dp_cmd_gen_pkg::loop_index_t                          main_index;
    real                                                      timestamp;

    `uvm_object_param_utils_begin(ai_core_dp_cmd_gen_command#(dp_command_t))
        `uvm_field_int(                                   data,          UVM_DEFAULT)
        `uvm_field_enum(aic_dp_cmd_gen_pkg::cmd_format_e, format,        UVM_DEFAULT)
        `uvm_field_int(                                   extra,         UVM_DEFAULT)
        `uvm_field_int(                                   last,          UVM_DEFAULT)
        `uvm_field_int(                                   overall_last,  UVM_DEFAULT)
        `uvm_field_int(                                   nested_1,      UVM_DEFAULT)
        `uvm_field_int(                                   nested_0,      UVM_DEFAULT)
        `uvm_field_int(                                   main,          UVM_DEFAULT)
        `uvm_field_int(                                   main_index,    UVM_DEFAULT)
        `uvm_field_real(                                  timestamp,     UVM_DEFAULT | UVM_NOCOMPARE) // Debug only
    `uvm_object_utils_end

    function new(string name = "");
        super.new(name);
        data          = dp_command_t'('0);
        format        = aic_dp_cmd_gen_pkg::cmd_format_e'('0); 
        extra         = aic_dp_cmd_gen_pkg::command_extra_t'('0);
        last          = 1'b0;
        overall_last  = 1'b0;
        nested_1       = aic_dp_cmd_gen_pkg::loop_iteration_t'('0);
        nested_0       = aic_dp_cmd_gen_pkg::loop_iteration_t'('0);
        main         = aic_dp_cmd_gen_pkg::loop_iteration_t'('0);
        main_index   = aic_dp_cmd_gen_pkg::loop_index_t'('0);      
    endfunction : new

endclass : ai_core_dp_cmd_gen_command

`endif // GUARD_AI_CORE_DP_CMD_GEN_COMMAND_SVH
