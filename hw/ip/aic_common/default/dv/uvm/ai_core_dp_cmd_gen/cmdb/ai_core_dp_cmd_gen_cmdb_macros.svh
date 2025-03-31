// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_CMDB_MACROS_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_CMDB_MACROS_SVH

`define _start_(x)       (x.start)
`define _length_(x)      (x.length)
`define _end_(x)         (x.start + x.length - 1)
`define _iteration_(x)   (x.iteration)
`define _main_0_valid_   (valid)
`define _main_1_valid_   (valid && (format >= aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N0)))
`define _main_2_valid_   (valid && (format >= aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N0)))
`define _nested_0_valid_ (valid && (format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N1) || aic_dp_cmd_gen_pkg::cmd_format_t'(format == aic_dp_cmd_gen_pkg::LoopsM1N2) || format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N1) || format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N2) || format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N1) || format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N2)))
`define _nested_1_valid_ (valid && (format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N2) || aic_dp_cmd_gen_pkg::cmd_format_t'(format == aic_dp_cmd_gen_pkg::LoopsM2N2) || format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N2)))
`define _co_nested_      (`_nested_0_valid_ && `_nested_1_valid_ && (nested_0_map_main == nested_1_map_main))

`endif // GUARD_AI_CORE_DP_CMD_GEN_CMDB_MACROS_SVH
