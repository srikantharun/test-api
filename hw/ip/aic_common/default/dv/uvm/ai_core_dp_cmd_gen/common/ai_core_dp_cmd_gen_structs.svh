`ifndef AI_CORE_DP_CMD_GEN_STRUCTS_SVH
`define AI_CORE_DP_CMD_GEN_STRUCTS_SVH
 
  typedef struct {
    bit [31:0] main_dt_cnt[3];
    bit [31:0] nested_dt_cnt[2];
  } data_stream_cfg_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m1n0_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m1n1_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_1;
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m1n2_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m2n0_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m2n1_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_1;
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m2n2_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
    aic_dp_cmd_gen_pkg::loop_description_t main_2;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m3n0_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
    aic_dp_cmd_gen_pkg::loop_description_t main_2;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m3n1_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_1;
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
    aic_dp_cmd_gen_pkg::loop_description_t main_2;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m3n2_t;
`endif // AI_CORE_DP_CMD_GEN_STRUCTS_SVH
