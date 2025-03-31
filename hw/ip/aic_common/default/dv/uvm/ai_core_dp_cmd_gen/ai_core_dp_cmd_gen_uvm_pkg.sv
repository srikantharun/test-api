package ai_core_dp_cmd_gen_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import aic_common_pkg::*;
  import axe_uvm_resource_allocator_pkg::*;
  import axe_uvm_scoreboard_pkg::*;
  import axe_uvm_numeric_pkg::*;
  import common_seq_lib_uvm_pkg::*;

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif

  // AXI Environment and environment Configurations
  `include "cust_svt_axi_system_configuration.svh"
  `include "axi_null_virtual_sequence.svh"

  // Configuration
  `include "ai_core_dp_cmd_gen_env_cfg.svh"

  // Command Side
  `include "ai_core_dp_cmd_gen_cmdb_macros.svh"
  `include "ai_core_dp_cmd_gen_cmdb.svh"
  `include "ai_core_dp_cmd_gen_cmdb_mon.svh"
  `include "ai_core_dp_cmd_gen_cmdb_cov.svh"
  `include "ai_core_dp_cmd_gen_cmdb_drv.svh"
  `include "ai_core_dp_cmd_gen_cmdb_sqr.svh"
  `include "ai_core_dp_cmd_gen_cmdb_scoreboard.svh"
  `include "ai_core_dp_cmd_gen_cmdb_agent.svh"
  `include "ai_core_dp_cmd_gen_cmdb_seq_base.svh"

  // Instruction Side
  `include "ai_core_dp_cmd_gen_command.svh"
  `include "ai_core_dp_cmd_gen_command_mon.svh"
  `include "ai_core_dp_cmd_gen_command_scoreboard.svh"

  // Model
  `include "ai_core_dp_cmd_gen_model.svh"

  // Env
  `include "ai_core_dp_cmd_gen_seq_base.svh"
  `include "ai_core_dp_cmd_gen_env.svh"

  // Tests
  `include "ai_core_dp_cmd_gen_test_lib.svh"

  //common files
  `include "ai_core_dp_cmd_gen_structs.svh"
  `include "ai_core_dp_cmd_gen_utils.svh"

endpackage : ai_core_dp_cmd_gen_uvm_pkg
