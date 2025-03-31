// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

///
/// Parameters for cmdblock.

package cmdblock_pkg;

  typedef enum logic[1:0] {
    idle  = 2'd0,
    fill  = 2'd1,
    ready = 2'd2,
    exec  = 2'd3
  } cmbd_state_e;

  parameter int CMDB_TRIGGER_W = 4;
  typedef enum int {
    acd_end_idx = 0,
    acd_start_idx = 1,
    ts_end_idx = 2,
    ts_start_idx = 3
  } cmdb_trigger_idx_e;

endpackage
