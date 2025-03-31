// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Package containing common definitions for all tech_cells
///
package axe_tcl_pkg;

  /// Type for specifying if a sram request is active this cycle
  typedef enum logic {
    SramReqActive = 1'b1,
    SramReqIdle   = 1'b0
  } sram_req_t;

  /// Type for write / read selection
  typedef enum logic {
    SramWrite = 1'b1,
    SramRead  = 1'b0
  } sram_we_t;

  /// RAM Margin control default values
  parameter bit [1:0] MCS  = 2'b01;
  parameter bit       MCSW = 1'b0;
  parameter bit [2:0] ADME = 3'b100;

endpackage
