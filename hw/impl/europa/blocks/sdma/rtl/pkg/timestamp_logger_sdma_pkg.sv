// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp logger package for SDMA instance
// Owner: Sander Geursen <sander.geursen@axelera.ai>

package timestamp_logger_sdma_pkg;

  //-------------------------------------------------
  // Port specific:
  //-------------------------------------------------

  //-------------------------------------------------
  // Logger config:
  //-------------------------------------------------
  parameter int unsigned TimeLogMemDepth = 32;
  parameter int unsigned TimeLogUseMacro = 0;
  parameter int unsigned TimeLogTimestampFifoDepth = 4;

  //-------------------------------------------------
  // Group config:
  //-------------------------------------------------
  parameter int unsigned TimeLogNumGroups = 3; // SW, DevSt, DevEnd
  parameter int unsigned TimeLogNumDevs = sdma_pkg::NUM_CHNLS; // number of channels, should be in aligned with CSR
  typedef enum logic[1:0] {
    swep_idx = 0,
    dev_st_idx = 1,
    dev_end_idx = 2
  } timelog_sdma_group_idx_e;

  parameter int unsigned TimeLogGroupMsgWidth[TimeLogNumGroups] = '{
    swep_idx: 2,
    dev_st_idx: TimeLogNumDevs,
    dev_end_idx: TimeLogNumDevs
  };
  parameter int unsigned TimeLogGroupFifoDepth[TimeLogNumGroups] = '{
    swep_idx: 2,
    dev_st_idx: 4,
    dev_end_idx: 4
  };
endpackage

