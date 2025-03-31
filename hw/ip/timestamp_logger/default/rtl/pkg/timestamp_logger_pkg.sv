// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp logger package
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef TIMESTAMP_LOGGER_PKG_SV
`define TIMESTAMP_LOGGER_PKG_SV

package timestamp_logger_pkg;

  //-------------------------------------------------
  // Parameter definition
  //-------------------------------------------------
  parameter int unsigned TimeLogMaxMsgW = 24;
  parameter int unsigned TimeLogEntryTimestampW = 32;
  parameter int unsigned TimeLogMaxNrGroups = 128; // Sync with CSR

  parameter int unsigned TimeLogScaleW = 3; // should match csr_reg_pkg cntr_division
  parameter int unsigned TimeLogCntrW = TimeLogEntryTimestampW + 2^TimeLogScaleW;

  parameter int unsigned TimeLogEntryMessageLsb   = 0;
  parameter int unsigned TimeLogEntryGroupLsb     = 24;
  parameter int unsigned TimeLogEntryTimestampLsb = 32;

  parameter int unsigned TimeLogEntryDW = 64; // TimeLogEntryTimestampLsb + TimeLogEntryTimestampW;

  parameter int unsigned TimeLogMaxBurst = 128; // Align with CSR
  parameter int unsigned TimeLogAlignBytes = TimeLogMaxBurst * 8;
  parameter int unsigned TimeLogAlignWidth = $clog2(TimeLogAlignBytes);

  typedef enum logic {
    csr_idx = 1'b0,
    mem_idx = 1'b1
  } time_log_bus_idx_e;

endpackage

`endif  // TIMESTAMP_LOGGER_PKG_SV
