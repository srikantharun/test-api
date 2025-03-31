// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp logger package for AIC instance
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef TIMESTAMP_LOGGER_AIC_PKG_SV
`define TIMESTAMP_LOGGER_AIC_PKG_SV

package timestamp_logger_aic_pkg;

  //-------------------------------------------------
  // Port specific:
  //-------------------------------------------------
  parameter int unsigned TimeLogACDMsgW = 2;

  //-------------------------------------------------
  // Logger config:
  //-------------------------------------------------
  parameter int unsigned TimeLogMemDepth = 1024;
  parameter int unsigned TimeLogUseMacro = 1;
  parameter TimeLogSramImplKey = "HS_RVT";
  parameter int unsigned TimeLogTimestampFifoDepth = 16;

  //-------------------------------------------------
  // Group config:
  //-------------------------------------------------
  parameter int unsigned TimeLogNumGroups = 7; // SW, ACD, DevSt, DevEnd, PC, LD, ST
  parameter int unsigned TimeLogNumDevs = 17;
  typedef enum logic[2:0] {
    swep_idx = 0,
    acd_idx = 1,
    dev_st_idx = 2,
    dev_end_idx = 3,
    pc_idx = 4,
    st_idx = 5,
    ld_idx = 6
  } timelog_aic_group_idx_e;

  parameter int unsigned TimeLogGroupMsgWidth[TimeLogNumGroups] = '{
    swep_idx: 2,
    acd_idx: 2,
    dev_st_idx: TimeLogNumDevs,
    dev_end_idx: TimeLogNumDevs,
    pc_idx: timestamp_logger_aic_csr_reg_pkg::PC_COMPARES,
    st_idx: timestamp_logger_aic_csr_reg_pkg::ST_COMPARES,
    ld_idx: timestamp_logger_aic_csr_reg_pkg::LD_COMPARES
  };
  parameter int unsigned TimeLogGroupFifoDepth[TimeLogNumGroups] = '{
    swep_idx: 2,
    acd_idx: 2,
    dev_st_idx: 8,
    dev_end_idx: 8,
    pc_idx: 4,
    st_idx: 4,
    ld_idx: 4
  };
endpackage

`endif  // TIMESTAMP_LOGGER_AIC_PKG_SV
