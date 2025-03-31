// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

interface timestamp_logger_event_if (input bit clk, input bit rst_n);
    logic [timestamp_logger_aic_pkg::TimeLogNumGroups-1:0]                                           group_triggers;
    logic [timestamp_logger_aic_pkg::TimeLogNumGroups-1:0] [timestamp_logger_pkg::TimeLogMaxMsgW-1:0] group_msgs;
    logic [timestamp_logger_pkg::TimeLogEntryTimestampW-1:0]         timestamp;
    logic sync_start;
    logic capture_enable; // TODO - only here while we have a race condition
endinterface : timestamp_logger_event_if
