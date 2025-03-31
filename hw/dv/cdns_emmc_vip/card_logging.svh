//------------------------------------------------------------------------------
//                                                                              
//            CADENCE                    Copyright (c) 2013                     
//                                       Cadence Design Systems, Inc.           
//                                       All rights reserved.                   
//                                                                              
//  This work may not be copied, modified, re-published, uploaded, executed, or 
//  distributed in any way, in any medium, whether in whole or in part, without 
//  prior written permission from Cadence Design Systems, Inc.                  
//------------------------------------------------------------------------------
//                                                                              
//   Author                : mrodzik@cadence.com                              
//                                                                              
//   Date                  : $Date$
//                                                                              
//   Last Changed Revision : $LastChangedRevision$
// 
//------------------------------------------------------------------------------
//   Description                                                                
//                                                                   
//   SystemVerilog macros for information logging by card model components.     
//------------------------------------------------------------------------------


`ifndef CARD_LOGGING
`define CARD_LOGGING

  `include "sv_macros.svh"
  `include "uvm_macros.svh"

  `ifdef USE_LOGGERS

    `define CARD_LOGGING_UTILS \
      logger_cl  logger    = null; \
      string     log_id    = ""; \
      string     hierarchy = ""; \
      function void init_logging(logger_cl _logger, string _log_id, string _hierarchy); \
        log_id = _log_id; \
        hierarchy = _hierarchy; \
        logger    = _logger; \
        init_logging_subcomponents; \
      endfunction : init_logging

    `define INIT_LOGGING_SUBCOMPS_BEGIN \
      virtual function void init_logging_subcomponents;

    `define INIT_LOGGING_SUBCOMPS_END \
      endfunction : init_logging_subcomponents

  `else // USE_LOGGERS

    `define CARD_LOGGING_UTILS // empty
    `define INIT_LOGGING_SUBCOMPS_BEGIN // empty
    `define INIT_LOGGING_SUBCOMPS_END // empty

  `endif // !USE_LOGGERS

  `ifdef USE_LOGGERS

    `define DISPLAY_LOGGER_MSG(_msg) \
      if (logger != null) \
        logger.message(stoq(log_id), NONE, hierarchy, _msg); \
      else \
        $display("%t %s", $realtime, _msg);

    `define DISPLAY_LOGGER_NOTE(_msg) \
      if (logger != null) \
        logger.message(stoq(log_id), NOTE, hierarchy, _msg); \
      else \
        $display("%t %s", $realtime, _msg);

    `define DISPLAY_LOGGER_INFO(_msg) \
      if (logger != null) \
        logger.message(stoq(log_id), INFO, hierarchy, _msg); \
      else \
        $display("%t %s", $realtime, _msg);

    `define DISPLAY_LOGGER_WARNING(_msg) \
      if (logger != null) \
        logger.message(stoq(log_id), WARNING, hierarchy, _msg); \
      else \
        assert (0) else $warning("%t %s", $realtime, _msg);

    `define DISPLAY_LOGGER_ERROR(_msg) \
      if (logger != null) \
        logger.message(stoq(log_id), ERROR, hierarchy, _msg); \
      else \
        assert (0) else $error("%t %s", $realtime, _msg);

    `define DISPLAY_LOGGER_GREEN(_msg) \
      if (logger != null) \
        logger.message(stoq(log_id), GREEN, hierarchy, _msg); \
      else \
        assert (0) else $info("%t %s", $realtime, _msg);

    `define ASSERT_COND_LOGGER_MSG(_cond, _sev, _msg, _action) \
      `ASSERT_COND_ACTION(_cond) \
        if (logger != null) \
          logger.message(stoq(log_id), _sev ? ERROR : WARNING, hierarchy, _msg); \
        else if (_sev) \
          $error(_msg); \
        else \
          $warning(_msg); \
        _action; \
      `ENDACTION

    `define DISPLAY_LOGGER_DEBUG(_sev, _msg) \
      if (logger != null) \
        logger.message(stoq(log_id), _sev ? DATAGEN : OVERRIDE, hierarchy, _msg); \
      else \
        assert (0) else $info("%t %s", $realtime, _msg);

  `else // USE_LOGGERS

    `ifdef QUESTA

      `define DISPLAY_LOGGER_MSG(_msg) \
        `uvm_info("EMMC_LOGGER", _msg, UVM_NONE)

      `define DISPLAY_LOGGER_NOTE(_msg) \
        `DISPLAY_LOGGER_MSG(_msg)

      `define DISPLAY_LOGGER_INFO(_msg) \
        `uvm_info("EMMC_LOGGER", _msg, UVM_LOW)

      `define DISPLAY_LOGGER_WARNING(_msg) \
        `uvm_warning("EMMC_LOGGER", _msg)

      `define DISPLAY_LOGGER_ERROR(_msg) \
        `uvm_error("EMMC_LOGGER", _msg)

    `define DISPLAY_LOGGER_GREEN(_msg) \
        `uvm_info("EMMC_LOGGER", _msg, UVM_LOW)

    `define DISPLAY_LOGGER_DEBUG(_sev, _msg) \
        `uvm_info("EMMC_LOGGER", _msg, UVM_LOW)

    `else // QUESTA

      `define DISPLAY_LOGGER_MSG(_msg) \
        $display("       %t %s", $realtime, _msg);

      `define DISPLAY_LOGGER_NOTE(_msg) \
        $display("NOTE:  %t %s", $realtime, _msg);

      `define DISPLAY_LOGGER_INFO(_msg) \
        $display("INFO:  %t %s", $realtime, _msg);

      `define DISPLAY_LOGGER_WARNING(_msg) \
        $display("WARN:  %t %s", $realtime, _msg);

      `define DISPLAY_LOGGER_ERROR(_msg) \
        $display("ERROR: %t %s", $realtime, _msg);

      `define DISPLAY_LOGGER_GREEN(_msg) \
        $display("%t %s", $realtime, _msg);

      `define DISPLAY_LOGGER_DEBUG(_sev, _msg) \
        $display("DEBUG: %t %s", $realtime, _msg);
      
    `endif // !QUESTA

    `define ASSERT_COND_LOGGER_MSG(_cond, _sev, _msg, _action) \
      `ASSERT_COND_ACTION(_cond) \
        if (_sev) \
          $error(_msg); \
        else \
          $warning(_msg); \
        _action; \
      `ENDACTION

  `endif // !USE_LOGGERS

`endif // !CARD_LOGGING

