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
//   Author                : (username)@cadence.com                              
//                                                                              
//   Date                  : $Date$
//                                                                              
//   Last Changed Revision : $LastChangedRevision$
// 
//------------------------------------------------------------------------------
//   Description                                                                
//                                                                 
//   Global SystemVerilog macros
//                                        
//------------------------------------------------------------------------------

`ifndef SV_MACROS_SVH
`define SV_MACROS_SVH

  `ifdef QUESTA
    //`define NO_PURE_KEYWORD
    //`define NO_INSTANCE_CONSTANTS
    `define NO_EMPTY_STATEMENT
  `endif

  `ifdef NCSIM
    //`define NO_PURE_KEYWORD
    //`define NO_INSTANCE_CONSTANTS
    //`define NO_EMPTY_STATEMENT
  `endif

  `ifdef NCSIM
    `define WAIT_COND(_cond, _wait) \
      while (~(_cond)) #(_wait);
  `else
    `define WAIT_COND(_cond, _wait) \
      wait (_cond);
  `endif

  // ---------------------------------------------------------------------- //
  
  // TRUE/FALSE
  // ~~~~~~~~~~

  `define TRUE     1'b1
  `define FALSE    1'b0
                   
  `define HIGH     1'b1
  `define LOW      1'b0
                   
  `define HIMP     1'bZ
  `define OPEN     1'bZ
  `define UNKN     1'bX
  `define DNTC     1'bX
                   
  `define YES      1'b1
  `define NO       1'b0
                   
  `define OK       1'b1
  `define FAILED   1'b0
  `define WAIT     1'bX
  
  `define SABGWAIT 1'bX
  `define SABGINT  1'b1
  `define TCINT    1'b0

  // NO_INSTANCE_CONSTANTS
  // ~~~~~~~~~~~~~~~~~~~~~
  // Example:
  // `CONST int n;

  `ifdef NO_INSTANCE_CONSTANTS
    `define CONST
  `else
    `define CONST const
  `endif

  // NO_PURE_KEYWORD
  // ~~~~~~~~~~~~~~~
  // Example:
  // `PURE virtual function bit F; `ENDPUREFUNCTION
  // `PURE virtual task T; `ENDPURETASK

  `ifdef NO_PURE_KEYWORD
    `define PURE 
    `define ENDPUREFUNCTION endfunction
    `define ENDPURETASK     endtask
  `else
    `define PURE pure 
    `define ENDPUREFUNCTION
    `define ENDPURETASK
  `endif

  // EMPTY STATEMENT
  // ~~~~~~~~~~~~~~~

  `ifdef NO_EMPTY_STATEMENT
    int empty_statement_superfluous_global_variable;
    `define EMPTY_STMNT int empty_statement_superfluous_variable=0
    `define EMPTY_INSTR ++empty_statement_superfluous_global_variable
  `else
    `define EMPTY_STMNT
    `define EMPTY_INSTR
  `endif

  // ASSERTIONS & PROPERTIES
  // ~~~~~~~~~~~~~~~~~~~~~~~

  /* CAUTION: assert/cover statement labels are not treated as a separate
              hierarchy level under some simulators (e.g. NCSIM). */

  `define ASSERT_PROP(_prop) \
    a_``_prop: \
    assert property (_prop) else

  `define COVER_PROP(_prop) \
    c_``_prop: \
    cover property (_prop)

  `define ASSERT_PROP_ERROR(_prop) \
    `ASSERT_PROP(_prop) $error("%m");

  `define COVER_PROP_INFO(_prop) \
    `COVER_PROP(_prop) $info("%m");

  `define ASSERT_PROP_ACTION(_prop) \
    `ASSERT_PROP(_prop) begin

  `define COVER_PROP_ACTION(_prop) \
    `COVER_PROP(_prop) begin

  `define ASSERT_PROP_ARGS(_prop, _label) \
    a_``_label: \
    assert property (_prop) else

  `define COVER_PROP_ARGS(_prop, _label) \
    c_``_label: \
    cover property (_prop)

  `define ASSERT_PROP_ARGS_ERROR(_prop, _label) \
    `ASSERT_PROP_ARGS(_prop, _label) $error("%m");

  `define COVER_PROP_ARGS_INFO(_prop, _label) \
    `COVER_PROP_ARGS(_prop, _label) $info("%m");

  `define ASSERT_PROP_ARGS_ACTION(_prop, _label) \
    `ASSERT_PROP_ARGS(_prop, _label) begin

  `define COVER_PROP_ARGS_ACTION(_prop, _label) \
    `COVER_PROP_ARGS(_prop, _label) begin

  `define ASSERT_COND(_cond) \
    assert (_cond) else

  `define COVER_COND(_cond) \
    cover (_cond)

  `define ASSERT_COND_ERROR(_cond) \
    `ASSERT_COND(_cond) $error("%m");

  `define COVER_COND_INFO(_cond) \
    `COVER_COND(_cond) $info("%m");

  `define ASSERT_COND_ACTION(_cond) \
    `ASSERT_COND(_cond) begin

  `define COVER_COND_ACTION(_cond) \
    `COVER_COND(_cond) begin

  `define COVER_SEQ_ACTION(_seq, _clk) \
    c_``_seq: \
    cover property (@(_clk) _seq) begin

  `define ENDACTION end

  `define COVER_SEQ_INFO_MSG(_seq, _clk, _msg) \
    c_``_seq: \
    cover property (@(_clk) _seq) $info(_msg);

  // Example:
  // `ASSERT_PROP_ERROR(some_prop)
  // `COVER_PROP_ACTION(some_prop) $display("whatever"); `ENDPROPACTION

  `define NOT_SUPPORTED_YET \
    begin \
      assert (0) else \
      $error("Not supported yet"); \
    end

  `define ISPULLEDUP(_pin) \
    (_pin === `HIGH || _pin === `HIMP)

  `define ISPULLEDDOWN(_pin) \
    (_pin === `LOW || _pin == `HIMP)
`endif // SV_MACROS_SVH
