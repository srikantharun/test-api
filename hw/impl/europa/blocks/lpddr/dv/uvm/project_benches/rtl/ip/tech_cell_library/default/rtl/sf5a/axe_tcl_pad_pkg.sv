// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Implementation definitions for sf5a PAD instances
///
package axe_tcl_pad_pkg;

  //////////////////////////////////////////
  // Functional Impl only, needed for mux //
  //////////////////////////////////////////
  typedef struct packed  {
    /// CMOS/Schmitt trigger selection
    logic       is;
    /// Drive Strength, width 2
    logic [1:0] ds;
    /// Nandtree enable
    logic       poe;
  } impl_pad_slow_inp_t;

  typedef struct packed  {
    /// Nand tree output
    logic po;
  } impl_pad_slow_oup_t;

  typedef struct packed  {
    /// CMOS/Schmitt trigger selection
    logic       is;
    /// Drive Strength, width 3
    logic [2:0] ds;
    /// Nandtree enable
    logic       poe;
  } impl_pad_fast_inp_t;

  typedef impl_pad_slow_oup_t impl_pad_fast_oup_t;

  ////////////////////
  // Ocillator Impl //
  ////////////////////
  typedef struct packed {
    /// Nandtree enable
    logic poe;
  } impl_oscillator_slow_inp_t;

  typedef struct packed {
    /// Clock output to core in DVDD level
    logic ck_iov;
    /// Nandtree output
    logic po;
  } impl_oscillator_slow_oup_t;

  typedef struct packed {
    /// Nandtree enable
    logic       poe;
    /// Select frequency pin
    logic [1:0] sf;
  } impl_oscillator_fast_inp_t;

  typedef impl_oscillator_slow_oup_t impl_oscillator_fast_oup_t;

  /////////////////////////////////////////
  // Power Impl, dirstibuted to all pads //
  /////////////////////////////////////////
  typedef struct packed {
    /// Active low weak PD resistor enable
    logic sps;
    /// Active low retention enable
    logic rtn;
    /// Voltage bias for levelshifter
    logic lsbias;
  } impl_pwr_t;

  // Note: when instantiatin do to be able to multiple drive it:
  // wire axe_tcl_pad_pkg::impl_pwr_t impl_power;
endpackage
