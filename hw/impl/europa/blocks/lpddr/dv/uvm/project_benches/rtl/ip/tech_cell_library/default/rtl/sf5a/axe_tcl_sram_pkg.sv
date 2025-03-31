// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

// TODO(wroennin): This file should be auto-generated!

/// Package containing the implemetation definition for sf5a memories
///
package axe_tcl_sram_pkg;

  // Miscellaneous Samsung 5nm memory signals that should be passed to
  // the synopsys memory wrapper via the impl_i port and impl_in_t type.
  typedef struct packed  {
    /// Margin adjustment control selection
    logic [1:0] mcs;
    /// Margin adjustment control selection write
    logic       mcsw;
    /// Retention mode enable input pin (power gating)
    logic       ret;
    /// Power down enable, active high (power gating)
    logic       pde;
    /// Scan enable, active high
    logic       se;
    /// Margin adjustment for access disturbance margin enhancement (Vmin Feature Control Pins)
    logic [2:0] adme;
  } impl_inp_t;

  typedef struct packed  {
    /// Power up ready negative
    logic       prn;
  } impl_oup_t;

  /// ROM control default values
  parameter bit ROM_KCS = 1'b0; // 0: disable, 1: enable
  parameter bit ROM_MCS = 1'b0; // 0: fast,    1: slow

  typedef struct packed  {
    /// Power down enable, active high (power gating)
    logic       pde;
    /// Scan enable, active high
    logic       se;
  } impl_inp_rom_t;

  typedef struct packed  {
    /// Power up ready negative
    logic       prn;
  } impl_oup_rom_t;

endpackage
