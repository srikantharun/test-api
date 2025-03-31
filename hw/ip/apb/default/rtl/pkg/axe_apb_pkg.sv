// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: abhishek maringanti <abhishek.maringanti@axelera.ai>

//! APB Package
/// Contains all necessary type definitions, constants, and generally useful functions.
///
package axe_apb_pkg;

  /// APB Transaction Prot Width.
  parameter int unsigned APB_PROT_WIDTH = 3;

  /// APB Transaction Protection Type.
  typedef logic [APB_PROT_WIDTH-1:0]  apb_prot_t;

endpackage
