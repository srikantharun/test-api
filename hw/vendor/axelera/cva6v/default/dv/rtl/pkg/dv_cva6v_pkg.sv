// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>


package vendor_cva6v_pkg;

  import cva6v_pve_pkg::*;
  import raptor_pkg::*;
  import cva6v_config_pkg::*;
  `include "cva6v/include/rvfi_types.svh"
  `include "cva6v/include/cva6v/cva6v_tracing.svh"
  `include "../cva6v_dv_typedefs.svh"

  parameter int unsigned USE_LVT_MEMS = 0;

endpackage : vendor_cva6v_pkg
