// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>
//        Tiago Campos <tiago.campos@axelera.ai>


package vendor_cva6v_pkg;

  // Define a dummy probe struct used for synthesis only
  typedef struct packed {
    logic csr;
    logic instr;
  } rvfi_probes_t;

  parameter int unsigned USE_LVT_MEMS = 0;

endpackage : vendor_cva6v_pkg
