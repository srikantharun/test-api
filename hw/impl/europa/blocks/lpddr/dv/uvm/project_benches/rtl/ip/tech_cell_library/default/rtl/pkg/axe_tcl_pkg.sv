// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Package containing common definitions for all tech_cells
///
package axe_tcl_pkg;

  /// Type for specifying if a sram request is active this cycle
  typedef enum logic {
    SramReqActive = 1'b1,
    SramReqIdle   = 1'b0
  } sram_req_t;

  /// Type for write / read selection
  typedef enum logic {
    SramWrite = 1'b1,
    SramRead  = 1'b0
  } sram_we_t;

  /// RAM Margin control default values
  parameter bit [1:0] MCS  = 2'b01;
  parameter bit       MCSW = 1'b0;
  parameter bit [2:0] ADME = 3'b100;

  `ifndef SYNTHESIS
  // TODO: Deprecate.
  /// Function to print the configuration in simulation
  function automatic void print_sram_configuration (
    int unsigned NumPorts,
    int unsigned AddrWidth,
    int unsigned DataWidth,
    int unsigned ByteWidth,
    int unsigned BeWidth,
    int unsigned NumWords,
    int unsigned Latency,
    string       ImplKey = "default"
  );
    $info(
      "#################################################################################\n",
      "axe_tcl_sram instantiated with the configuration:\n",
      "Number of ports   (dec): %d\n", NumPorts,
      "Number of words   (dec): %d\n", NumWords,
      "Address width     (dec): %d\n", AddrWidth,
      "Data width        (dec): %d\n", DataWidth,
      "Byte width        (dec): %d\n", ByteWidth,
      "Byte enable width (dec): %d\n", BeWidth,
      "Latency Cycles    (dec): %d\n", Latency,
      "ImplKey           (str): %s\n", ImplKey,
      "#################################################################################"
    );
  endfunction
  `endif

endpackage
