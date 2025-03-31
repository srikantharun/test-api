// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

// Thermal  Management Supervisor (TMS).
// common cell to perorm edge edetection
`ifndef TMS_EDGE_DETECT_SV
`define TMS_EDGE_DETECT_SV
module tms_edge_detect (
  // Clock, positive edge triggered
  input  wire                         i_clk   ,
  // Asynchronous reset, active low
  input  wire                         i_rst_n ,
  // data to edge detect
  input  logic                        din     ,
  // rising edge detect
  output logic                        redge   ,
  // falling edge detect
  output logic                        fedge   ,
  // any edge detect
  output logic                        aedge
);

//==============================================================================
// Local parameters


//==============================================================================
// signal declarations
logic data_reg;

//==============================================================================
// RTL

// edge momnitor control
always_comb begin
  // rising edge detect. input high and register low
  redge =  din & ~data_reg;
  // falling edge detect. input low and register high
  fedge = ~din &  data_reg;
  // pulse for any edge
  aedge =  din ^  data_reg;
end

// input register
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    data_reg <= 1'h0;
  end else begin
    data_reg <= din;
  end
end

endmodule
`endif // TMS_EDGE_DETECT_SV

