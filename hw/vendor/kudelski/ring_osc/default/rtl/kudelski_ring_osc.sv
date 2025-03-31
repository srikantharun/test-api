// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
//
// Kudelski Ring Oscillator behavioural model wrapper.
//

module kudelski_ring_osc
#(
  parameter int unsigned N_BITS   = 8,
  parameter type ro_clk_t = logic[N_BITS-1:0]
) (
  input  logic      i_en,
  output ro_clk_t   o_ro_clk
);

generate
  for (genvar i=0; i<N_BITS; i++) begin : ro_gen

    ro #(
      .SEED_SEL (i)
    ) u_ring_osc_bit (
      .en_i     (i_en),
      .clk_o    (o_ro_clk[i])
    );

  end
endgenerate

endmodule
