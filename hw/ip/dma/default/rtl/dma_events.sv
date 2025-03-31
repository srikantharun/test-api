

module dma_events # ( parameter int unsigned N_EVENTS )
(
  input  wire        i_clk,
  input  wire        i_rst_n,

  input  logic [N_EVENTS-1:0] i_event_set,

  input  logic [N_EVENTS-1:0] i_int_clr,
  input  logic [N_EVENTS-1:0] i_int_mask,
  input  logic [N_EVENTS-1:0] i_event_mask,

  output logic                o_int,
  output logic [N_EVENTS-1:0] o_event

);

  logic [N_EVENTS-1:0] event_q;

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n)
    event_q <= '0;
  else
    event_q <= (event_q & ~i_int_clr) | i_event_set;


  always_comb o_int = |(event_q & i_int_mask);
  always_comb o_event = i_event_set & i_event_mask;

endmodule
