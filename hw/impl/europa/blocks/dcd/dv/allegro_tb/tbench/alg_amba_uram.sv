
module alg_amba_uram #(parameter NUM_WORD = 4096) (
  input  logic        clk,
  input  logic        wren,
  input  logic        rden,
  input  logic [$clog2(NUM_WORD)-1:0] addr,
  input  logic [71:0] data,
  output logic [71:0] q
);
logic [71:0] i_q [NUM_WORD/4096-1:0];
wire  [$clog2(NUM_WORD)-1:12] addr_high = addr[$clog2(NUM_WORD)-1:12];
logic [$clog2(NUM_WORD)-1:12] addr_high_d;

for (genvar i=0; i < NUM_WORD/4096; i=i+1) begin : uram_cut
  (* ram_style = "ultra" *) reg [71:0] mem [4096-1:0];
  always_ff @(posedge clk)
  begin
    if ((wren || rden) && (addr_high==i))
    begin
    if (wren)
      mem[addr[11:0]] <= data;
    else
      i_q[i] <= mem[addr[11:0]];
    end
  end
end : uram_cut

always_ff @(posedge clk)
  addr_high_d <= addr_high;

assign q=i_q[addr_high_d];

if (NUM_WORD%4096 != 0) begin $fatal(1,"URAM error: NUM_WORD must be multiple of 4K"); end
endmodule

