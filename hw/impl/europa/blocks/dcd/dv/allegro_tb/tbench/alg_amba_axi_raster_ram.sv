module alg_amba_axi_raster_ram #(parameter NUM_WORD = 8192) (
  input  logic         clk,
  input  logic         wren,
  input  logic         rden,
  input  logic [$clog2(NUM_WORD)-1:0]  addr,
  input  logic [127:0] data,
  output logic [127:0] q
);

logic [127:0] mem [NUM_WORD-1:0];

always_ff @(posedge clk)
begin
  if (wren)
    mem[addr] <= data;
  if (rden)
    q <= mem[addr];
end
endmodule

