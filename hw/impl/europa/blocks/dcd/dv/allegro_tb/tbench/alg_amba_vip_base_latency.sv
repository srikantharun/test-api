
module alg_amba_vip_base_latency #(
  parameter DATA_WIDTH = 128,
  parameter PROB_EN = 1
)(
  
  input  logic                         clk,
  input  logic                         resetn,
  
  input  logic [7:0]                   proba,
  input  logic [15:0]                  seed,
  input  logic                         seed_rst,
  input  logic [15:0]                  min,
  input  logic [15:0]                  width_mask,
  
  output logic                         m_valid,
  output logic [DATA_WIDTH-1:0]        m_data,
  input  logic                         m_ready,
  
  input  logic                         s_valid,
  input  logic [DATA_WIDTH-1:0]        s_data,
  output logic                         s_ready
);

logic [15:0] cnt;

logic [15:0] lfsr_latency;
logic [15:0] lfsr_latency_next;

logic [7:0]  lfsr_proba;
logic [7:0]  lfsr_proba_next;


assign lfsr_proba_next[0]    = lfsr_proba[3] ^ lfsr_proba[4] ^ lfsr_proba[5] ^ lfsr_proba[7];
assign lfsr_proba_next[7:1]  = lfsr_proba[6:0];
always_ff @(posedge clk)
begin
  if (~resetn) begin
    lfsr_proba        <= '0;
  end else begin
    if (seed_rst) begin
      lfsr_proba      <= seed[7:0];
    end else if (s_valid & s_ready) begin
      lfsr_proba      <= lfsr_proba_next;
    end
  end
end


assign lfsr_latency_next[0]     = lfsr_latency[3] ^ lfsr_latency[12] ^ lfsr_latency[14] ^ lfsr_latency[15];
assign lfsr_latency_next[15:1]  = lfsr_latency[14:0];
always_ff @(posedge clk)
begin
  if (~resetn) begin
    lfsr_latency        <= '0;
  end else begin
    if (seed_rst) begin
      lfsr_latency      <= seed;
    end else if (s_valid & s_ready) begin
      lfsr_latency      <= lfsr_latency_next;
    end
  end
end


assign m_valid = (cnt == 0) ? s_valid : 1'b0;
assign s_ready = (cnt == 0) ? m_ready : 1'b0;
assign m_data  = s_data;
always_ff @(posedge clk)
begin
  if (~resetn) begin
    cnt        <= '0;
  end else begin
    if (cnt > 0 && s_valid) begin
      cnt      <= cnt - 1;
    end else begin
      cnt      <= '0;
      if (((PROB_EN == 0) || (lfsr_proba <= proba)) && !(s_valid && !s_ready)) begin
        cnt      <= min + (width_mask & lfsr_latency_next);
      end
    end
  end
end

endmodule
