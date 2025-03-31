
module alg_amba_vip_base_vldrdy_pipe #(
  parameter RSTPOL            = 0,
  parameter NO_PIPE           = 1,
  parameter DATA_WIDTH        = 1
)(
  
  input  logic                      rstn,
  input  logic                      clk,
  
  input  logic                      in_valid,
  input  logic  [DATA_WIDTH-1:0]    in_data,
  output logic                      in_ready,
  
  output logic                      out_valid,
  output logic  [DATA_WIDTH-1:0]    out_data,
  input  logic                      out_ready
);

logic                  buf1_valid;
logic                  buf1_ready;
logic [DATA_WIDTH-1:0] buf1_data;
logic                  buf2_valid;
logic [DATA_WIDTH-1:0] buf2_data;
logic                  buf2_ready;

logic                  next_output;

generate

if (NO_PIPE == 1) begin: G_NO_PIPE

  assign out_valid = in_valid;
  assign out_data  = in_data;
  assign in_ready  = out_ready;

end else begin: G_PIPE

  
  assign next_output = (buf1_valid || buf2_valid) && (!out_valid || out_ready);
  assign buf1_ready  = next_output && !buf2_valid;
  assign buf2_ready  = next_output && buf2_valid;
  always_ff @(posedge clk) begin
    if (rstn == RSTPOL) begin
      out_valid <= 1'b0;
      out_data  <= '0;
    end else begin
      if (next_output) begin
        out_valid <= 1'b1;
        out_data  <= buf2_valid ? buf2_data : buf1_data;
      end else begin
        if (out_ready) begin
          out_valid <= 1'b0;
        end
      end
    end
  end

  
  always_ff @(posedge clk) begin
    if (rstn == RSTPOL) begin
      in_ready    <= 1'b0;
      buf1_valid  <= 1'b0;
      buf1_data   <= '0;
      buf2_valid  <= 1'b0;
      buf2_data   <= '0;
    end else begin

      
      in_ready  <= 1'b0;
      if (!buf1_valid || buf1_ready) begin
        in_ready  <= 1'b1;
      end

      
      if (in_valid && in_ready) begin
        buf1_valid  <= 1'b1;
        buf1_data   <= in_data;
        if (buf1_valid && !buf1_ready) begin
          buf2_valid  <= 1'b1;
        end
        buf2_data   <= buf1_data;
      end else begin
        if (buf1_ready) begin
          buf1_valid  <= 1'b0;
        end
        if (buf2_ready) begin
          buf2_valid  <= 1'b0;
        end
      end
    end
  end

end
endgenerate

endmodule
