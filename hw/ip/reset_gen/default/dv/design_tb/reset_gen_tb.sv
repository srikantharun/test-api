module reset_gen_tb;

  localparam DATA_W = 2;

  bit                  clk_i;
  bit                  rst_ni;
  bit [DATA_W - 1 : 0] a_i;
  bit [DATA_W - 1 : 0] b_i;
  bit [DATA_W - 1 : 0] out_o;

  reset_gen #( .DATA_W (DATA_W))
  reset_gen_inst (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .a_i    (a_i),
    .b_i    (b_i),
    .out_o  (out_o)
  );

  initial begin
    rst_ni = 0;
    #100;
    rst_ni = 1;
    #100;
    a_i = 0;
    b_i = 0;
    #100;
    a_i = 1;
    b_i = 1;
    #100;
    $finish;
  end

  always begin
    clk_i <= 1; #5;
    clk_i <= 0; #5;
  end

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end

endmodule
