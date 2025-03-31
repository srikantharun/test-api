

module ro_module 
#(
    parameter RO_M_DOUT = 1
)(
    input  logic clk,
    input  logic running,
    input  logic i_use,
    input  logic rst,

    output logic [RO_M_DOUT-1:0] count
);

always @(posedge clk or rst) begin
    if (rst) begin
        count <= 0;
    end
    if (i_use & running) begin
        count <= count + 1;
    end
end

endmodule
