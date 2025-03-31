





module alg_ram_worden #(parameter NUM_WORD = 1, parameter DATA_WIDTH = 1, parameter BYTE_SIZE = 0, parameter WORDEN_WIDTH = 1, parameter TRISTATE = 1, parameter SOFT_ERROR_RESILIENT = 0) (
  al_ram_byteen_if.slavemod ram
);

localparam I_BYTE_SIZE = (BYTE_SIZE ==0)? 1 : BYTE_SIZE;
logic rdenff;
logic [DATA_WIDTH - 1 : 0] i_q;
logic [DATA_WIDTH - 1 : 0] i_tq;
logic [DATA_WIDTH - 1 : 0] mem [NUM_WORD - 1 : 0] /* synthesis syn_ramstyle = "no_rw_check" */  ;
logic [NUM_WORD - 1 : 0]   i_xcheck;

always_ff @(posedge ram.clk)
begin
  if (ram.wren)
    for (int i = 0; i < WORDEN_WIDTH; i++)
      if (ram.byteen[i])
        mem[ram.addr][I_BYTE_SIZE*(i+1)-1 -: I_BYTE_SIZE] <= ram.data[I_BYTE_SIZE*(i+1)-1 -: I_BYTE_SIZE];
  if (ram.rden)
    i_q <= mem[ram.addr];
  rdenff <= ram.rden;
end

`ifdef INSERT_SOFT_ERROR_NOPP
  logic [DATA_WIDTH - 1 : 0]   q_mask;
  always_ff @ (posedge ram.clk or negedge ram.rstn)
    if (!ram.rstn) begin
      q_mask <= 1;
    end else begin
      if (rdenff) begin
        q_mask[0] <= q_mask[DATA_WIDTH-1];
        q_mask[DATA_WIDTH-1:1] <= q_mask[DATA_WIDTH-2:0];
      end
    end
  if(SOFT_ERROR_RESILIENT)
    assign i_tq = i_q ^ q_mask;
  else
    assign i_tq = i_q;
`else
  assign i_tq = i_q;
`endif

generate
  if (TRISTATE == 1) begin
    assign ram.q = (rdenff) ? i_tq : 'Z;
  end else begin
    assign ram.q = i_tq;
  end
endgenerate

`ifndef SYNTHESIS
always_ff @(posedge ram.clk)
begin
  assert (!(ram.wren && ram.rden)) else $error("*-*-*-*-*-*-*-*-* MEMORY ACCESS ERROR *-*-*-*-*-*-*-*-*");
  assert (!((ram.wren || ram.rden) && ram.addr > NUM_WORD-1)) else $error("*-*-*-*-*-*-*-*-* MEMORY ADDRESS ERROR *-*-*-*-*-*-*-*-*");
end
`endif



`ifdef RAM_COVERAGE_NOPP
  covergroup toggle_read with function sample(int bit_num, bit bit_val);
    coverpoint bit_val { bins value[] = {0,1}; type_option.weight = 0; }
    coverpoint bit_num { bins bit_number[] = {[0:$clog2(NUM_WORD)-1]}; type_option.weight = 0; }
    cp_bitXval : cross bit_num, bit_val;
  endgroup
  covergroup toggle_write with function sample(int bit_num, bit bit_val);
    coverpoint bit_val { bins value[] = {0,1}; type_option.weight = 0; }
    coverpoint bit_num { bins bit_number[] = {[0:$clog2(NUM_WORD)-1]}; type_option.weight = 0; }
    cp_bitXval : cross bit_num, bit_val;
  endgroup
  toggle_read toggle_read_i = new();
  toggle_write toggle_write_i = new();
  always @(posedge ram.clk) begin
    for(int i=0;i<$clog2(NUM_WORD);i++) begin
      if (ram.rden==1) begin
        toggle_read_i.sample(i,ram.addr[i]);
      end
      if (ram.wren==1) begin
        toggle_write_i.sample(i,ram.addr[i]);
      end
    end
  end
`ifdef RAM_COVERAGE_DEBUG_NOPP
  covergroup Ram_Addr @(posedge (ram.clk));
    option.name         = "Address_Coverage";
    option.comment      = "Report Ram Coverage : Single Port Ram";

    c_raddr : coverpoint ram.addr iff(ram.rden == 1){
      bins addr[] = {[0 : NUM_WORD - 1]};
    }
    c_waddr : coverpoint ram.addr iff(ram.wren == 1){
      bins addr[] = {[0 : NUM_WORD - 1]};
    }
  endgroup
  Ram_Addr Ram_Addr_inst = new();
`endif
`endif



endmodule


