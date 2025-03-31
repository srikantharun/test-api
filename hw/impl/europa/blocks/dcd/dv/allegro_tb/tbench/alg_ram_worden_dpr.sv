





module alg_ram_worden_dpr #(parameter NUM_WORD = 1, parameter DATA_WIDTH = 1, parameter BYTE_SIZE = 0, parameter WORDEN_WIDTH = 1, parameter SOFT_ERROR_RESILIENT = 0) (
  al_ram_dpr_byteen_if.slavemod ram
);

localparam I_BYTE_SIZE = (BYTE_SIZE ==0)? 1 : BYTE_SIZE;
logic [DATA_WIDTH - 1 : 0]   mem [0 : NUM_WORD - 1] /* synthesis syn_ramstyle = "no_rw_check" */  ;
logic                        rdenff;
logic [WORDEN_WIDTH - 1 : 0] byteenff;
logic [DATA_WIDTH - 1 : 0]   i_q;
logic [DATA_WIDTH - 1 : 0]   i_tq;
logic [NUM_WORD - 1 : 0]     i_xcheck;


`ifndef SYNTHESIS
always_ff @(posedge ram.clk)
begin
  
  assert (!(ram.wren && ram.waddr > NUM_WORD-1)            ) else $error("*-*-*-*-*-*-*-*-* MEMORY ADDRESS ERROR *-*-*-*-*-*-*-*-*");
  assert (!(ram.rden && ram.raddr > NUM_WORD-1)            ) else $error("*-*-*-*-*-*-*-*-* MEMORY ADDRESS ERROR *-*-*-*-*-*-*-*-*");
end
`endif

always_ff @(posedge ram.clk)
begin
  if (ram.wren) begin
    for (int i = 0; i < WORDEN_WIDTH; i++) begin
      if (ram.byteen[i])
        mem[ram.waddr][i*I_BYTE_SIZE +: I_BYTE_SIZE] <= ram.wdata[i*I_BYTE_SIZE +: I_BYTE_SIZE];
    end
  end
  if (ram.rden)
    i_q <= mem[ram.raddr];

  rdenff   <= ram.rden;
  byteenff <= (ram.wren && ram.rden && ram.waddr == ram.raddr) ? ram.byteen : '0;
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
    for (genvar i = 0; i < WORDEN_WIDTH; i++) begin
      assign ram.rdata[i*I_BYTE_SIZE +: I_BYTE_SIZE] = (!byteenff[i]) ? i_tq[i*I_BYTE_SIZE +: I_BYTE_SIZE] : 'Z;
    end
  endgenerate

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
        toggle_read_i.sample(i,ram.raddr[i]);
      end
      if (ram.wren==1) begin
        toggle_write_i.sample(i,ram.waddr[i]);
      end
    end
  end
`ifdef RAM_COVERAGE_DEBUG_NOPP
  covergroup Ram_Addr @(posedge (ram.clk));
    option.name         = "Address_Coverage";
    option.comment      = "Report Ram Coverage : Single Port Ram";

    c_raddr : coverpoint ram.raddr iff(ram.rden == 1){
      bins addr[] = {[0 : NUM_WORD - 1]};
    }
    c_waddr : coverpoint ram.waddr iff(ram.wren == 1){
      bins addr[] = {[0 : NUM_WORD - 1]};
    }
  endgroup
  Ram_Addr Ram_Addr_inst = new();
`endif
`endif



endmodule
