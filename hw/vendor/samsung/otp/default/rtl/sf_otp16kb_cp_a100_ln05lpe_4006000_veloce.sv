// dummy version of:
// /data/foundry/samsung/sf5a/ip/samsung/sf_otp_cp_a100_ln05lpe_4006000_V1.01/./FE-Common/MODEL/sf_otp16kb_cp_a100_ln05lpe_4006000.v

module sf_otp16kb_cp_a100_ln05lpe_4006000 (

  ADD,
  CEB,
  CLE,
  CPUMPEN,
  PGMEN,
  DLE,
  DIN,
  READEN,
  RSTB,
  WEB,
  VDDRDY,
  CLK,
  CLKEN,

  DOUT,
  LOCK,


  VTDO,
  VREFM,
  VPP
  );

  parameter ADDR_WIDTH = 14;
  parameter DOUT_WIDTH = 32;
  parameter DIN_WIDTH = 1;
  parameter OTP_DEPTH = 1 << ADDR_WIDTH;
  parameter LOCK_DEPTH = 8;  // 8bit lock, other fuse

  input CPUMPEN;  // charge pump enable high
  input [ADDR_WIDTH-1:0] ADD;  // address
  input CEB;  // chip enable, active low
  input CLE;  // command latch enable
  input PGMEN;  // program enable
  input READEN;  // read enable
  input RSTB;  // reset, active low
  input WEB;  // write enable low
  input VDDRDY;
  input CLK;
  input CLKEN;
  input DIN;
  input DLE;


  output [DOUT_WIDTH-1:0] DOUT;  // data out
  output [LOCK_DEPTH-1:0] LOCK;


  inout VTDO;
  inout VREFM;
  inout VPP;

  wire  [ADDR_WIDTH-1:0] addr;    // address

  wire           rd_en;
  wire           pg_en;
  wire           ceb;
  wire           cle;
  wire           dle;
  wire           rstb;
  wire           web;
  wire     [0:0] din;
  wire           cpumpen;

  wire vddrdy;
  wire otpclk;
  wire otpclken;

  wire vtdo;
  wire vrefm;
  wire vpp;
  wire vcp;           // prog voltage source

  reg   [LOCK_DEPTH-1:0] lock;
  wire  [LOCK_DEPTH-1:0] lock_i;

  reg [DOUT_WIDTH-1:0] dout;

  nmos (rd_en,     READEN,     1'b1);
  nmos (pg_en,     PGMEN,      1'b1);
  nmos (ceb,       CEB,        1'b1);
  nmos (cle,       CLE,        1'b1);
  nmos (dle,       DLE,        1'b1);
  nmos (rstb,      RSTB,       1'b1);
  nmos (web,       WEB,        1'b1);
  nmos (cpumpen,   CPUMPEN,    1'b1);
  nmos (din[0],       DIN,        1'b1);

  genvar g1;
  generate
    for (g1=0; g1<ADDR_WIDTH; g1=g1+1) begin :addr_loop
      nmos (addr[g1],      ADD[g1],       1'b1);
    end
  endgenerate

  nmos (vddrdy,       VDDRDY,     1'b1);
  nmos (otpclk,      CLK,       1'b1);
  nmos (otpclken,      CLKEN,       1'b1);

  generate
    for (g1=0; g1<DOUT_WIDTH; g1=g1+1) begin :dout_loop
      nmos (DOUT[g1],      dout[g1],       1'b1);
    end
  endgenerate

  nmos (LOCK[0],      lock_i[0],       1'b1);
  nmos (LOCK[1],      lock_i[1],       1'b1);
  nmos (LOCK[2],      lock_i[2],       1'b1);
  nmos (LOCK[3],      lock_i[3],       1'b1);
  nmos (LOCK[4],      lock_i[4],       1'b1);
  nmos (LOCK[5],      lock_i[5],       1'b1);
  nmos (LOCK[6],      lock_i[6],       1'b1);
  nmos (LOCK[7],      lock_i[7],       1'b1);

  nmos (vtdo,       VTDO,        1'b1);
  nmos (vrefm,      VREFM,       1'b1);
  nmos (vpp,      VPP,       1'b1);

  //----------------------------------------------

  // pragma attribute mem0 logic_block 1
  reg [DIN_WIDTH-1:0]  mem0 [0:OTP_DEPTH-1]; // main mem array
  // pragma attribute mem1 logic_block 1
  reg [DIN_WIDTH-1:0]  mem1 [0:OTP_DEPTH-1]; // redundant mem array

  //read operation
  reg [DOUT_WIDTH-1:0] dout_reg='0;
  reg [ADDR_WIDTH-1:0] read_addr='0;

  assign read_addr = (addr & 32'hFFFF_FFE0); //remove the lower 5 bits (32 bits addressing)

  always @(negedge otpclk) begin
    if(rd_en) begin
      for(bit [31:0] i=0; i<DOUT_WIDTH; i++) begin
        dout_reg[i] <= mem0[read_addr+i];
      end
    end
    else begin
      dout_reg <= '0;
    end
  end
  generate
    for(genvar i=0; i<DOUT_WIDTH; i++) begin
      assign dout[i] = (rd_en && (~ceb)) ? mem0[read_addr+i] : dout_reg[i];
    end
  endgenerate

  //program operation (write)
  reg data2wr=0;
  reg mem2wr=0;

  always @(negedge web) begin
    if((~web) && (dle)) begin
      data2wr <= din;
    end
    if((~web) && pg_en && cpumpen) begin
      if(din) begin
        if(mem2wr==0) mem0[addr] <= data2wr;
        else          mem1[addr] <= data2wr;

        mem2wr <= mem2wr+1; //wrap around when mem2wr is 1
      end
    end
  end

endmodule
