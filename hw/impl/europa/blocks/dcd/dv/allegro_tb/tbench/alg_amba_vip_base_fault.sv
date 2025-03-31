






module alg_amba_vip_base_fault #(
  parameter DATA_WIDTH = 128,
  parameter FAULT_WIDTH = 128,
  parameter ID_WIDTH = 1
)(
  
  input  logic                  clk,
  input  logic                  rstn,
  
  input  logic                  restart,
  input  logic[19:0]            seed,
  input  logic[19:0]            probThresReq, 
  input  logic[FAULT_WIDTH-1:0] regPattern,
  input  logic[3:0]             cmd,
  input  logic[ID_WIDTH-1:0]    id,
  output logic[31:0]            stats_lfsr,
  output logic[31:0]            stats_nberror,
  output logic[31:0]            stats_nbrequest,
  
  output logic[ID_WIDTH-1:0]    m_id,
  output logic[DATA_WIDTH-1:0]  m_data,
  output logic                  m_valid,
  input  logic                  m_ready,
  
  input  logic[ID_WIDTH-1:0]    s_id,
  input  logic[DATA_WIDTH-1:0]  s_data,
  input  logic                  s_valid,
  output logic                  s_ready
);
localparam DATA_WLG2 = $clog2(FAULT_WIDTH);

logic                          i_fifo_wreq;
logic[ID_WIDTH+DATA_WIDTH-1:0] i_fifo_wdata;
logic                          i_fifo_wfull;
logic                          i_fifo_rreq;
logic[ID_WIDTH+DATA_WIDTH-1:0] i_fifo_rdata;
logic                          i_fifo_rempty;

logic[ID_WIDTH-1:0]            i_rid;
logic[DATA_WIDTH-1:0]          i_rdata;

logic                          i_lfsrShift;
logic[19:0]                    i_lfsr;

logic                          i_fault_valid;
logic                          i_fault_enable;
logic[FAULT_WIDTH-1:0]         i_fault_data;
logic[FAULT_WIDTH-1:0]         i_fault_PartialMask;
logic[DATA_WLG2-1:0]           i_fault_id1;
logic[DATA_WLG2-1:0]           i_fault_id2;
logic[DATA_WLG2-1:0]           i_fault_id1_byte;
logic[DATA_WLG2-1:0]           i_fault_id2_byte;
logic[DATA_WLG2-1:0]           i_fault_start;
logic[DATA_WLG2-1:0]           i_fault_end;



assign i_fifo_wreq = (~i_fifo_wfull) & s_valid;


assign i_fifo_wdata = {s_id,s_data};


assign i_rid   = i_fifo_rdata[ID_WIDTH+DATA_WIDTH-1:DATA_WIDTH];
assign i_rdata = i_fifo_rdata[DATA_WIDTH-1:0];

alg_amba_vip_base_fifo_fwft #(.FIFO_WIDTH(ID_WIDTH+DATA_WIDTH),.FIFO_LOG2_DEPTH(1)) I_IN_FIFO (
  .rstn        (rstn),
  .clk         (clk),
  .wreq        (i_fifo_wreq),
  .wfull       (i_fifo_wfull),
  .wdata       (i_fifo_wdata),
  .rreq        (i_fifo_rreq),
  .rempty      (i_fifo_rempty),
  .rdata       (i_fifo_rdata)
);

assign i_fifo_rreq = (~i_fifo_rempty) & m_ready;


always_ff @(posedge clk)
begin
  if(!rstn) begin
    i_lfsr            <= 20'b0;
  end else begin
    if (restart) begin
      i_lfsr          <= seed;
    end else if(i_lfsrShift) begin
      i_lfsr[0]       <= i_lfsr[19] ^ i_lfsr[16];
      i_lfsr[19:1]    <= i_lfsr[18:0];
    end
  end
end

assign i_lfsrShift         = i_fifo_rreq && i_fault_valid;

assign i_fault_valid       = (i_rid == id)           ? 1'b1 : 1'b0;
assign i_fault_enable      = (i_lfsr < probThresReq) ? 1'b1 : 1'b0;

assign i_fault_id1         = i_lfsr[DATA_WLG2-1:0];
assign i_fault_id2         = i_lfsr[19:19-DATA_WLG2];
assign i_fault_id1_byte    = {i_fault_id1[DATA_WLG2-1:3],3'b000};
assign i_fault_id2_byte    = {i_fault_id2[DATA_WLG2-1:3],3'b000};
assign {i_fault_start,i_fault_end} = (i_fault_id1 < i_fault_id2) ? {i_fault_id1,i_fault_id2} : {i_fault_id2,i_fault_id1};
always_comb
begin
  i_fault_PartialMask <= 0;
  for(int unsigned i=0; i<FAULT_WIDTH; i++) begin
    if (i >= i_fault_start && i <= i_fault_end)
      i_fault_PartialMask[i] <= 1'b1;
  end
end


always_comb
begin
  case(cmd)
    4'hA : begin 
      i_fault_data = i_rdata;
      i_fault_data[i_fault_id1_byte+:7] =  i_rdata[i_fault_id2_byte+:7];
      i_fault_data[i_fault_id2_byte+:7] =  i_rdata[i_fault_id1_byte+:7];
    end
    4'h9 : begin 
      i_fault_data = i_rdata;
      i_fault_data[i_fault_id1] =  i_rdata[i_fault_id2];
      i_fault_data[i_fault_id2] =  i_rdata[i_fault_id1];
    end
    4'h8 : begin 
      for(int unsigned i=0; i<FAULT_WIDTH; i++)
        i_fault_data[i] = (i_fault_PartialMask[i]) ? ~i_rdata[i] : i_rdata[i];
    end
    4'h7 : begin 
      i_fault_data = ~i_rdata;
    end
    4'h6 : begin 
      for(int unsigned i=0; i<FAULT_WIDTH; i++)
        i_fault_data[i] = (i_fault_PartialMask[i]) ? i_rdata[i] | regPattern[i] : i_rdata[i];
    end
    4'h5 : begin 
      for(int unsigned i=0; i<FAULT_WIDTH; i++)
        i_fault_data[i] = (i_fault_PartialMask[i]) ? i_rdata[i] & regPattern[i] : i_rdata[i];
    end
    4'h4 : begin 
      for(int unsigned i=0; i<FAULT_WIDTH; i++)
        i_fault_data[i] = (i_fault_PartialMask[i]) ? i_rdata[i] ^ regPattern[i] : i_rdata[i];
    end
    4'h3 : begin 
      i_fault_data = i_rdata | regPattern;
    end
    4'h2 : begin 
      i_fault_data = i_rdata & regPattern;
    end
    4'h1 : begin 
      i_fault_data = i_rdata ^ regPattern;
    end
    default : begin 
      i_fault_data = i_rdata;
    end
  endcase
end

assign s_ready                          = !(i_fifo_wfull);

assign m_id                             = i_rid;
assign m_data[DATA_WIDTH-1:FAULT_WIDTH] = i_rdata[DATA_WIDTH-1:FAULT_WIDTH];
assign m_data[FAULT_WIDTH-1:0]          = (i_fault_valid && i_fault_enable) ? i_fault_data : i_rdata[FAULT_WIDTH-1:0];
assign m_valid                          = !(i_fifo_rempty);



assign stats_lfsr = i_lfsr;
always_ff @(posedge clk)
begin
  if(!rstn) begin
    stats_nberror       <= 0;
    stats_nbrequest     <= 0;
  end else begin
    if (restart) begin
      stats_nberror     <= 0;
      stats_nbrequest   <= 0;
    end else begin
      if (i_fifo_rreq)
        stats_nbrequest <= stats_nbrequest + 1;
      if (i_fifo_rreq && i_fault_valid && i_fault_enable)
        stats_nberror   <= stats_nberror   + 1;
    end
  end
end

















































endmodule

