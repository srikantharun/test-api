module alg_amba_check_syncy #(
  parameter CORE          = 0,
  parameter PULSE_MODE    = 0,
  parameter RASTER_EN     = 0,
  parameter CHROMA_EN     = 0,
  parameter MAP_EN        = 0,
  parameter ADDR_START    = 0,
  parameter ADDR_ADDR     = 0,
  parameter ADDR_CHROMA   = 0,
  parameter ADDR_RASTER   = 0,
  parameter ADDR_HEIGHT   = 0,
  parameter ADDR_PITCH    = 0,
  parameter PITCH_START   = 0,
  parameter PITCH_END     = 0,
  parameter ID            = 0
)(
  input  logic       pclk   ,
  input  logic       prstn  ,
  input  logic[15:0] paddr  ,
  input  logic       psel   ,
  input  logic       penable,
  input  logic[31:0] pwdata ,
  input  logic       pwrite ,
  
  input  logic       aclk,
  input  logic       arstn,
  input  logic[4:0]  awid,
  input  logic[63:0] awaddr,
  input  logic       awvalid,
  input  logic       awready,
  
  input  logic[13:0] al_sync_y,
  input  logic       reset_stat,
  output logic       sync_status
);


logic al_sync_eof;
logic al_sync_eol;
logic i_start;
logic [63:0] addr;
logic [31:0] pitch;
logic [31:0] pitchmap;
logic [31:0] height;
logic [13:0] i_sync_y;
logic [11:0] i_pulse_cnt;
logic [63:0] i_buffmin_addr;
logic [63:0] i_buffmax_addr;
logic i_wren;
logic en_core;
logic dis_raster;
logic i_420;

assign al_sync_eol = al_sync_y[0];
assign al_sync_eof = al_sync_y[1];

always @(posedge aclk, negedge arstn)
begin
  if (!arstn) begin
    i_pulse_cnt <= '0;
    i_sync_y <= '0;
  end else begin
    if (PULSE_MODE)
      i_sync_y <= i_pulse_cnt;
    else
      i_sync_y <= al_sync_y*4;
    if (PULSE_MODE) begin
      if (i_start) begin
        i_pulse_cnt <= '0;
      end else
        i_pulse_cnt <= i_pulse_cnt + (al_sync_eol<<2);
    end
  end
end

always @(posedge aclk, negedge arstn)
begin
  if (!arstn) begin
    i_buffmin_addr <= '0;
    i_buffmax_addr <= '0;
  end else begin
    if (MAP_EN) begin
      if (CHROMA_EN) begin
        i_buffmin_addr <= i_sync_y[13:3]*pitchmap + addr;
        i_buffmax_addr <= height*pitchmap + addr;
      end else begin
        i_buffmin_addr <= i_sync_y[13:2]*pitchmap + addr;
        i_buffmax_addr <= height*2*pitchmap + addr;
      end
    end else begin
      if (RASTER_EN) begin
        if (CHROMA_EN) begin
          if (i_420) begin
            i_buffmin_addr <= i_sync_y*pitch[31:1] + addr;
            i_buffmax_addr <= height*8*pitch[31:1] + addr;
          end else begin
            i_buffmin_addr <= i_sync_y*pitch + addr;
            i_buffmax_addr <= height*8*pitch + addr;
          end
        end else begin
          i_buffmin_addr <= i_sync_y*pitch + addr;
          i_buffmax_addr <= height*8*pitch + addr;
        end
      end else begin
        if (CHROMA_EN) begin
          i_buffmin_addr <= i_sync_y[13:4]*pitch + addr;
          i_buffmax_addr <= height*pitch + addr;
        end else begin
          i_buffmin_addr <= i_sync_y[13:2]*pitch + addr;
          i_buffmax_addr <= height*2*pitch + addr;
        end
      end
    end
  end
end

always @(posedge pclk, negedge prstn)
begin
  if (!prstn) begin
    addr                          <= '0;
    pitch                         <= '0;
    height                        <= '0;
    pitchmap                      <= '0;
    i_start                       <= '0;

    en_core                       <= '1;
    dis_raster                    <= '0;
    i_420                         <= '0;
    pitchmap                      <= '0;
  end else begin
    i_start <= 0;
    if (psel && penable && pwrite) begin
      case(paddr)
        16'h0060+(4*CORE): en_core <= pwdata[CORE];
        ADDR_RASTER   : begin
                          if(!RASTER_EN) begin dis_raster <= pwdata[24]; end
                          pitchmap <= 1<<(!pwdata[22]+5);
                        end
        ADDR_ADDR     : addr[31:0]  <= pwdata;
        ADDR_ADDR+4   : addr[63:32]  <= pwdata;
        ADDR_CHROMA   : if(pwdata[25:24]==2'b01) begin i_420 <= '1; end
        ADDR_PITCH    : pitch  <= pwdata[PITCH_END:PITCH_START];
        ADDR_HEIGHT   : height <= pwdata[21:11]+1;
        ADDR_START    : i_start     <= 1;
      endcase
    end
  end
end

assign i_wren = (awid == ID && awaddr >= addr && awaddr < i_buffmax_addr) ? awvalid && awready : 0;

always @(posedge aclk, negedge arstn)
begin
  if (!arstn) begin
    sync_status <= '0;
  end else begin
    if (reset_stat)
      sync_status <= 0;
    if (i_wren && (awaddr < i_buffmin_addr)) begin
      sync_status <= !dis_raster & en_core;
      if (PULSE_MODE)
        $error ("[SYNC] ERROR sync_eol/sync_eof at address:0x%x < 0x%x",awaddr,i_buffmin_addr);
      else
        $error ("[SYNC] ERROR sync_y at address:0x%x < 0x%x",awaddr,i_buffmin_addr);
    end
    if (i_wren)
      if (PULSE_MODE)
        $display ("[SYNC] Check sync_eol/sync_eof at address:0x%x >= 0x%x",awaddr,i_buffmin_addr);
      else
        $display ("[SYNC] Check sync_y at address:0x%x >= 0x%x",awaddr,i_buffmin_addr);
  end
end

endmodule
