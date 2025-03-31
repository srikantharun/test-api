




module alg_amba_vip_apbdemux #(parameter ADDR_WIDTH = 32, parameter NUM_SLAVES = 2) (

  input  logic                                  clk    ,
  input  logic                                  rstn   ,
  input  logic                                  psel   ,
  input  logic                                  penable,
  input  logic                                  pwrite ,
  input  logic [31:0]                           pwdata ,
  input  logic [21:0]                           paddr  ,
  output logic [31:0]                           prdata ,
  output logic                                  pready ,
  output logic                                  pintreq,
  output logic                                  pslverr,
  input  logic [NUM_SLAVES-1:0][ADDR_WIDTH-1:0] slv_address_begin,
  input  logic [NUM_SLAVES-1:0][ADDR_WIDTH-1:0] slv_address_end  ,
  input  logic [NUM_SLAVES-1:0][ADDR_WIDTH-1:0] slv_address_mask ,
  output logic [NUM_SLAVES-1:0]                 slv_psel   ,
  output logic [NUM_SLAVES-1:0]                 slv_penable,
  output logic [NUM_SLAVES-1:0]                 slv_pwrite ,
  output logic [NUM_SLAVES-1:0][31:0]           slv_pwdata ,
  output logic [NUM_SLAVES-1:0][21:0]           slv_paddr  ,
  input  logic [NUM_SLAVES-1:0][31:0]           slv_prdata ,
  input  logic [NUM_SLAVES-1:0]                 slv_pready ,
  input  logic [NUM_SLAVES-1:0]                 slv_pintreq,
  input  logic [NUM_SLAVES-1:0]                 slv_pslverr
);

  localparam ID_MSB  =  NUM_SLAVES==1?0:$clog2(NUM_SLAVES)-1;
  typedef enum logic [1:0] {S_IDLE, S_SETUP, S_ACCESS, S_READY} State;
  State i_state;
  logic i_psel;
  logic i_penable;
  logic i_pwrite;
  logic i_noone;
  logic [31:0]                 i_pwdata;
  logic [ADDR_WIDTH-1:0]       i_paddr;
  logic [ID_MSB:0]             i_id;
  logic [NUM_SLAVES-1:0]       i_ready;
  logic [NUM_SLAVES-1:0]       i_slverr;
  logic [NUM_SLAVES-1:0][31:0] i_rdata;

  always_ff @ (posedge clk or negedge rstn)
  if (rstn == 0) begin
    i_state          <= S_IDLE;
    i_psel           <= '0;
    i_penable        <= '0;
    i_pwrite         <= '0;
    i_pwdata         <= '0;
    i_paddr          <= '0;
    i_noone          <= '0;
    i_id             <= '0;
    pready           <= '0;
    prdata           <= '0;
    pslverr          <= '0;
  end else begin
    case (i_state)
      S_SETUP : begin
        if (penable) begin
          i_penable <= '1;
          i_state   <= S_ACCESS;
        end
      end
      S_ACCESS : begin
        if (i_noone) begin
          i_psel    <= '0;
          i_penable <= '0;
          pready    <= '1;
          pslverr   <= '0;
          prdata    <= '0;
          i_state   <= S_READY;
        end
        else if (i_ready[i_id]) begin
          i_psel    <= '0;
          i_penable <= '0;
          pready    <= '1;
          pslverr   <= i_slverr[i_id];
          prdata    <= i_rdata[i_id];
          i_state   <= S_READY;
        end
      end
      S_READY : begin
        pready    <= '0;
        pslverr   <= '0;
        i_state   <= S_IDLE;
      end
      default : begin
        if (psel) begin
          i_id    <= '0;
          i_noone <= '1;
          i_paddr <= '0;
          for (int i = 0; i < NUM_SLAVES; i++) begin
            if (paddr[ADDR_WIDTH-1:0] >= slv_address_begin[i] && paddr[ADDR_WIDTH-1:0] < slv_address_end[i]) begin
              i_paddr <= paddr & slv_address_mask[i];
              i_id    <= i;
              i_noone <= 0;
            end
          end
          i_psel    <= '1;
          i_pwrite  <= pwrite;
          i_pwdata  <= pwdata;
          i_state   <= S_SETUP;
        end
      end
    endcase

  end

  generate
    for (genvar i = 0; i < NUM_SLAVES; i++) begin : g_assign
      assign slv_psel[i]    = (i_id!=i)? '0 : i_psel & ~i_noone;
      assign slv_penable[i] = (i_id!=i)? '0 : i_penable & ~i_noone;
      assign slv_pwrite[i]  = (i_id!=i)? '0 : i_pwrite & ~i_noone;
      assign slv_paddr[i]   = (i_id!=i)? '0 : i_paddr;
      assign slv_pwdata[i]  = (i_id!=i)? '0 : i_pwdata;
      assign i_ready[i]     = (i_id!=i)? '0 : slv_pready[i];
      assign i_slverr[i]    = (i_id!=i)? '0 : slv_pslverr[i];
      assign i_rdata[i]     = (i_id!=i)? '0 : slv_prdata[i];
    end
  endgenerate

  always_ff @ (posedge clk or negedge rstn)
  if (rstn == 0) begin
    pintreq     <= '0;
  end else begin
    pintreq     <= |slv_pintreq;
  end

endmodule

