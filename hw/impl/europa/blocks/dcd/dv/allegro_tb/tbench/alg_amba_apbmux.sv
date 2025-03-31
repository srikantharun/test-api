




module alg_amba_apbmux #(parameter ADDR_WIDTH = 22) (

  input                clk      ,
  input                rstn     ,
  input  logic [ADDR_WIDTH-1:0] s0_addr,
  input  logic         s0_enable,
  output logic [31:0]  s0_rdata ,
  output logic         s0_ready ,
  input  logic         s0_sel   ,
  input  logic [31:0]  s0_wdata ,
  input  logic         s0_write ,
  input  logic [ADDR_WIDTH-1:0] s1_addr,
  input  logic         s1_enable,
  output logic [31:0]  s1_rdata ,
  output logic         s1_ready ,
  input  logic         s1_sel   ,
  input  logic [31:0]  s1_wdata ,
  input  logic         s1_write ,
  output logic [ADDR_WIDTH-1:0] m_addr,
  output logic         m_enable ,
  input  logic [31:0]  m_rdata  ,
  input  logic         m_ready  ,
  output logic         m_sel    ,
  output logic [31:0]  m_wdata  ,
  output logic         m_write
);

  typedef enum logic [1:0] {S_IDLE, S_SETUP, S_ACCESS, S_END} State;
  State state;
  logic select;

  always_ff @ (posedge clk or negedge rstn)
  if (rstn == 0) begin
    state     <= S_IDLE;
    select    <= '0;
    m_enable  <= '0;
    m_sel     <= '0;
    m_addr    <= '0;
    m_write   <= '0;
    m_wdata   <= '0;
    s0_ready  <= '0;
    s0_rdata  <= '0;
    s1_ready  <= '0;
    s1_rdata  <= '0;
  end else begin
    case (state)
      S_SETUP : begin
        if ((s0_enable && select) ||
            (s1_enable && ~select)) begin
          m_enable  <= '1;
          state             <= S_ACCESS;
        end
      end
      S_ACCESS : begin
        if (m_ready) begin
          m_sel     <= '0;
          m_enable  <= '0;
          if (select) begin
            s0_ready   <= '1;
            s0_rdata   <= m_rdata;
          end else begin
            s1_ready   <= '1;
            s1_rdata   <= m_rdata;
          end
          state             <= S_END;
        end
      end
      S_END : begin
        s0_ready   <= '0;
        s1_ready   <= '0;
        state             <= S_IDLE;
      end
      default : begin
        if (s0_sel && ~(s1_sel && select)) begin
          select           <= '1;
          m_sel    <= '1;
          m_write  <= s0_write;
          m_addr   <= s0_addr;
          m_wdata  <= s0_wdata;
          state            <= S_SETUP;
        end else begin
          if (s1_sel) begin
            select           <= '0;
            m_sel    <= '1;
            m_write  <= s1_write;
            m_addr   <= s1_addr;
            m_wdata  <= s1_wdata;
            state            <= S_SETUP;
          end
        end
      end
    endcase

  end

endmodule

