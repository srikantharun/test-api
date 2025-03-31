
module alg_amba_vip_base_apb_stage (
  al_vip_apb_if.slavemod               s_apb,
  al_vip_apb_if.mastermod              m_apb
);

logic        s_apb_request_toggle;

logic        m_apb_request;
logic        m_apb_request_ff1;
logic        m_apb_request_ff2;

logic        m_apb_ready_toggle;
logic [31:0] m_apb_rdata;
logic        m_apb_slverr;

logic        s_apb_ready;
logic        s_apb_ready_ff1;
logic        s_apb_ready_ff2;

always_ff @(posedge s_apb.clk) begin
  if (!s_apb.rstn) begin
    s_apb_request_toggle    <= 1'b0;
    s_apb_ready             <= 1'b0;
    s_apb_ready_ff1         <= 1'b0;
    s_apb_ready_ff2         <= 1'b0;
    s_apb.ready             <= 1'b0;
    s_apb.slverr            <= 1'b0;
    s_apb.rdata             <= '0;
  end else begin

    if (s_apb.sel & !s_apb.enable) begin
      s_apb_request_toggle  <= ~s_apb_request_toggle;
    end

    s_apb_ready       <= m_apb_ready_toggle;
    s_apb_ready_ff1   <= s_apb_ready;
    s_apb_ready_ff2   <= s_apb_ready_ff1;

    s_apb.ready       <= 1'b0;
    if (s_apb_ready_ff1 != s_apb_ready_ff2) begin
      s_apb.ready     <= 1'b1;
      s_apb.slverr    <= m_apb_slverr;
      s_apb.rdata     <= m_apb_rdata;
    end

  end
end

always_ff @(posedge m_apb.clk) begin
  if (~m_apb.rstn) begin
    m_apb_request       <= 1'b0;
    m_apb_request_ff1   <= 1'b0;
    m_apb_request_ff2   <= 1'b0;
    m_apb_ready_toggle  <= 1'b0;
    m_apb_rdata         <= '0;
    m_apb_slverr        <= '0;
    m_apb.sel           <= 1'b0;
    m_apb.enable        <= 1'b0;
    m_apb.addr          <= '0;
    m_apb.wdata         <= '0;
    m_apb.write         <= 1'b0;
  end else begin

    m_apb_request       <= s_apb_request_toggle;
    m_apb_request_ff1   <= m_apb_request;
    m_apb_request_ff2   <= m_apb_request_ff1;

    if (m_apb_request_ff1 != m_apb_request_ff2) begin
      m_apb.sel          <= 1'b1;
      m_apb.addr         <= s_apb.addr;
      m_apb.wdata        <= s_apb.wdata;
      m_apb.write        <= s_apb.write;
    end else if (m_apb.sel && m_apb.enable && m_apb.ready) begin
      m_apb.sel          <= 1'b0;
      m_apb.enable       <= 1'b0;
      m_apb_ready_toggle <= ~m_apb_ready_toggle;
      m_apb_rdata        <= m_apb.rdata;
      m_apb_slverr       <= m_apb.slverr;
    end else begin
      m_apb.enable       <= m_apb.sel;
    end

  end
end

endmodule
