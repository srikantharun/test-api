// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// An AXI endpoint with a FIFO to put in some messages for different cores to fetch.
///
module axi_mailbox #(
  /// The depth of the Fifo that is instantiated
  parameter int unsigned MailboxDepth = 16
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  input  wire i_rst_n,

  input  axi_mailbox_csr_reg_pkg::axi_a_ch_h2d_t i_axi_s_aw,
  output logic                                   o_axi_s_aw_ready,
  input  axi_mailbox_csr_reg_pkg::axi_w_ch_h2d_t i_axi_s_w,
  output logic                                   o_axi_s_w_ready,
  output axi_mailbox_csr_reg_pkg::axi_b_ch_d2h_t o_axi_s_b,
  input  logic                                   i_axi_s_b_ready,
  input  axi_mailbox_csr_reg_pkg::axi_a_ch_h2d_t i_axi_s_ar,
  output logic                                   o_axi_s_ar_ready,
  output axi_mailbox_csr_reg_pkg::axi_r_ch_d2h_t o_axi_s_r,
  input  logic                                   i_axi_s_r_ready,

  /// Interrupt
  output logic o_irq
);
  ///////////////////////////////
  // Parameters and Sanitation //
  ///////////////////////////////
  if (MailboxDepth < 1)   $fatal(1, "MailboxDepth has to be at least 2");
  if (MailboxDepth > 128) $fatal(1, "MailboxDepth has to be at less than 128");

  localparam int unsigned FifoUsageWidth = $clog2(MailboxDepth);

  // Note thiss ic currently hardcoded in the CSR generator
  localparam int unsigned AxiDataWidth = 64;
  typedef logic[AxiDataWidth-1:0] axi_data_t;
  if ($bits(i_axi_s_w.data) != AxiDataWidth) $fatal(1, "Parameter: '$bits(i_axi_s_w.data)' must be 64;");
  if ($bits(o_axi_s_r.data) != AxiDataWidth) $fatal(1, "Parameter: '$bits(o_axi_s_r.data)' must be 64;");

  // Note: We define the threshold registers to be 8-bit wide.
  // To ease implementaion we limit the maximum depth to 128 entries.
  localparam int unsigned CsrUsageWidth = 8;
  typedef logic [CsrUsageWidth-1:0] csr_usage_t;

  ///////////////
  // Registers //
  ///////////////
  axi_mailbox_csr_reg_pkg::axi_mailbox_csr_reg2hw_t reg2hw;
  axi_mailbox_csr_reg_pkg::axi_mailbox_csr_hw2reg_t hw2reg;


  axi_mailbox_csr_reg_top u_axi_mailbox_csr_reg_top (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    .axi_aw_i   (i_axi_s_aw),
    .axi_awready(o_axi_s_aw_ready),
    .axi_ar_i   (i_axi_s_ar),
    .axi_arready(o_axi_s_ar_ready),
    .axi_w_i    (i_axi_s_w),
    .axi_wready (o_axi_s_w_ready),
    .axi_b_o    (o_axi_s_b),
    .axi_bready (i_axi_s_b_ready),
    .axi_r_o    (o_axi_s_r),
    .axi_rready (i_axi_s_r_ready),
    .reg2hw,
    .hw2reg,
    .devmode_i  (1'b1)
  );

  //////////
  // FIFO //
  //////////

  logic fifo_full;
  logic fifo_push;
  logic fifo_empty;
  logic fifo_pop;

  always_comb fifo_push = reg2hw.mboxw.qe & ~fifo_full;

  always_comb hw2reg.error.write_error.d  = fifo_full;
  always_comb hw2reg.error.write_error.de = reg2hw.mboxw.qe;

  // If empty and read we want to give bax magic number.
  axi_data_t fifo_rdata;
  assign hw2reg.mboxr.d = fifo_empty ? axi_data_t'(32'hFEED_DEAD) : fifo_rdata;

  always_comb fifo_pop = reg2hw.mboxr.re & ~fifo_empty;

  always_comb hw2reg.error.read_error.d  = fifo_empty;
  always_comb hw2reg.error.read_error.de = reg2hw.mboxr.re;

  // Special case for a power of 2 depth
  logic [FifoUsageWidth-1:0] fifo_usage;
  csr_usage_t                usage;

  if (!(MailboxDepth & (MailboxDepth-1))) begin : gen_usage_pow_2
    always_comb usage = csr_usage_t'({fifo_full, fifo_usage});
  end else begin : gen_usage
    always_comb usage = csr_usage_t'(fifo_usage);
  end

  fifo_v3 #(
    .FALL_THROUGH(1'b0),
    .DEPTH       (MailboxDepth),
    .dtype_t     (axi_data_t)
  ) u_fifo_mailbox (
    .i_clk,
    .i_rst_n,
    .flush_i   (reg2hw.ctrl.wfifo.q | reg2hw.ctrl.rfifo.q),
    .testmode_i(1'b0),
    .full_o    (fifo_full),
    .empty_o   (fifo_empty),
    .usage_o   (fifo_usage),
    .data_i    (reg2hw.mboxw.q),
    .push_i    (fifo_push),
    .data_o    (fifo_rdata),
    .pop_i     (fifo_pop)
  );

  ////////////////////////////
  // Threshold calculations //
  ////////////////////////////
  logic over_write_threshold;
  logic over_read_threshold;

  always_comb over_write_threshold = usage > reg2hw.wirqt.q;
  always_comb over_read_threshold  = usage > reg2hw.rirqt.q;

  ////////////////
  // Interrupts //
  ////////////////
  logic dbg_sw_interrupt;

  assign hw2reg.irqs.wtirq.d            = 1'b1;
  assign hw2reg.irqs.rtirq.d            = 1'b1;
  assign hw2reg.irqs.eirq.d             = 1'b1;
  assign hw2reg.irqs.dbg_sw_interrupt.d = 1'b1;

  // Error signals can level trigger the interrupt if its IRQ is enabled
  assign hw2reg.irqs.wtirq.de = over_write_threshold;
  assign hw2reg.irqs.rtirq.de = over_read_threshold;
  assign hw2reg.irqs.eirq.de = |reg2hw.error;
  assign hw2reg.irqs.dbg_sw_interrupt.de = dbg_sw_interrupt;

  assign hw2reg.irqp = reg2hw.irqs & reg2hw.irqen;
  always_comb o_irq  = |hw2reg.irqp;


  // Connect the DBG_SW_IRQ to the error signal
  assign dbg_sw_interrupt = reg2hw.ctrl.dbg_sw_irq.q;

  ////////////
  // Status //
  ////////////
  assign hw2reg.status.empty.d  = fifo_empty;
  assign hw2reg.status.full.d   = fifo_full;
  assign hw2reg.status.wfifol.d = over_write_threshold;
  assign hw2reg.status.rfifol.d = over_read_threshold;
endmodule
