


module europa_lpddr_async_perf_counter #(
  parameter int CounterWidth = 32,
  parameter int SyncStages = 3
) (

  // Signals sync to the count clk
  input wire i_count_clk,
  input wire i_count_rst_n,
  input logic i_count_inc,

  // Signals sync to the ctrl_clk
  input wire i_ctrl_clk,
  input wire i_ctrl_rst_n,
  input logic i_ctrl_cnt_en,
  input logic i_ctrl_cnt_flush,
  output logic [CounterWidth-1:0] o_ctrl_cnt_value
);

  typedef logic [CounterWidth-1:0] counter_w_t;

  // Synchronise the count_cnt_en flag to the counter clock domain.
  // This value is considered quasi static, so a simple sync stages suffices
  logic count_cnt_en;
  axe_tcl_seq_sync #(
    .SyncStages(SyncStages),
    .ResetValue(0)
  ) cnt_en_sync_inst (
    /// Clock to synchronize to, positive edge triggered
    .i_clk (i_count_clk),
    // doc async
    /// Asynchronous reset, active low
    .i_rst_n (i_count_rst_n),
    // doc async
    /// Data input
    .i_d (i_ctrl_cnt_en),
    // doc sync i_clk
    /// Synchronized data output
    .o_q (count_cnt_en)
  );

  // Synchronise the counter flush pulse to the counter clock domain.
  // Flush will be a pulse type signal in the ctrl domain, so using a cdc pulse stage here.
  logic count_cnt_flush;
  axe_ccl_cdc_pulse #(
    .SyncStages(SyncStages)
  ) flush_sync_inst (
    /// Source domain clock, positive edge triggered
    .i_src_clk (i_ctrl_clk),
    /// Source domain asynchronous reset, active low
    .i_src_rst_n (i_ctrl_rst_n),
    /// Source domain input pulse
    .i_src_pulse (i_ctrl_cnt_flush),
    /// Source domain busy flag, input pulses are ignored!
    .o_src_busy (),
    /// Source domain error flag, Pulse was not propagated.
    .o_src_error (),

    /// Destination domain clock, positive edge triggered
    .i_dst_clk (i_count_clk),
    /// Destination domain asynchronous reset, active low
    .i_dst_rst_n (i_count_rst_n),
    /// Destination domain pulse
    .o_dst_pulse (count_cnt_flush)
  );

  // The actual counter running in the count clock domain.
  // Increments when count_inc input is high and count_en ctrl flag is high.
  // Flushes using the flush pulse above, setting to a specific value is not implemented
  counter_w_t count_cnt_value;
  cc_cnt_delta #(
    .Width (CounterWidth),
    .StickyOverflow(1'b0)
  ) counter_inst (
    .i_clk (i_count_clk),
    .i_rst_n (i_count_rst_n),
    .i_cnt_en (i_count_inc & count_cnt_en),
    .i_flush (count_cnt_flush),
    .o_q (count_cnt_value),
    .i_cnt_down(1'b0),
    .i_delta   ('1),
    .i_d       ('0),
    .i_d_load  (1'b0),
    .o_overflow(/* open */)
  );

  // Sync the output value of the counter back to the ctrl domain.
  // i_src_en of cdc_bus is set to count_cnt_en.
  // This makes the sync run constantly while the counter is on.
  // If the ctrl clock is slower than the count clock this means values will be missed.
  // However, this is the best we can do if we want the ctrl domain to be able to read the latest available value on of the counter.
  axe_ccl_cdc_bus #(
    .SyncStages(SyncStages),
    .data_t(counter_w_t)
  ) counter_output_sync_inst (
    /// Source domain clock, positive edge triggered
    .i_src_clk (i_count_clk),
    /// Source domain asynchronous reset, active low
    .i_src_rst_n (i_count_rst_n),
    /// Source domain input enable (sync this data)
    .i_src_en (count_cnt_en),
    /// Source data input
    .i_src_data (count_cnt_value),
    /// Source domain busy flag, new data sync requests are ignored while high
    .o_src_busy (),

    /// Destination domain clock, positive edge triggered
    .i_dst_clk (i_ctrl_clk),
    /// Destination domain asynchronous reset, active low
    .i_dst_rst_n (i_ctrl_rst_n),
    /// Destination domain data
    .o_dst_data (o_ctrl_cnt_value),
    /// Destination domain update pulse (new data this cycle)
    .o_dst_update ()
  );

endmodule
