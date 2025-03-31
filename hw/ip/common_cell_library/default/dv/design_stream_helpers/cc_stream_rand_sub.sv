// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Randomizing Stream (Ready/Valid) Slave
///
module cc_stream_rand_sub #(
  parameter type  data_t = logic,
  // Minimum number of clock cycles to wait between applying two consecutive values.
  parameter int   MinWaitCycles = -1,
  // Maximum number of clock cycles to wait between applying two consecutive values.
  parameter int   MaxWaitCycles = -1,
  // Application delay: time delay before output changes after an active clock edge.
  parameter realtime  ApplTime = 0.0ps,
  // Acquisition delay: time delay before ready input is read after an active clock edge.
  parameter realtime  TestTime = 0.0ps,
  // Store each inupt beat in an internal queue.
  parameter bit   Enqueue = 1'b0
)(
  input  wire i_clk,
  input  wire i_rst_n,

  input  data_t   i_data,
  input  logic    i_valid,
  output logic    o_ready
);
  //////////////////////////
  // Parameter sanitation //
  //////////////////////////
  `ifdef SYNTHESIS
    $fatal(1, "module 'cc_stream_rand_man' is NOT synthesizable!");
  `endif

  if (MinWaitCycles < 0) $fatal(1, "Parameter: 'MinWaitCycles' must be at least 0!;");
  if (MaxWaitCycles < 0) $fatal(1, "Parameter: 'MaxWaitCycles' must be at least 0!;");
  if (MaxWaitCycles < MinWaitCycles)
      $fatal(1, "Parameter: 'MaxWaitCycles' must be at least the minimum number of 'MinWaitCycles';");
  if (ApplTime == 0ps) $fatal(1, "Parameter: 'ApplTime' must be larger than 0!;");
  if (TestTime == 0ps) $fatal(1, "Parameter: 'TestTime' must be larger than 0!;");
  if (TestTime <= ApplTime) $fatal(1, "Parameter: 'TestTime' must be larger than 'Appltime';");

  /////////////////
  // Handshaking //
  /////////////////

  data_t queue[$];

  if (Enqueue) begin: gen_queue
    always @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        queue = {};
      end else begin
        #(TestTime);
        if (i_valid && o_ready) begin
          queue.push_back(i_data);
        end
      end
    end
  end

  initial begin
    automatic int unsigned rand_delay, rand_success;
    o_ready = '0;
    wait (i_rst_n);
    @(posedge i_clk);
    forever begin
      rand_success = std::randomize(rand_delay) with {
        rand_delay >= MinWaitCycles;
        rand_delay <= MaxWaitCycles;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat(rand_delay) begin
        @(posedge i_clk);
      end
      #(ApplTime);
      void'(std::randomize(o_ready));
    end
  end

endmodule
