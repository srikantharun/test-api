// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


// Randomizing Stream (Ready/Valid) Master
module cc_stream_rand_man #(
  parameter type  data_t = logic,
  // Minimum number of clock cycles to wait between applying two consecutive values.
  parameter int   MinWaitCycles = -1,
  // Maximum number of clock cycles to wait between applying two consecutive values.
  parameter int   MaxWaitCycles = -1,
  // Application delay: time delay before output changes after an active clock edge.
  parameter realtime ApplTime = 0.0ps,
  // Acquisition delay: time delay before ready input is read after an active clock edge.
  parameter realtime TestTime = 0.0ps,
  // Store each output beat in an internal queue.
  parameter bit   Enqueue = 1'b0
)(
  input  wire   i_clk,
  input  wire   i_rst_n,

  output data_t o_data,
  output logic  o_valid,
  input  logic  i_ready
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
        if (o_valid && i_ready) begin
          queue.push_back(o_data);
        end
      end
    end
  end

  int unsigned rand_wait_cycles;

  function automatic void randomize_wait_cycles();
    int unsigned rand_success;
    rand_success = std::randomize(rand_wait_cycles) with {
      rand_wait_cycles >= MinWaitCycles;
      rand_wait_cycles <= MaxWaitCycles;
    };
    assert (rand_success) else $error("Failed to randomize wait cycles!");
  endfunction

  initial begin
    o_data  = '0;
    o_valid = 1'b0;
    wait (i_rst_n);
    // Initially pick a random number of cycles to wait until we offer the first valid data.
    randomize_wait_cycles();
    @(posedge i_clk);
    forever begin
      // Wait for the picked number of clock cycles.
      repeat(rand_wait_cycles) begin
        @(posedge i_clk);
      end
      // Delay application of data and valid output.
      #(ApplTime);
      // Randomize data output and set valid output.
      void'(std::randomize(o_data));
      o_valid = 1'b1;
      // Delay acquisition of ready signal. TestTime is relative to the clock edge, and we have
      // already waited for ApplTime in this edge, so we need to subtract ApplTime.
      #(TestTime-ApplTime);
      // Sample the ready input. While the slave is not ready, wait a clock cycle plus the
      // acquisition delay and resample the ready input.
      while (!i_ready) begin
        @(posedge i_clk);
        #(TestTime);
      end
      // The slave is ready to acquire data on the next rising edge, so we pick a new number of
      // cycles to wait until we offer the next valid data.
      randomize_wait_cycles();
      if (rand_wait_cycles == 0) begin
        // If we have to wait 0 cycles, we apply new data directly after next clock edge plus the
        // application delay.
        @(posedge i_clk);
      end else begin
        // If we have to wait more than 0 cycles, we unset the valid output and randomize the data
        // output after the next clock edge plus the application delay.
        @(posedge i_clk);
        #(ApplTime);
        o_valid = 1'b0;
        void'(std::randomize(o_data));
      end
    end
  end
endmodule
