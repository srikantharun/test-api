// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: svs monitor behavioral model.
//
// Authors: Bram Rooseleer, Bob Vanhoof, Mohit Gupta
// Owner: Mohit Gupta

`timescale 1ns/1ps

`define FASTSIM 0

module svs_monitor
import svs_monitor_pkg::*;
(
  input	  wire                       clock,
  input   wire                       enable,

  input   wire                       ref_clock,

  input   wire [SVS_TARGET_W-1:0]    target,

  input   wire [SVS_NB_MONITOR-1:0]  use_ro,

  output  wire                       valid,
  output  wire [SVS_COUNT_W-1:0]     count_0,
  output  wire [SVS_COUNT_W-1:0]     count_1,
  output  wire [SVS_COUNT_W-1:0]     count_2,
  output  wire [SVS_COUNT_W-1:0]     count_3,
  output  wire [SVS_COUNT_W-1:0]     count_4,
  output  wire [SVS_COUNT_W-1:0]     count_5,
  output  wire [SVS_COUNT_W-1:0]     count_6,
  output  wire [SVS_COUNT_W-1:0]     count_7,
  output  wire [SVS_COUNT_W-1:0]     count_8,
  output  wire [SVS_COUNT_W-1:0]     count_9,
  output  wire [SVS_COUNT_W-1:0]     count_10,
  output  wire [SVS_COUNT_W-1:0]     count_11,
  output  wire [SVS_COUNT_W-1:0]     count_12,
  output  wire [SVS_COUNT_W-1:0]     count_13,
  output  wire [SVS_COUNT_W-1:0]     count_14,
  output  wire [SVS_COUNT_W-1:0]     count_15,
  output  wire [SVS_COUNT_W-1:0]     count_16,
  output  wire [SVS_COUNT_W-1:0]     count_17,
  output  wire [SVS_COUNT_W-1:0]     count_18,
  output  wire [SVS_COUNT_W-1:0]     count_19,
  output  wire [SVS_COUNT_W-1:0]     count_20,
  output  wire [SVS_COUNT_W-1:0]     count_21,
  output  wire [SVS_COUNT_W-1:0]     count_22,
  output  wire [SVS_COUNT_W-1:0]     count_23,
  output  wire [SVS_COUNT_W-1:0]     count_24,
  output  wire [SVS_COUNT_W-1:0]     count_25,
  output  wire [SVS_COUNT_W-1:0]     count_26,
  output  wire [SVS_COUNT_W-1:0]     count_27,
  output  wire [SVS_COUNT_W-1:0]     count_28,
  output  wire [SVS_COUNT_W-1:0]     count_29
);


// Quick sanity check on parameters
// * interface port sizes are hardcoded due to timing annotations
// * multidimensional interface ports are split (also hardcoded)
// * logical limitations

// synopsys translate_off
initial begin
  assert(SVS_NB_MONITOR == 30);
  assert(SVS_COUNT_W == 16);
end
// synopsys translate_on

// sig dec
logic enable_capt;
logic clock_settings;
logic running, stop;
logic reset_monitor, running_rst;
logic enable_sync;

// synchronize enable
always_ff @(posedge clock) begin
    enable_capt <= enable;
end

// clock gate
assign clock_settings = (clock && !enable_capt);

// expand outputs
logic [SVS_COUNT_W-1:0] count [SVS_NB_MONITOR-1:0];

assign count_0 = count[0];
assign count_1 = count[1];
assign count_2 = count[2];
assign count_3 = count[3];
assign count_4 = count[4];
assign count_5 = count[5];
assign count_6 = count[6];
assign count_7 = count[7];
assign count_8 = count[8];
assign count_9 = count[9];
assign count_10 = count[10];
assign count_11 = count[11];
assign count_12 = count[12];
assign count_13 = count[13];
assign count_14 = count[14];
assign count_15 = count[15];
assign count_16 = count[16];
assign count_17 = count[17];
assign count_18 = count[18];
assign count_19 = count[19];
assign count_20 = count[20];
assign count_21 = count[21];
assign count_22 = count[22];
assign count_23 = count[23];
assign count_24 = count[24];
assign count_25 = count[25];
assign count_26 = count[26];
assign count_27 = count[27];
assign count_28 = count[28];
assign count_29 = count[29];


// input capturing
logic [SVS_TARGET_W-1:0] target_capt;
logic [SVS_NB_MONITOR-1:0] use_capt;

always_ff @(posedge clock_settings) begin
    target_capt <= target;
    use_capt <= use_ro;
end

// reset generation
assign reset_monitor = !enable_capt;
assign running_rst = reset_monitor || stop;

// set generation
always_ff @(posedge ref_clock) begin
    enable_sync <= enable_capt;
end

always @(running_rst or posedge enable_sync) begin
    if (running_rst) begin
        running <= 0;
    end else if (enable_sync) begin
            running <= 1;
    end
end

// target counter
logic [2**SVS_TARGET_W-1:0] target_count, counter;

assign target_count = 1 << target_capt;

always_ff @(posedge ref_clock or reset_monitor) begin
    if (reset_monitor) begin
        stop <= 0;
        counter <= 0;
    end
    if (running) begin
        stop <= 0;
        counter <= counter + 1;
        if (counter >= target_count) begin
            stop <= 1;
        end
    end
end

// output enable
logic complete;
always_ff @(posedge clock) begin
    complete <= stop;
end

assign valid = complete && enable_capt;

// delay lines
logic [SVS_COUNT_W-1:0] count_int [SVS_NB_MONITOR-1:0];

genvar i;

generate
    for (i=0; i<SVS_NB_MONITOR; i++) begin
        ro_module #(
            .RO_M_DOUT(SVS_COUNT_W)
        )
        ro_inst (
            .clk(clock),
            .running(running),
            .i_use(use_capt[i]),
            .rst(reset_monitor),
            .count(count_int[i])
        );
    end
endgenerate

generate
    for (i=0; i<SVS_NB_MONITOR; i++) begin
        assign count[i] = count_int[i] & {(SVS_COUNT_W-1){valid}};
    end
endgenerate

endmodule
