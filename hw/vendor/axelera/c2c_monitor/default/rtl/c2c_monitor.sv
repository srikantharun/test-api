// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: C2C monitor behavioral model.
//
// Authors: Bram Rooseleer
// Owner: Bram Rooseleer <bram.rooseleer@axelera.ai>

`timescale 1ns/1ps

module c2c_monitor
import c2c_monitor_pkg::*;
(
  input	  wire                    clock,
  output  wire [C2C_COUNT_W-1:0]  count_0,
  output  wire [C2C_COUNT_W-1:0]  count_1
);


  ////////////////////////
 // Internal registers //
////////////////////////

logic signed [C2C_COUNT_W-1:0] COUNT [0:2][0:3];
// initial
//   foreach(COUNT[c,p])
//     COUNT[c][p] <= 8'hxx;


  ///////////////////////
 // Monitor operation //
///////////////////////

always_ff @(posedge clock) begin
  COUNT[0][0] <= C2C_COUNT_0;
  COUNT[1][0] <= C2C_COUNT_1;
  COUNT[0][1] <= COUNT[0][0];
  COUNT[1][1] <= COUNT[1][0];
  COUNT[0][2] <= COUNT[0][1];
  COUNT[1][2] <= COUNT[1][1];
end

assign count_0 = COUNT[0][2];
assign count_1 = COUNT[1][2];


  ////////////////////////
 // Timing annotations //
////////////////////////

`ifdef IMC_SPECIFY
reg notif;
specify
  specparam
    trise=0,
    tfall=0,
    tpck=0.400,
    tnck=0.400,
    tckp=0.833,
  (posedge clock *> count_0) = (trise,tfall);
  (posedge clock *> count_1) = (trise,tfall);
  $width(posedge clock, tpck, 0, notif);
  $width(negedge clock, tnck, 0, notif);
  $period(posedge clock, tckp, notif);
  $period(negedge clock, tckp, notif);
endspecify

`endif

endmodule
