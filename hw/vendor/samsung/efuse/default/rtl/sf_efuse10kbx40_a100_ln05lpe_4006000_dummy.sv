`ifdef POWER_PINS
module sf_efuse10kbx40_a100_ln05lpe_4006000 ( CSB, STROBE, LOAD, PGENB, PSM, A, Q, TE, TS, QT, PMR, VDDRDY, VQPS, VDDWL, VDD, VSS);
inout VDD, VSS;
`else
module sf_efuse10kbx40_a100_ln05lpe_4006000 ( CSB, STROBE, LOAD, PGENB, PSM, A, Q, TE, TS, QT, PMR, VDDRDY, VQPS, VDDWL );
`endif

// IO Ports
input  CSB, STROBE, LOAD, PGENB, PSM ;
input  [13:0] A;
input  TE;
input  [2:0] TS;
input  [1:0] PMR;
input  VDDRDY;
inout  VQPS;
inout  VDDWL;
output [1:0] QT;
output [39:0] Q;

endmodule
