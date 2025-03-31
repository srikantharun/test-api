---
title: Integer Clock Divider
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

Divide a clock by an integer ratio.

!!! warning "Duty Cycle"

    As this module works via a posedge Flop and negedge Latch we are susceptible to duty cycle.
    This divider can **not** be used to smoothe out non 50% duty cycle clocks. Use
    [axe_ccl_clk_div_by_2](./div_by_2.md) instead!


## Phase Calculation

The phase signals always follow the same pattern. We can use a counter, which counts up to a given division
ratio, to keep track in which part of the phase we are in. Lower part has to be `2'b11` to have the resulting
output clock high, and the higher part `2'b00` to keep it low.  For uneven divisions we need to drop the clock
on the `negedge` of the fast clock.  We find the cycle index by shifting the division ratio by `1` to the
right.  The LSB gives us the hint if we need to lower the output clock on the negedge of the fast clock.

We can visualize phase behaviour with the following table:

| divisor_q  | Binary      | 0      | 1      | 2      | 3      | 4      | 5      | 6      | 7      |
|:---------- |:----------- |:------:|:------:|:------:|:------:|:------:|:------:|:------:|:------:|
| `4'd0`     | `4'b_000_0` | `[00]` |        |        |        |        |        |        |        |
| `4'd1`     | `4'b_000_1` | `[10]` |        |        |        |        |        |        |        |
| `4'd2`     | `4'b_001_0` |  `11`  | `[00]` |        |        |        |        |        |        |
| `4'd3`     | `4'b_001_1` |  `11`  | `[10]` |  `00`  |        |        |        |        |        |
| `4'd4`     | `4'b_010_0` |  `11`  |  `11`  | `[00]` |  `00`  |        |        |        |        |
| `4'd5`     | `4'b_010_1` |  `11`  |  `11`  | `[10]` |  `00`  |  `00`  |        |        |        |
| `4'd6`     | `4'b_011_0` |  `11`  |  `11`  |  `11`  | `[00]` |  `00`  |  `00`  |        |        |
| `4'd7`     | `4'b_011_1` |  `11`  |  `11`  |  `11`  | `[10]` |  `00`  |  `00`  |  `00`  |        |
| `4'd8`     | `4'b_100_0` |  `11`  |  `11`  |  `11`  |  `11`  | `[00]` |  `00`  |  `00`  |  `00`  |


In terms of waves we are getting the following for different division ratios:

<script type="WaveDrom">
{ signal: [
  { name: "i_clk", wave: 'p..............', period: 2 },
  ['Div2',
    { name: "phase[1:0]", wave: 'x.3.5.3.5.3.5.x.x.............', data:["2b11","2b00","2b11","2b00","2b11","2b00"]},
    { name: "phase_0_q",  wave: 'x...1.0.1.0.1.0.x.............',},
    { name: "phase_1_q",  wave: 'x..1.0.1.0.1.0.x..............',},
    { name: "o_clk",      wave: 'x...h.l.h.l.h.l.x.............',},
  ],
  {},
  ['Div3',
    { name: "phase[1:0]", wave: 'x.3.8.5.3.8.5.3.8.5.x.........', data:["2b11","2b10","2b00","2b11","2b10","2b00","2b11","2b10","2b00"]},
    { name: "phase_0_q",  wave: 'x...1.0...1.0...1.0...x.......' },
    { name: "phase_1_q",  wave: 'x..1...0.1...0.1...0.x........' },
    { name: "o_clk",      wave: 'x...h..l..h..l..h..l..x.......' },
  ],
  {},
  ['Div4',
    { name: "fsm_out", wave: 'x.3...5...3...5...3...5...x...', data:["2b11","2b00","2b11","2b00","2b11", "2b00"]},
    { name: "phase_0", wave: 'x...1...0...1...0...1...0...x.' },
    { name: "phase_1", wave: 'x..1...0...1...0...1...0...x..' },
    { name: "out_clk", wave: 'x...h...l...h...l...h...l...x.' },
  ],
  {},
  ['Div5',
    { name: "fsm_out", wave: 'x.3...8.5...3...8.5...x.......', data:["2b11","2b10","2b00","2b11","2b10","2b00"]},
    { name: "phase_0", wave: 'x...1...0.....1...0.....x.....' },
    { name: "phase_1", wave: 'x..1.....0...1.....0...x......' },
    { name: "out_clk", wave: 'x....h....l....h....l....x....' },
  ],
]}
</script>


::: hw/ip/common_cell_library/default/rtl/axe_ccl_clk_div_by_int.sv:axe_ccl_clk_div_by_int

::: hw/vendor/axelera/clk_div_by_int_modulator/default/rtl/clk_div_by_int_modulator_functional.sv:clk_div_by_int_modulator
