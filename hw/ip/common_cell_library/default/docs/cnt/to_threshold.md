---
title: Threshold Counter
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_cnt_to_threshold.sv:axe_ccl_cnt_to_threshold


## Features

An internal counter starts at `0` and each cycle where `enable_i == 1`, `increment_i` is added to it.
When the threshold is reached (internal count `>= threshold_i`), `pulse_o` is pulsed and the counter restarts from `enable_i ? increment_i : 0`.

Overflowing is allowed but counting integrity is not obeyed.
The surrounding logic must ensure overflowing is either safe or avoided.

Functional rule:

- `pulse_o` is asserted when the registered value of the internal sum is `>= threshold_i`. This means there is 1 cycle of latency between the increment and the associated pulse.
- `pulse_o` always tries to deassert itself once asserted, even if `enable_i == 0`. The only cases where it can remain asserted for more than 1 clock cycle is when `threshold_i == 0`, or `threshold_i == 1` and `enable_i` is continuously asserted, as described below.

Case analysis based on value of `threshold_i` (assuming `clear_i == 0`):

- If `threshold_i == 0`, `pulse_o` will be stable high every cycle regardless of `enable_i` value (assuming at least 1 cycle has elapsed since reset).
- If `threshold_i == 1`, `pulse_o` will be pulsed on the cycle after any `enable_i && (increment_i > 0)` cycle.
- If `threshold_i == N` where `N > 1`, `pulse_o` will be pulsed every `ceil(N/increment_i)` cycles (assuming `increment_i` is stable througout the count).

Example waveform for a pulse every 2 cycles:
<script type="WaveDrom">
{signal: [
  {name: 'clk', wave: 'P..........'},
  {name: 'rst_ni', wave: '01.........'},
  {name: 'clear_i', wave: '0..........'},
  {name: 'enable_i', wave: '1..........'},
  {name: 'increment_i', wave: '=..........', data: [1]},
  {name: 'threshold_i', wave: '=..........', data: [2]},

  {},

  {name: 'cnt_d', wave: '=.=========', data: [1, 2, 1, 2, 1, 2, 1, 2, 1, 2]},
  {name: 'cnt_q', wave: '=.=========', data: [0, 1, 2, 1, 2, 1, 2, 1, 2, 1]},

  {},

  {name: 'pulse_o', wave: '0..10101010'},
  {name: 'overflow_o', wave: '0..........'},
]}
</script>

`enable_i` waveform example as a variant of the previous example where `enable_i` is deasserted when `pulse_o == 1`:
<script type="WaveDrom">
{signal: [
  {name: 'clk', wave: 'P..............'},
  {name: 'rst_ni', wave: '01.............'},
  {name: 'clear_i', wave: '0..............'},
  {name: 'enable_i', wave: '1..01.01.01.01.'},
  {name: 'increment_i', wave: '=..............', data: [1]},
  {name: 'threshold_i', wave: '=..............', data: [2]},

  {},

  {name: 'cnt_d', wave: '=.=============', data: [1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]},
  {name: 'cnt_q', wave: '=.=============', data: [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1]},

  {},

  {name: 'pulse_o', wave: '0..10.10.10.10.'},
  {name: 'overflow_o', wave: '0..............'},
]}
</script>
