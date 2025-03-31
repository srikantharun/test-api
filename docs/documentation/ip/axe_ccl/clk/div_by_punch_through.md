---
title: Punch Through Clock Divider
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_clk_div_by_pt.sv:axe_ccl_clk_div_by_pt

## Basic Operation

The basic operating principle is that the clock is divided by letting a percentage of input clock pulses though.
The ratio is determined by the average overflow rate of the phase accumulator.
By setting the increment accordingly any frequency division depending on `PhaseAccumulatorWidth` can be achieved.
Example waveforms for different division ratios which are generated as an example. In practice the denominator of the fraction has to be a power of 2.

| Port Name  | Description                       |
|:---------- |:--------------------------------- |
| `i_clk`    | Input clock                       |
| `i_div_en` | Divider enable                    |
| `o_active` | Internal enable of the clock gate |
| `o_clk`    | Output divided clock              |

<script type="WaveDrom">
{signal: [
  {name: 'i_clk',    wave: 'p................'},
  {name: 'i_div_en', wave: '0..1.............'},
  {},
  [ '0',
   {name: 'o_active', wave: '0...1............'},
   {name: 'o_clk',    wave: 'l....p...........'}
  ],
  {},
  [ '1/2',
   {name: 'o_active', wave: '0....101010101010'},
   {name: 'o_clk',    wave: 'l.....plplplplplp'}
  ],
  {},
  [ '1/3',
   {name: 'o_active', wave: '0.....10.10.10.10'},
   {name: 'o_clk',    wave: 'l......pl.pl.pl.p'}
  ],
  {},
  [ '2/3',
   {name: 'o_active', wave: '0....1.01.01.01.0'},
   {name: 'o_clk',    wave: 'l.....p.lp.lp.lp.'}
  ],
],
 foot:{
   tock:0
 }
}
</script>


## Setting the Division Ratio

The increment is used to set the division ratio. In short the increment value is the fixed-point representation of the division ratio.
Use this formula to calculate the desired division ratio:

$$
F_{o\_clk} = C * F_{i\_clk} | C \in [0,1]
$$

$$
F_{o\_clk} = \frac{i\_acc\_incr}{2^{PhaseAccumulatorWidth}} * F_{i\_clk}
$$

$$
i\_acc\_incr = \frac{F_{o\_clk}}{F_{i\_clk}}*2^{PhaseAccumulatorWidth} = C * 2^{PhaseAccumulatorWidth} = C << PhaseAccumulatorWidth
$$

When C is defined using fixed-point representation (`logic [-1:-PhaseAccumulatorWidth]`) the desired
fraction can be applied to `i_acc_incr` as is. Or think of `i_acc_incr` being the numerator of the fraction.
A value for `i_acc_incr` of `'0` will apply a division ratio of 1 (always enabled).
