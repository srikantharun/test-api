---
title: Stream Elastic Register
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/cc_stream_reg_el.sv:cc_stream_reg_el:parameter_table


## Operation Principle

```mermaid
    graph LR
        A>stream_inp] --> B{cc_stream_reg_el}
        B --> C>stream_oup]
```

This module does not cut any timing paths between its inputs and outputs.

## Example Waveforms

To illustrate the workings of this fall-through register, the following waves show some example transactions:

<script type="WaveDrom">
{signal: [
  {name: 'in_vld',  wave: '1....01...010.'},
  {name: 'in_rdy',  wave: '1..01...01....'},
  {name: 'in_data', wave: '2222.0222.020.', data: ['1', '2','3','4','5','6','7','8']},
  {name: 'STALL?', wave: '7..9737.97373.'},
  {},
  {name: 'fall-through reg', wave: 'z.55.5z.5.5z..', data: ['2','3','4','6','7','8']},
  {},
  {name: 'out_vld',  wave: '1...........0.'},
  {name: 'out_rdy',  wave: '10101..0.1....'},
  {name: 'out_data', wave: '22.2.222..220.', data: ['1', '2','3','4','5','6','7','8']},
  {name: 'STALL?', wave: '79797..9.7..3.'},
  ],
  config: { hscale: 0 },
  head:{
  	text: 'Elastic Fall-Through Register, in_vld = "1111_0111_0100", out_rdy = "1010_1110_0111"'
  },
  foot: {
   text: 'Elastically absorbs backpressure stalls of length 1, keeps up steady state when possible.',
    tock: 1
  }
}
</script>
