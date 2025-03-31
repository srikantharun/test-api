---
title: "Stream Fall-Through Register"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/cc_stream_reg_ft.sv:cc_stream_reg_ft


## Operation Principle

```mermaid
    graph LR
        A>stream_inp] --> B{cc_stream_reg_ft}
        B --> C>stream_oup]
```

This module does cut the timing path on the `ready` signals going from downstream to upstream. There are combinational paths from upstream to downstream.

## Example Waveforms

To illustrate the workings of this fall-through register following waves show three examples of transactions between it's input and output stream.

1. Singe transaction where the downstream acknowledges in the same cycle.
2. Single transaction where the output stream is stalled for one cycle. The data is cunsumed directly, as the upsream ready is driven by the module state.
2. Back to back transactions are possible.

<script type="WaveDrom">
{signal: [
  {name: 'i_clk', wave: 'lp..lp...lp...l'},
  {},
  [ 'Inp Stream',
    {name: 'i_data',   wave: 'xx2xxx2xxx.22xx', data: ['1', '2', '3', '4']},
    {name: 'i_valid' , wave: 'x010x010.x01.0x'},
    {name: 'o_ready' , wave: 'x1..x1.01x1...x'}
  ],
  {},
  [ 'Oup Stream',
    {name: 'o_data',   wave: 'xx2xxx2.xx.22xx', data: ['1', '2', '3', '4']},
    {name: 'o_valid' , wave: 'x010x01.0x01.0x'},
    {name: 'i_ready' , wave: 'x010x0.10x01.0x'}
  ],
  {},
  {name: '', wave: 'x.2x..22x..22x.', data: ['TNX1', 'STALL', 'TNX2', 'TNX3', 'TNX4']},
  {name: '', wave: 'x2..x2...x2...x', data: ['EG1: Transaction', 'EG2: Stalled Transaction', 'EG2: Default Ready']},
],
 foot:{
   text: '',
   tock:0
 },
  config: { hscale: 1.5}
}
</script>
