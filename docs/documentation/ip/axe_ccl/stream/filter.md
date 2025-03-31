---
title: Stream Filter
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/cc_stream_filter.sv:cc_stream_filter


## Operation Principle

```mermaid
    graph LR
        A>stream_inp] --> B{cc_stream_filter}
        S[i_drop] --> B
        B --> C>stream_oup]
        B --> D[o_dropped]
```

The data runs outside the module, as only the handshaking needs to be affected when dropping stream items.

<script type="WaveDrom">
{signal: [
  {name: 'i_drop',     wave: '0.....1....0....'},
  {name: 'o_dropped',  wave: '0.......1.0.....'},
  [ 'Input',
    {name: 'i_valid',  wave: '0..1010.1.0..1.0'},
    {name: 'o_ready',  wave: '01..011....0..1.'},
  ],
  [ 'Output',
    {name: 'o_valid',  wave: '0..1010......1.0'},
    {name: 'i_ready',  wave: '01..01..0.....1.'},
  ]
],
 foot:{
   tock:0
 }
}
</script>
