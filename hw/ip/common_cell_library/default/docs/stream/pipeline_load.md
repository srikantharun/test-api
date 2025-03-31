---
title: "Stream Pipeline Load"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/cc_stream_pipe_load.sv:cc_stream_pipe_load


## Operation Principle

```mermaid
    graph LR
        A -->|data| P0[data_reg_0]
        P0 --> P1[data_reg_1]
        P1 --> P2[data_reg_2]
        P2 -->|data| C
        A>stream_inp] -->|valid/ready| B{cc_stream_pipe_load}
        B -->|o_load_0| P0
        B -->|o_load_1| P1
        B -->|o_load_2| P2
        B -->|valid/ready| C>stream_oup]
```

The data registers are outside of the module.
The longest combinatorial path is through the ready back-pressure.
