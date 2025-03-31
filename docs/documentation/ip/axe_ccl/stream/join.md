---
title: Stream Join
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/cc_stream_join.sv:cc_stream_join


## Operation Principle

```mermaid
    graph LR
        A0>stream_inp_0] --> B{cc_stream_join}
        A1>stream_inp_1] --> B
        A2>stream_inp_2] --> B
        S[i_select] --> B
        B --> C>stream_oup]
```

The data runs outside the module. A common use case for this is to cycle synchronize data from multiple input streams into one.
The output `o_valid` is only asserted when all respective selected input `i_valid[i]` are asserted. The ready acknowledgement from downstream happens upstream at the same time.
If an input stream is not selected the handshake does not trigger, even if the respective stream is asserted.
