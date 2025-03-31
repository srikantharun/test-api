---
title: Stream Fork
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/cc_stream_fork.sv:cc_stream_fork


## Operation Principle

```mermaid
graph LR
    A0>stream_inp] --> B{cc_stream_fork}
    S[i_select] --> B
    B --> C0>stream_oup_0]
    B --> C1>stream_oup_1]
    B --> C2>stream_oup_2]
```

The data runs outside the module. A common use case for this is to distribute one stream item to multiple other streams.
The input `o_ready` is only asserted when all respective selected output handshakes `o_valid[i] && i_ready[i]` have
been asserted once.
If an output stream is not selected the respective output handshake does not trigger, even if the respective input
stream is asserted.
