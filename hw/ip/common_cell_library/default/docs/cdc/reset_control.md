---
title: "Reset Controller"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

This module is mainly used internally to synchronize the clear requests between both sides of a CDC module.
It aims to solve the problem of initiating a CDC clear, reset one-sidedly without running into reset-domain-crossing
issues and breaking CDC protocol assumption.

!!! quote "Source Origin"

    This reset controller is a ported version of the one found in the [pulp-platform common_cells](https://github.com/pulp-platform/common_cells/tree/master).

    - [cdc_reset_ctrlr](https://github.com/pulp-platform/common_cells/blob/master/src/cdc_reset_ctrlr.sv)

    Original Author: Manuel Eggimann <meggimann@iis.ee.ethz.ch>!


## Problem Formulation

CDC implementations usually face the issue that one side of the CDC must not be cleared without clearing the other side.
E.g. clearing the write-pointer without clearing the read-pointer in a gray-counting CDC FIFO results in an invalid
fill-state an may cause spurious transactions of invalid data to be propagated accross the CDC.  A similar effect is
caused in 2-phase CDC implementations.

A naive mitigation technique would be to reset both domains asynchronously with the same reset signal. This will cause
intra-clock domain RDC issues since the asynchronous clear event (assertion of the reset signal) might happen close to
the active edge of the CDC's periphery and thus might induce metastability.  A better, but still flawed approach would
be to naively synchronize assertion AND deassertion (the usual rst sync only synchronize deassertion) of the resets into
the respective other domain. However, this might cause the classic issue of fast-to-slow clock domain crossing where the
clear signal is not asserted long enough to be captured by the receiving side. The common mitigation strategy is to use
a feedback acknowledge signal to handshake the reset request into the other domain.  One even more peculiar corner case
this approach might suffer is the scenario where the synchronized clear signal arrives at the other side of the CDC
within or even worse after the same clock cylce that the other domain crossing signals (e.g. read/write pointers) are
cleared. In this scenario, multiple signals change within the same clock cycle and due to metastability we cannot be
sure, that the other side of the CDC sees the reset assertion before the first bits of e.g. the write/read pointer start
to switch to their reset state. Care must also be taken to handle the corner cases where both sides are reset
simultaneously or the case where one side leaves reset earlier than the other.


## How this Works

This module intended to be used in pairs, the `src` side and the `dst` side.  Each side can be triggered using the
`i_flush` signal or (optionally) by the asynchronous `i_rst_n`.  Once e.g. `src` is triggered it will initiate a clear
sequence that first asserts an `o_isolate_req` signal, waits until the external circuitry acknowledges isolation using
the `i_isolate_ack`. Then the module asserts the `o_flush_req` signals before some cycles later, the isolate signal is
deasserted.  This sequence ensures that no transactions can arrive to the CDC while the state is cleared.  Now the
important part is, that those four phases (asser isolate, assert flush, deassert flush, deassert isolate) are mirrored
on the other side (`dst`) in lock-step.  The `axe_ccl_cdc_reset_control` module uses a dedicated 4-phase handshaking CDC
to transmit the current phase of the clear sequence to the other domain.  We use a 4-phase rather than a 2-phase CDC to
avoid the issues of one-sided async reset that might trigger spurious transactions. Furthermore, the 4-phase CDC within
this module is operated in a special mode: `WaitHandshake(1'b1)` ensures that there are no in-flight transactions.
The src side only consumes the item once the destination side acknowledged the receiption.  This property is required to
transition through the phases in lock-step.  Furthermore, `SendResetMsg(1'b1)` will cause the src side of the 4-phase
CDC to immediately initiate the isolation phase in the dst domain upon asynchronous reset regardless how long the async
reset stays asserted or whether the source clock is gated.  Both sides of this module independently generate the
sequence signals as an initiator (triggered by the `i_flush` or `i_rst_n` signal) or target (trigerred for the other
side). The or-ed version of initiator and target are used to generate the actual `o_isolate_req` and
`o_flush_req` signal. That way, it doesn't matter wheter both sides simulatenously trigger a clear sequence, proper
sequencing is still guaranteed.

The time it takes to complete an entire clear sequence can be bounded as follows:

$$
t_{clear} <= 20*T+16*\text{SYNC_STAGES}*T | T=\max{T_{src}, T_{dst}}
$$

## Integrate the Module

Instantiate the module two times within your CDC and connect `i_clk`, the  asyncrhonous `i_rst_n` and the synchronous
`i_flush` signals to the respective `src` and `dst` domain.

If one enables support for async reset `FlushOnAsyncReset(1'b1)`, the number of synchronization stages (for metastability resolution) **must be strictly less** than the latency of the CDC. E.g. if the CDC uses 3 (the minimum) sync stages, parametrize this module with `SyncStages < 2`! The CDC must implement a `i_[src|dst]_flush` port that **SYNCHRONOUSLY** clears all FFs on the respective side. Connect the CDC's src/dst_flush ports to this module's `o_flush_req port.

Once the `o_isolate_req` signal is asserted, the respective CDC side (`src/dst`) must be isolated from the outside world
(i.e. must no longer accept any transaction on the src side and cease presenting or even withdrawing data on the `dst`
side).  Once the CDC side is isolated (depending on protocol this might take several cycles), assert the
`i_isolate_ack` signal.


::: hw/ip/common_cell_library/default/rtl/axe_ccl_cdc_reset_control.sv:axe_ccl_cdc_reset_control
