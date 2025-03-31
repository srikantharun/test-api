---
title: Performance Information
doc:
  status: review
  version: [2, 0, 0]
  confidentiality: internal
---

# Performance Information

This section gives an overview of the limiting factors in terms of performance and latency when executing programs on
the DWPU.


## Performance Limits

Application performance on the DWPU can be either compute-bound or I/O-bound.


### Computational Performance (TODO:@stefe were do I find this info?)

For the `SOP` and `SUM` operations, the data path in the DWPU channel performs a sum-of-products operation on 9 operand
pairs, hence performing $9 MAC ⁄ cycle$.

Using 1 $MAC=2$ operations, the channel performance is $P_{channel}=18 op ⁄ cycle$, and the overall DWPU performance
therefore becomes $P_{DWPU} = 64 * P_{channel} = 1.152  k_{op} ⁄ cycle$.
At the expected clock frequency of 1 GHz, DWPU performance is $1.152  Top ⁄ s$.


### Throughput

Peak throughput of the unit is limited by the AXI stream interfaces at $1  PWORD ⁄ cycle$, i.e., 1 data item per cycle
both at input and output streams from the channel point of view.  Therefore, considering the size of the input and
output streams of a program in beats, the program will always need at least (TODO:@manuel enable Mathjax)
<!--- $\max size_input, size_output$ --->
cycles to complete.


### Summary of Performance Limits

-	A well-balanced program will consume and/or produce 1 data item per cycle while performing 9 MAC operations per cycle.
-	A program is *compute-bound* if it needs to compute more than 9 MAC operations per input and/or output data item.
-	A program is *I/O-bound* if it requires more than one input and/or output data item per 9 MAC operations.


## Latency

There are two distinct paths of information flow through DWPU.  On one hand, the computational data path from steam
input to stream output, and on the other hand the instruction path originating in the data path command generator and
ending in the DWPU data path.

Both paths have inherent latency attached to them but are fully handshaked (AXI-style valid/ready) and
back-pressureable, thus exhibiting pipelined behavior.


### Data Latency

The DWPU computational data path has a parameterizable latency of 3 clock cycles (min 2).  Furthermore, the latency of
input FIFO and output buffer must be considered to reach the input-output data latency of the subsystem, as shown below.

The input FIFO – if present – has latency 1 when empty, and a latency corresponding to the number of data items stored
otherwise, up to `INPUT_FIFO_DEPTH`.  If back-pressure is applied from the output stream, the resulting stall will only
gradually propagate backpressure to the input stream if intermediate pipeline stages (e.g., the output buffer) are
empty.

| Signal Path                   | Latency Description   | Current Value |
|:----------------------------- |:--------------------- |:------------- |
| `i_axis_in_tdata`             | -                     | -             |
| `u_dwpu_dp/u_input_fifo`      | `INPUT_FIFO_DEPTH`    | 0             |
| `u_dwpu_dp/u_dwpu_channel[*]` | `NUM_PIPELINE_STAGES` | 2             |
| `u_dwpu_dp`                   | Output Register       | 1             |
| `o_axis_out_tdata`            | Total Latency         | 4             |


### Control Latency

Control latency is harder to observe from the outside of the DWPU subsystem, as data path commands are internally
generated using the [data path command generator block](./21_dwpu_cmd_gen.md). Nevertheless, below Table lists the
latency incurred on the control path between the instruction address FSM and the data path.

There is one stream register between the data path command generator and the data path to cut long combinatorial paths
from the instruction memory directly into data path multiplexors. In case of a data path stall (due to input or output
stream stalls), the command stream is stalled through back-pressure towards the command generator, in turn stalling the
instruction address FSM.
