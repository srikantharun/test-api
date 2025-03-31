---
title: Common Cells Library (AXE_CCL)
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

This library contains a variety of basic simple blocks intended for heavy reuse in other IP.
To use in your IP add the `dependency: cc_lib` to the `Bender.yml` manifest.

```yaml
dependencies:
  cc_lib_pkg: { path: "hw/ip/common_cell_library/default/rtl/pkg" } # For using the packages
  cc_lib:     { path: "hw/ip/common_cell_library/default/rtl"     } # For using the modules
```

!!! warning "Module and Package prefixes"

    It was decided to prevent with eventual name clashes of 3rd party IP to change the prefixing from
    `cc_*` to `axe_ccl_*`! Not all modules have been converted yet and will be so gradually.

    New modules *MUST* use the new `axe_ccl_*` prefix!



## AXE_CCL_*_PKG: Packages with common useful functionality

A collection of packages. Each sub-category might have their own package which encapsulates common functions
and type definition for said category.

| Name                             | Module                          | Description                                             |
|:-------------------------------- |:------------------------------- |:------------------------------------------------------- |
| `Constant Math Functions`        | [cc_math_pkg](pkg/math.md)      | Constant math expression                                |
|                                  |                                 |                                                         |


## AXE_CCL: General modules that do not match any other categories


| Name                             | Module                                                              | Desciption                               |
|:-------------------------------- |:------------------------------------------------------------------- |:---------------------------------------- |
| `Mux Onehot`                     | [axe_ccl_mux_onehot](misc/mux_onehot.md)                            | Multiplexer using a onehot select signal |
| `Memory 1RP 1WP Deconflict`      | [axe_ccl_mem_1rp_1wp_deconflict.sv](misc/mem_1rp_1wp_deconflict.md) | Memory 1RP 1WP deconflict                |
|                                  |                                                                     |                                          |


## CC_CLK/RST: Modules for manipulation clock and reset paths

A collection of clock dividers, multiplexers ans synchronizers

| Name                             | Module                                                  | Description                                                           |
|:-------------------------------- |:------------------------------------------------------- |:--------------------------------------------------------------------- |
| `Clock Divider by 2`             | [axe_ccl_clk_div_by_2](clk/div_by_2.md)                 | T-Flip Flop based clock divider by 2.                                 |
| `Integer Divider`                | [axe_ccl_clk_div_by_int](clk/div_by_int.md)             | Integer divider, based on flop-latch-mux clock modulator.             |
| `Punch Through Divider`          | [axe_ccl_clk_div_by_pt](clk/div_by_punch_through.md)    | Phase accumulator for generating pulses every X cycles.               |
| `Glitch-free Multiplexer`        | [axe_ccl_clk_mux](clk/glich_free_multiplexer.md)        | Glitch-free clock multiplexer.                                        |
| `Tree of OR2 Tech Cells`         | [axe_ccl_clk_or_tree](clk/or_tree.md)                   | Generated tree of Tech_cell clock ors                                 |
| `Reset Synchronizer`             | [axe_ccl_rst_n_sync](clk/reset_synchronizer.md)         | Active-low reset synchronizer, with test bypass                       |
| `Low Power Control`  `           | [axe_ccl_clk_lp_control](clk/lp_control.md)             | Low Power controller gating the clock using AMBA LowPower Interface   |
|                                  |                                                         |                                                                       |


## CC_CDC: Modules for crossing clock boundaries

A collection of clock domain crossings

| Name                             | Module                                            | Description                                                        |
|:-------------------------------- |:------------------------------------------------- |:------------------------------------------------------------------ |
| `Pulse Synchronizer`             | [axe_ccl_cdc_pulse](cdc/pulse.md)                 | Pulse clock crossing with feedback path.                           |
| `4-phase Handshake`              | [axe_ccl_cdc_4_phase](cdc/4_phase.md)             | Transfer data with a 4-phase handshake. Very low throughput.       |
| `Bus Synchonizer`                | [axe_ccl_cdc_bus](cdc/bus.md)                     | Bus capture, handshake resync. Not high throughput.                |
| `Graycoded Fifo`                 | [axe_ccl_cdc_fifo](cdc/fifo.md)                   | Graycoded Asynchronous FIFO.                                       |
| `Synchronizer Array`             | [cc_cdc_sync_array](cdc/sync_array.md)            | Simple array of synchronizer cells. Use for slow sideband signals. |
| `Reset (Flush) Controller`       | [axe_ccl_cdc_reset_control](cdc/reset_control.md) | Controls reset and flush between SRC and DST side.                 |
|                                  |                                                   |                                                                    |


## CC_CNT: Counters and Shift Registers

A collection of different counters and shift registers.

| Name                             | Module                                                  | Description                                             |
|:-------------------------------- |:------------------------------------------------------- |:------------------------------------------------------- |
| `Delta Counter`                  | [cc_cnt_delta](cnt/delta.md)                            | Counter with optional sticky overflow.                  |
| `Phase Accumulator`              | [axe_ccl_cnt_phase_acc](cnt/phase_accumulator.md)       | Phase accumulator for generating pulses every X cycles. |
| `Shift Register`                 | [cc_cnt_shift_reg](cnt/shift_register.md)               | Shift register with enable, clear and stall             |
| `Threshold Counter`              | [axe_ccl_cnt_to_threshold](cnt/to_threshold.md)         | Counter that pulses when a given threshold is reached.  |
|                                  |                                                         |                                                         |
<!--
| `Linear Feedback Shift Register` | [cc_cnt_lfsr](cnt/lfsr.md)                              | LFSR with dynamic-taps, output flipping and masking.    |
| `Onehot Counter`                 | [cc_cnt_onehot](cnt/onehot.md)                          | Up/Down counter with a onehot bit                       |
-->


## CC_DFT: DFT helper modules

| Name                             | Module                                                  | Description                                             |
|:---------------------------------|:------------------------------------------------------- |:------------------------------------------------------- |
| `DFT Pad Multiplexer`            | [axe_ccl_dft_pad_mux](dft/pad_mux.md)                   | IO Pad multiplexer between functional and DFT mode.     |
| `DFT Block Wrapper`              | [axe_ccl_dft_block_wrapper](dft/block_wrapper.md)       | DFT insertion generic wrapper.                          |
|                                  |                                                         |                                                         |


## CC_(DE)CODE: Representation Converters

A collection of different converters from one representation to another.

| Name                             | Module                                                  | Description                                             |
|:---------------------------------|:------------------------------------------------------- |:------------------------------------------------------- |
| `Graycode`                       | [axe_ccl_decode_gray](code/gray.md)                     | Convert between Binary and Graycode representations.    |
| `Population Counter`             | [cc_decode_population](code/population_counter.md)      | Count the number of 1's in a vector (Hamming-Weight)    |
| `Onehot to Binary`               | [cc_decode_onehot](code/decode_onehot.md)               | Decodes a onehot0 signal to binary index, with flags    |
|                                  |                                                         |                                                         |
<!--
| `Address Decoder`                | [cc_decode_addr](code/address.md)                    | Decodes an Address map to a binary index                |
-->


## CC_MON: Monitors

A collection of different event monitors to track special events on signals.

| Name                             | Module                                                            | Description                                            |
|:---------------------------------|:----------------------------------------------------------------- |:------------------------------------------------------ |
| `Hysteresis Comparator`          | [axe_ccl_mon_hysteresis_comparator](mon/hysteresis_comparator.md) | Comparator block with hysteresis inside a value range. |
| `Minimum-Maximum Monitor`        | [axe_ccl_mon_minimum_maximum](mon/minimum_maximum.md)             | Monitor minimum and maximum values of a given signal.  |
| `Edges Monitor`                  | [axe_ccl_mon_edge_detector](mon/edge_detector.md)                 | Detects rising and falling edges of single bit signal. |
|                                  |                                                                   |                                                        |


## CC_STREAM: Stream Handshaking Modules

A collection of basic blocks which coordinate AXI-like valid/ready handshaking

| Name                             | Module                                                                    | Description                                                 |
| :------------------------------- | :------------------------------------------------------------------------ | :---------------------------------------------------------- |
| `Stream Demultiplexer`           | [cc_stream_demux](stream/demux.md)                                        | Select one of several output streams.                       |
| `Stream Disconnect`              | [cc_stream_disconnect](stream/disconnect.md)                              | Disconnect a stream, with optional input dropping.          |
| `Stream Fifo`                    | [cc_stream_fifo](stream/fifo.md)                                          | First-In-First-Out data structure using Flops for storage.  |
| `Stream Fifo with Memory Macro`  | [cc_stream_fifo_mem](stream/fifo_mem.md)                                  | First-In-First-Out data structure using Memory for storage. |
| `Stream Filter`                  | [cc_stream_filter](stream/filter.md)                                      | Filter / drop data stream packages.                         |
| `Stream Fork`                    | [cc_stream_fork](stream/fork.md)                                          | Fork one stream to multiple streams.                        |
| `Stream Join`                    | [cc_stream_join](stream/join.md)                                          | Join multiple streams together to one.                      |
| `Stream Multiplexer`             | [cc_stream_mux](stream/mux.md)                                            | Select one of several input streams.                        |
| `Stream Pipeline Load`           | [cc_stream_pipe_load](stream/pipeline_load.md)                            | Coordinate load signals for pipeline registers.             |
| `Stream Register Elastic`        | [cc_stream_reg_el](stream/register_elastic.md)                            | Handshaked register to absorb stream bubbles.               |
| `Stream Register Fall Through`   | [cc_stream_reg_ft](stream/register_fall_through.md)                       | Handshaked register to get default ready behavior.          |
| `Stream to Memory`               | [axe_ccl_stream_to_mem](stream/to_memory.md)                              | Full handshking for non-backpressurable memories.           |
|                                  |                                                                           |                                                             |

<!--
| `Stream Buffer`                  | [cc_stream_buffer](stream/buffer.md)                                      | Buffer one or multiple stream items (FIFO).                 |
| `Stream Crossbar`                | [cc_stream_crossbar](stream/crossbar.md)                                  | Crossbar network with multiple inputs and outputs.          |
-->
<!--
| `Stream Omega Network`           | [cc_stream_omega_network](stream/omega_network.md)                        | Omega (butterfly) network with multiple inputs and outputs. |
-->
<!--
| `Stream Round Robin Arbiter`     | [cc_stream_round_robin_arbiter](stream/round_robin_arbiter.md)            | Arbitrate from multiple streams in round robin fashion.     |
| `Stream Round Robin Distributor` | [cc_stream_round_robin_distributor](stream/round_robin_distributor.md)    | Distribute to different streams in round robin fashion.     |
| `Stream Throttle`                | [cc_stream_throttle](stream/throttle.md)                                  | Throttle the amount of outstanding requests.                |
-->
