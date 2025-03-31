# EUROPA_LPDDR_ASYNC_PERF_COUNTER

## Overview

The `europa_lpddr_async_perf_counter` module is a performance counter designed to operate with two asynchronous clock domains: `count_clk` and `ctrl_clk`. The counter increments based on the `i_count_inc` signal and operates synchronously with the `count_clk`. The control signals (`i_ctrl_cnt_en`, `i_ctrl_cnt_flush`, and `o_ctrl_cnt_value`) operate synchronously with the `ctrl_clk`. The module ensures that the latest possible counter value is available in the control domain, even if intermediate values are skipped due to the asynchronous nature of the clocks.

## Parameters

- `CounterWidth` (default: 32): Width of the counter.
- `SyncStages` (default: 3): Number of synchronization stages for clock domain crossing.

## Ports

### Input Ports

- `i_count_clk`: Clock signal for the counting domain.
- `i_count_rst_n`: Asynchronous reset signal for the counting domain (active low).
- `i_count_inc`: Increment signal for the counter.
- `i_ctrl_clk`: Clock signal for the control domain.
- `i_ctrl_rst_n`: Asynchronous reset signal for the control domain (active low).
- `i_ctrl_cnt_en`: Enable signal for the counter in the control domain.
- `i_ctrl_cnt_flush`: Flush signal to reset the counter to 0 in the control domain.

### Output Ports

- `o_ctrl_cnt_value`: Latest synchronized counter value in the control domain.

## Functionality

- The counter increments when `i_count_inc` is high and `i_ctrl_cnt_en` is enabled.
- The counter operates synchronously with `i_count_clk`.
- The counter can be flushed (reset to 0) using the `i_ctrl_cnt_flush` signal.
- The control signals (`i_ctrl_cnt_en`, `i_ctrl_cnt_flush`) are synchronized to the counting domain using synchronization stages.
- The latest counter value is synchronized back to the control domain and made available on `o_ctrl_cnt_value`.

### Clock Domain Crossing

- The module uses synchronization stages to safely transfer signals between the asynchronous clock domains.
- The `i_ctrl_cnt_en` signal is synchronized to the counting domain.
- The `i_ctrl_cnt_flush` signal is synchronized to the counting domain using a pulse synchronization mechanism.
- The counter value is synchronized back to the control domain to ensure the latest possible value is available.

### Assumptions

- The `count_clk` is assumed to be faster than the `ctrl_clk`.
- Due to the asynchronous nature of the clocks, the `o_ctrl_cnt_value` may lag behind the actual internal counter value in the count clock doamin and may skip intermediate values. The goal is to provide the latest possible value in the control domain.
