---
title: Data-Path
doc:
  status: review
  version: [2, 0, 0]
  confidentiality: internal
rtl:
  sv:
    dwpu_dp:
      bender:
        subip/ai_core/subip/dwpu/rtl/Bender.yml
---

# DWPU Data Path (dwpu_dp)

**TODO(@wolfgang.roennigner): Use the new docstring extraction when it comes online**
%% (page.meta._rtl.sv.dwpu_dp.modules | selectattr('name', '==', 'dwpu_dp') | first).doc %%

## Features

This module implements the functionality of the DWPU. It's features are:

- Multiple calculation channels for SIMD operation.
- Scratchpad and weight buffer registers.
- Logic for calculation of SOP, SUM, MAX and MIN
- Fully pipelined and handshaked in command and data streams.
- Bypass mode to avoid calculation.

The overall data-path architecture is depicted below, for simplicity the handshaking is omitted. Details are found in the next section.

![DWPU DP](./figures/22-DWPU-dp.drawio.png "The overall DWPU pipeline architecture.")

The unit joins the command stream together with the input data-stream, processes it and generates an output stream.
Depending on the command data-stream items are either consumed or generated depending on the command flags. In general
there can be per command stream only one input and/or output stream, as depicted by the tlast stream flags.

## Control & Stream Handling

Handshaking is handled by common `cc_stream_*` modules. Below diagram shows how the handshaking is connected to have
a fully handshake controlled back-pressurizable pipeline:

```mermaid
graph TD
    INP>Input]
    FIFO(FIFO)
    CMD>Command]
    JOIN{Stream Join}
    DEMUX{CC Stream Demux}
    FILTER[CC Stream Filter]
    PIPE[CC Stream Pipeline Load]
    CHANNEL(DWPU Channel)
    MUX{Stream Mux}
    BUF(Output Buffer)
    OUP>Output]

    INP ==>|Data| FIFO
    FIFO ==>|Input Data| CHANNEL
    CHANNEL ==>|Output Data| MUX
    FIFO ==>|Bypass Data| MUX
    MUX ==>|Data| BUF
    BUF ==>|Data| OUP

    INP <-.->|Input Handshake| FIFO
    CMD <-.->|Command Stream| JOIN
    FIFO <-.-> JOIN
    JOIN <-.->|Joined Data and Cmd Handshake| DEMUX
    DEMUX <-.->|Operation Handshake| FILTER
    FILTER <-.->|Output Enable Handshake| PIPE
    PIPE -->|Pipeline Register Load| CHANNEL
    PIPE <-.->|Channel Output Handshake| MUX
    DEMUX <-.->|Bypass Handshake| MUX
    MUX <-.->|Mux Handshake| BUF
    BUF <-.->|Output Handshake| OUP
```

Depending on the command it will join an item from the data input stream.
The stream filter will prevent activating the channel pipleine when no output is required.
All scratchpad and weigthbuffer can be loaded regardless.

## Module Parameters

**TODO(@wolfgang.roenniner): Update properly when docstring extraction comes online**

%% europa/hw/ip/dwpu/default/rtl/dwpu_dp.sv:parameter_table %%


## IO Description

**TODO(@wolfgang.roenniner): Update properly when docstring extraction comes online**

%% europa/hw/ip/dwpu/default/rtl/dwpu_dp.sv:port_table %%
