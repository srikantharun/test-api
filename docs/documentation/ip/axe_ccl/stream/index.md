---
title: Common Stream Modules
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

Common generic streaming modules which use an AXI-like valid/ready handshaking.


## Handshake Behavior

A stream is defined as a combination of 3 signals:

* `data_t data`: Payload data transferred from `upstream/source/manager` to `downstream/sink/subordinate`.
  * This signal is desired to be stable when the corresponding `valid` handshake signal is asserted. However depending on the functionality this is not a hard requirement.
* `logic valid`: Handshake signal from `upstream/source/manager` to `downstream/sink/subordinate` to indicate validity to transfer the `data`.
  * This signal when set by a source module (`valid_o`) **must not** depend on the corresponding `ready_i`. This is to prevent deadlocks in the handshaking. However it is allowed to combinatorically depend on another `valid_i` originating upstream.
  * Unlike AXI can be de-asserted when valid. This is a more general assumption and allows for example to implement a flushing capability.
* `logic ready`: Handshake signal from `downstream/sink/subordinate` to `upstream/source/manager` to indicate readiness to transfer the `data`.
  * This signal is allowed to combinatorically depend on the corresponding `valid` signal.

Here few examples how this handshaking plays out:

<script type="WaveDrom">
{signal: [
  {name: 'clk_i', wave: 'lp..lp...lp...l'},
  {},
  [ 'Stream',
   {name: 'data',   wave: 'xx2xxx2.xx.22xx', data: ['1', '2', '3', '4']},
   {name: 'valid' , wave: 'x010x01.0x01.0x'},
   {name: 'ready' , wave: 'x010x0.10x1...x'}
  ],
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


## Stream Network

These modules are intended to be instantiated together to form all sorts of different streaming networks. Datapath functionality is usually implemented on the outside and can be custom to the respective IP which uses them. An example network could look something like:

```mermaid
graph LR
    %% Nodes
    CMD>Stream CMD]
    INP>Stream INP]
    OUP0>Stream OUP 0]
    OUP1>Stream OUP 1]

    CONC(data concatination)

    JOIN{cc_stream_join}
    LOAD{cc_stream_pipeline_load}
    DEMUX{cc_stream_demultiplexer}

    P0[data_reg_0]
    P1[data_reg_1]

    %% Dataflow
    CMD -->|data| CONC
    INP -->|data| CONC
    CONC -->|data| P0
    P0 -->|data| P1
    P1 -->|data| OUP0
    P1 -->|data| OUP1

    %% Select is part of the command data
    P1 -->|data.select| DEMUX

    %% Handshaking
    CMD -->|valid/ready| JOIN
    INP -->|valid/ready| JOIN
    JOIN -->|valid/ready| LOAD
    LOAD -->|valid/ready| DEMUX
    DEMUX  -->|valid/ready| OUP0
    DEMUX  -->|valid/ready| OUP1

    LOAD -->|load_0| P0
    LOAD -->|load_1| P1
```

A control stream is joined with a data stream. Then the data is pipelined for arithmetic computation. A select signal from the data chooses which output streams the data flows onto.
