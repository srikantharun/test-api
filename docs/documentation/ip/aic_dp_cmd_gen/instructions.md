---
title: Instruction Looping and Encoding
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

We have several instruction-based AI Core blocks with different looping support.  This enables looping support for
Transformer operations.

## Instruction-Based Loop Support

!!! quote "History of Instruction-based AI Core blocks (MVMExe, DWPU, IAU, DPU)"

    They used to implement all features with slightly differing program structures and implementations while essentially
    following the same operating principle. As such, the way to form commands for each block differed in the past.

The hardware tasked with processing these commands is the command block (cmdblock) which produces the command, and the
datapath command generator [aic_dp_cmd_gen](./microarchitecture/index.md) which interprets the program structure
described by the command and sequences instructions from the instruction memory towards the datapath.

## Specification

The following `AI-Core` blocks use this unified Looping structure:

- `MVMExe`
- `DWPU`
- `IAU`
- `DPU`

### Unified Loop Structure

A loop is defined by three parameters, its starting address in the block's DP command generator program memory (`start`),
the number of DP commands in the loop (`length`), and the number of iterations for which the loop runs (`iter`).
In case either the length or iter fields are `0`, the loop is considered *empty* and skipped.

Up to three independent main loops (labeled `main`) and a per-command total of up to two nested loop levels (labeled
`nested_0` and `nested_1`) can be configured in a unified command format.  The rules for valid loop constellations are
as follows:

- Each nested loop level is linked to exactly one main loop and must be fully contained within that main loop.
  It is considered *"active"* within that main loop. Multiple nested loops can be active in the same main loop.
- If two nested loops are active within the same main loop, they can be:
    - either completely nested within each other according to level (`nested_1` nested inside `nested_0`),
    - **or** completely parallel to each other according to level (`nested_1` after `nested_0`).
- Partially overlapping loops are **not** permitted.

The steps for processing the loops of a unified loop command are as follows:

1. If multiple main loops are present, they are processed sequentially according to their ordering within the command.
2. The processing of the main loop starts at its `start` address and is repeated for `iter` times in total.
3. When processing arrives at the `start` address of a nested loop, that nested loop is repeated for its `iter` times
   before resuming execution of the containing loop.
4. When the `start` address of two nested loops coincides, the lower-level `nested_1` loop is executed first.

These rules are illustrated in the following diagram:

![LOOP LEVEL COMMANDS](./figures/loop_level_commands_1.drawio.png)


### Unified Command Encoding

The full unified loop command holds descriptors for three main and two nested loops.  The command header is followed by
the command words of all main loops, followed by the command words for all nested loops.  The effective layout of the
program (i.e. which nested loops belong to which main loop) is determined from the `map_main` field in the command words
of the nested loops themselves, which holds the index (`0`, `1`, or `2`) of the respective main loop.

For reducing the size of commands, the reduced unified loop command uses the `cmd_format` field in the command header to
encode the variable number of `main` & `nested` loops possible.  These commands only contain the necessary command words
for the loops actually present in the program, and are subsequently expanded into the full unified loop command
(with 3 main & 2 nested loops) by the command block with unused loops being encoded as *empty* loops.

As such, the command header encodes the length and layout of the program information in the command block storage itself
and can be implemented using the already present static command format feature.

The unified encoding follows the command header unification from [AIC-CTRL-I1](https://git.axelera.ai/prod/europa/-/issues/189).

??? example "Mapping from block-specific Commands"

    ![LOOP LEVEL COMMAND MAPPING](./figures/loop_level_commands_0.drawio.png)


#### LOOP_M1_N0: Single Loop

Command Format: `0x0`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  192,
    lanes:   3,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### LOOP_M1_N1: Nested Loop

Command Format: `0x1`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "nested_0",
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  256,
    lanes:   4,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### LOOP_M1_N2: 1+2 Loops

Command Format: `0x2`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "nested_1",
      "nested_0",
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  320,
    lanes:   5,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### LOOP_M2_N0: Two Loops

Command Format: `0x3`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "main_1",
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  256,
    lanes:   4,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### LOOP_M2_N1: 2+1 Loops

Command Format: `0x4`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "nested_0",
      "main_1",
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  320,
    lanes:   5,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### LOOP_M2_N2: 2+2 Loops

Command Format: `0x5`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "nested_1",
      "nested_0",
      "main_1",
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  384,
    lanes:   6,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### LOOP_M3_N0: Three Loops

Command Format: `0x6`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "main_2",
      "main_1",
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  320,
    lanes:   5,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### LOOP_M3_N1: 3+1 Loops

Command Format: `0x7`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "nested_0",
      "main_2",
      "main_1",
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  384,
    lanes:   6,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### LOOP_M3_N2: 3+2 Loops (FULL COMMAND)

Command Format: `0x8`

<script type="WaveDrom">
{reg: [
    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'map_main',   bits:  8, type: 2,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{                    bits:  8, type: 1,},

    {name: 'start',      bits: 16, type: 2,},
    {name: 'length',     bits: 16, type: 2,},
    {name: 'iter',       bits: 24, type: 2,},
  	{name: 'extra',      bits:  8, type: 3,},

    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "nested_1",
      "nested_0",
      "main_2",
      "main_1",
      "main_0",
      "header",
  	  "CMD",
    ],},
  	bits:  448,
    lanes:   7,
    compact: true,
    hspace: 1200,
  }
}
</script>


#### BYPASS: Bypass

Set the respective datapath into stream bypass mode.

Command Format: `0x9`

<script type="WaveDrom">
{reg: [
    {name: 'triggers',   bits:  8, type: 2,},
    {                    bits:  8, type: 1,},
    {name: 'token_prod', bits: 16, type: 2,},
    {name: 'token_cons', bits: 16, type: 2,},
    {name: 'cmd_format', bits:  8, type: 5,},
    {name: 'config',     bits:  8, type: 2,},

    {name: '0',          bits:  8, type: 4,},
    {name: '1',          bits:  8, type: 4,},
    {name: '2',          bits:  8, type: 4,},
    {name: '3',          bits:  8, type: 4,},
    {name: '4',          bits:  8, type: 4,},
    {name: '5',          bits:  8, type: 4,},
    {name: '6',          bits:  8, type: 4,},
    {name: '7',          bits:  8, type: 4,},
  ],
  config: {
    label: {left: [
      "header",
  	  "CMD",
    ],},
  	bits:  128,
    lanes:   2,
    compact: true,
    hspace: 1200,
  }
}
</script>
