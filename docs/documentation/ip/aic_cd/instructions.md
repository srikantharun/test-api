---
title: "Command & Instruction Encodings"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

Here we provide the encoding specifics for the *AI-Core Control Dispatcher*.

Both commands and instructions are *64-bit words* with their fields byte-aligned for ease of use.
There are currently seven instructions encoded with an opcode:

- `cmd`: sends a command to an AI Core Block
- `prg`: sends a program to an AI Core Block
- `cons_local`: awaits tokens from AI Core Blocks
- `prod_local`: generates tokens to AI Core Blocks
- `cons_global`: awaits external top-level tokens
- `prod_global`: generates external top-level tokens
- `timestamp`: triggers a timestamp in the timestamp unit with a 2-bit wide timestamp ID


## Command Description

<script type="WaveDrom">
{reg:
  [
    {name: 'task_list_ptr',  bits: 16},
    {name: 'length',         bits: 16},
    {name: 'control_offset', bits: 24},
    {                        bits:  8},
  ],
  config: {
    label: {left: [
      "command",
    ],},
  	bits:  64,
    lanes:  1,
    compact: false,
    hspace: 1200,
  }
}
</script>

The command causes the `aic_cd` to start fetching from a position in memory described by the `task_list_ptr` a task
list of a certain `length` (in words). The `control_offset` is added to all addresses of a command and instruction
address pointers.

| Field            | Description                                                                                                        |
|:---------------- |:------------------------------------------------------------------------------------------------------------------ |
| `task_list_ptr`  | Word pointer to the first instruction of the offloaded AI Core task list located in the control data memory region |
| `length`         | Length of the offloaded AI Core task list in words                                                                 |
| `control_offset` | Byte offset for the command and program pointers of the control instructions of the off-loaded AI Core task list   |


## Instruction Descriptions

<script type="WaveDrom">
{reg: [
    {name: '11',             bits:  2, type: 6,},
    {                        bits:  6, type: 1,},
    {name: 'id',             bits:  2,         },
    {                        bits: 54, type: 1,},

    {name: '01',             bits:  2, type: 6,},
    {name: '000011',         bits:  6, type: 5,},
    {name: 'tok_prod',       bits: 24,         },
    {                        bits: 32, type: 1,},

    {name: '01',             bits:  2, type: 6,},
    {name: '000010',         bits:  6, type: 5,},
    {name: 'tok_cons',       bits: 24,         },
    {                        bits: 32, type: 1,},

    {name: '01',             bits:  2, type: 6,},
    {name: '000001',         bits:  6, type: 5,},
    {name: 'tok_prod',       bits: 24,         },
    {                        bits: 32, type: 1,},

    {name: '01',             bits:  2, type: 6,},
    {name: '000000',         bits:  6, type: 5,},
    {name: 'tok_cons',       bits: 24,         },
    {                        bits: 32, type: 1,},

    {name: '10',             bits:  2, type: 6,},
    {name: 'dst_id',         bits:  6,         },
    {name: 'program_ptr',    bits: 24,         },
    {name: 'dst_address',    bits: 16,         },
    {name: 'length',         bits: 16,         },

    {name: '00',             bits:  2, type: 6,},
    {name: 'dst_id',         bits:  6,         },
    {name: 'command_ptr',    bits: 24,         },
    {name: 'patch_id_0',     bits:  8,         },
    {name: 'patch_id_1',     bits:  8,         },
    {name: 'length',         bits:  8,         },
    {name: 'patch_mode',     bits:  8,         },
  ],
  config: {
    label: {left: [
      "timestamp",
      "prod_global",
      "cons_global",
      "prod_local",
      "cons_local",
      "prg",
      "cmd",
    ],},
  	bits:  448,
    lanes:   7,
    compact: true,
    hspace: 1200,
  }
}
</script>

Instructions are decoded via the `2-bit opcode`. Token instructions have an additional `6-bit token_opcode`.
The [instruction validation](microarchitecture/instruction_fetch/index.md) takes care that only sane instructions are
passed to the execute stage.

!!! note "Validation Errors"

    If the instruction validation fails, the offending instruction and all subsequent ones will be dropped!
    An IRQ will be raised with the error and the offending instruction index is reported in the CSRs.


### Copy Instruction: `cmd`

<!-- TODO(@wolfgang.roennigner): Update the links when there -->

Copies a command intended for an ai-core subunit from a source to a destination.  With the patch modes it is possible
to change the addresses found in memory. See the details in [address patching](microarchitecture/copy_unit/index.md).

| Field            | Description                                                                                                                               |
|:---------------- |:----------------------------------------------------------------------------------------------------------------------------------------- |
| `dst_id`         | ID of the destination AI Core Block (lookup for address map)                                                                              |
| `command_ptr`    | Byte pointer to the first word of the AI Core Block command located in the control data memory region (can be offset by `control_offset`) |
| `patch_id_0`     | ID of the base address of the memory pool address for the first address patching of the selected patch mode (configurable via CSR)        |
| `patch_id_1`     | ID of the base address of the memory pool address for the second address patching of the selected patch mode (configurable via CSR)       |
| `length`         | Byte length of the AI Core Block command                                                                                                  |
| `patch_mode`     | Patch mode selection indicating the address patching pattern to be applied to the command (configurable via CSR)                          |


### Copy Instruction: `prg`

Copies a program intended for an ai-core sububit from a source to a destination.

| Field         | Description                                                                                                                       |
|:------------- |:--------------------------------------------------------------------------------------------------------------------------------- |
| `dst_id`      | ID of the destination AI Core Block (lookup for address map)                                                                      |
| `program_ptr` | Byte pointer to the first word of the AI Core Block program in the control data memory region (can be offset by `control_offset`) |
| `dst_address` | Destination byte address in the AI Core Block program memory                                                                      |
| `length`      | Byte length of the AI Core Block program                                                                                          |


### Token Instruction: `cons_local`

Perform a series of local token consuming handshakes as defined by the `tok_cons` field.

| Field      | Description                                           |
|:---------- |:----------------------------------------------------- |
| `tok_cons` | Bit vector of the AI Core Block tokens to be consumed |

### Token Instruction: `prod_local`

Perform a series of local token producing handshakes as defined by the `tok_prod` field.

| Field      | Description                                           |
|:---------- |:----------------------------------------------------- |
| `tok_prod` | Bit vector of the AI Core Block tokens to be produced |


### Token Instruction: `cons_global`

Perform a series of global token consuming handshakes as defined by the `tok_cons` field.

| Field      | Description                                               |
|:---------- |:--------------------------------------------------------- |
| `tok_cons` |Bit vector of the external top-level tokens to be consumed |


### Token Instruction: `prod_global`

Perform a series of global token producing handshakes as defined by the `tok_prod` field.

| Field      | Description                                                |
|:---------- |:---------------------------------------------------------- |
| `tok_prod` | Bit vector of the external top-level tokens to be produced |


### Timestamp Instruction: `timestamp`

Send a pulse with the `id` towards the timestamp unit.

| Field | Description                   |
|:----- |:----------------------------- |
| `id`  | Timestamp Trigger Indentifier |
