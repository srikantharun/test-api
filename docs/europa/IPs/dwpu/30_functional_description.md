---
title: Functional Description
doc:
  status: review
  version: [2, 0, 0]
  confidentiality: internal
---

# Functional Description

This section describes the main operating principles of DWPU and gives detailed information on how the data path
executes operations.


## Use-Cases

The DWPU is a SIMD vector processing unit meant to process intra-channel (depth-wise) operations which would be
inefficient to perform on the MVM unit. It supports sum-of-products as well as min/max operations. As such, it is suited
to perform convolutions as well as pooling operations.


## Dataflows

The DWPU processes dynamic data from an input stream and a set of static data stored in weight buffer registers to
produce an output stream. To allow for internal data reuse, a set of scratchpad registers is available.

The two common intended data flows are either using the DWPU as a pure stream sink to consume static data into the
weight buffer registers or using the DWPU to sink an input stream while producing an output stream during computations.
Use of the DWPU as a pure stream producer (i.e., computing purely off scratchpad and weight buffer) is possible, however
not very useful in practice. The last option, a purely internal operation that neither sinks nor produces a stream is
technically possible but unnecessary in practice.


## Modes of Operation

The DWPU supports two modes of operation, bypass mode (BYPASS) and regular execution mode (EXE).

During bypass mode, the entire input stream is consumed, input data are extended to output data width according to the
image sign-extension setting in the [CSRs](.build_reg/dwpu_csr_regs.md) and forwarded to the output stream.  Bypass mode
is entered upon receiving a BYPASS command format, which in turn emits one single instruction with the `bypass` bit set
to the data path.  The data path remains in bypass mode until the entire input stream has been processed and sent downstream.

!!! note

    Transactions committed into the data path output register are considered completed from the data path point of view.

Upon completion, the data path signals dp_done and returns into idle mode, ready to accept new instructions.

During the regular execution mode, stream beats are consumed and produced (if applicable) on a cycle-by-cycle basis.
Regular execution mode is entered upon receiving an EXE command descriptor, which in turn sets up the data path command
generator to emit data path commands according to a program found in the instruction memory. These instructions contain
flow control bits that decide the consumption and production of stream beats during that cycle. Furthermore,
instructions contain source addresses for computation input registers and next state selectors for scratchpad and weight
buffer registers. Upon execution of the last instruction, the data path signals `dp_done` and returns into idle mode,
ready to accept new instructions.

For detailed information on setting up execution on any AI core block, refer to the [programming flow](TODO(@review): were do I find this?)
documentation.


## Data Path Functionality

This section outlines functionality of the DWPU data path during regular execution. Operations on the DWPU are executed
on the channels in a parallel SIMD fashion. Hence, for most of this section, the behavior of a single channel’s
data path is outlined.

The terms *data path command*, *operation*, and *cycle* are used somewhat interchangeably and signify one step performed
by the data path according to the control signals in the data path command. Conceptually this happens in one clock
cycle, however the output is produced after an internal data path latency as described in the
[Application Note](./50_application_note.md).

The various portions of the data path outlined below – most of which are dedicated to data movement – are independently
controlled in parallel, and hence can be combined to achieve various concurrent data flows such as preloading new data
while producing outputs computed on previously stored data.

??? note "RTL implementation of register shifting behavior."

    The following registers are loaded via a shifting operation. To save on power the actual shift is implemented using
    a global shift offset pointer inside the data path. The actual data resides in the register and the pointer is
    advanced on a shift. The pointer is used to calculate the actual offset for the selection multiplexers and load
    enable bits. This performs effectively renaming of the respective registers in hardware. In practice this is
    transparent to the programmer, mentioned here for completeness.


### Weight Buffer Control

The 64 weight buffer registers are implementing a shifting functionality. `wb0` is functionally connected to the input
data and `wb1-wb63` can be loaded using the `wb_shift` bit. The input data is latched into weight buffer register
`wb0` and residing values shifted upwards `wb0 -> wb1, wb1 -> wb2, etc`. The value in `wb63` is discarded.


### Scratchpad Control

The 126 scratchpad registers `sp2-sp127` are implementing the same shifting behavior than the weight buffer registers.
The first two scratchpad register outputs, `sp0` and `sp1`, are hard-wired to the absorbing element of the operation
and the input data, respectively, and hence are not real architectural registers.
`sp2` is functionally connected to the input data and `sp3-wb127` can be loaded using the `sp_shift` bit. The input data
is latched into scratchpad register `sp2` and residing values shifted upwards `sp2 -> sp3, sp3 -> sp4, etc`. The value
in `sp127` is discarded.


### Image Operand Selection

The DWPU features a 9-operand data path. The nine dynamic (image) operands `i0-i8` are selected from the scratchpad
registers using the `i_sel` image selection control signals. Each dynamic operand `ix` has its own 7-bit scratchpad
address signal `i_sel[x]` to select from `sp0-sp127`. By using `sp0`, an operand can be effectively silenced (as shown
below), and by using `sp1`, the input data can be directly used for operations without storing it in a scratchpad
register first.

| Operation `opcode` | Contents of `sp0` for `image_sgn = 0` | Contents of `sp0` for `image_sgn = 0` |
|:------------------ |:------------------------------------- |:------------------------------------- |
| `SOP`              | sp(0) = 0                             | sp(0) = 0                             |
| `SUM`              | sp(0) = 0                             | sp(0) = 0                             |
| `MAX`              | sp(0) = 0                             | sp(0) = -128                          |
| `MIN`              | sp(0) = 255                           | sp(0) = 127                           |


### Weight Operand Selection

Some operations in DWPU use operand pairs of dynamic and static operands. The nine static (weight) operands `w0-w8` are
selected from the weight buffer registers using the `w_sel` weight selection control signals. Each static operand `wx`
has its own 6-bit weight buffer address signal `w_sel[x]` to select from `wb0-wb63`.


### Computational Operations

The computational operation is selected using the `opcode` co`ntrol signal and performs computation on the dynamic and
optionally static operands.

| Operation `opcode` | Encoding | Operation Result `out_data`                        | Description                   |
|:------------------ |:-------- |:-------------------------------------------------- |:----------------------------- |
| `SOP`              | `0b00`   | out_data = i_0 × w_0 + i_1 × w_1 + ... + i_8 × w_8 | Sum-of-Products (Convolution) |
| `SUM`              | `0b01`   | out_data = i_0 + i_1 + ... + i_8                   | Addition (Sum)                |
| `MAX`              | `0b10`   | out_data = max(i_o, i_1, ..., i_8)                 | Maximum                       |
| `MIN`              | `0b11`   | out_data = max(i_o, i_1, ..., i_8)                 | Minimum                       |

The result is made available on the output data port and will be pushed downstream if the corresponding flow control
flag (`op_exe`) is set. In case an operation should not produce output results, dynamic operands can be silenced to
reduce dynamic switching power.


### Stream Flow Control Handling

There are three flow control flags in the DWPU data path command, which have the following effects:

*	`op_exe`: The result of this operation is produced as a beat on the output stream interface.
*	`push_tlast`: The output beat produced in this operation will terminate the stream with `tlast`.

In case of a stalled input stream, data path commands continue to be executed until a data path command which expects
an input value while the input FIFO is empty. The command stream will stall thereafter until input data is available.

In case of a stalled output stream, data path commands continue to be executed until a data path command with the
`op_exe` flag set is encountered while the output buffer is full. The command stream will stall thereafter until the
output becomes free again. As the handshaking is fully implemented for the full pipeline, eventual pipeline
"bubbles" will be compressed.

!!! note

    When involving the input data stream in any part of the operation (loading into the scratchpad or weight buffer
    registers, or as an operand through sp1), the data path will expect an input stream to be present. The conditions
    for a command to expect an input item are:

    ```systemverilog
    always_comb read_from_input =
        dp_cmd_q[0].instruction.op_desc.shift_sp ||
        dp_cmd_q[0].instruction.op_desc.shift_wb ||
       (dp_cmd_q[0].instruction.op_desc.op_exe   && |any_i_sel_is_one);
    ```
