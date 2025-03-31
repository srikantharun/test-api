---
title: Microarchitecture
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---


This unit is responsible of generating a stream of datapath commands from a generalized looping command.

!!! abstract "Specification"

    - [Specification](../index.md)
    - [Instructions](../instructions.md)
    - [AIC-DP-F0.2: Unified and extended Instruction Looping](https://git.axelera.ai/prod/europa/-/issues/168)
    - [AIC-DP-I2: Unification of Block Program Control](https://git.axelera.ai/prod/europa/-/issues/195)


![Block Diagram of the AI-Core Command Generator](./../figures/block_diagram.drawio.svg)


## Operating Principle

The unit works on a dataflow driven scheme. Executing a command will generate datapath instruction streams depending on
processed the command.

The [decode stage](./aic_dp_cmd_gen_decode.md) is responsible for looking at the command for validation, consume it and
generate a stream of individual loop descriptors.  It will create one *loop descriptor* transaction per existing main
loop encoded in the command.  A *loop descriptor* contains all information for executing one main loop together with any
potential nested loops.  It handles errors found in the command and is responsible for mapping the command to the
respective downstream loop descriptor.  Additionally it keeps track of all outstanding commands that have loop
descriptors in flight and handles the correct forwarding of the datapath done signal to the *command-block*.

The *metadata FIFO* contains static information from the command that is valid for the full duration of a instruction
stream.  It is loaded as part of the command validation before the decoding stage emits the loop descriptors.
The value form this FIFO is popped when the last instruction is transferred.

The [loop generator](./aic_dp_cmd_gen_loops.md) is responsible for generating the address stream for the
*instruction memory*.  The [loop generator](./aic_dp_cmd_gen_loops.md) contains an FSM and multiple counters.  The
*address counter* keeps track of the current address whereas the iteration coutners keep track of the current iteration
counts of the executed loops.  Internally the *loop descriptor* is expanded into loop sections.  Whenever the
*address counter* reaches the end of a specific loop section the logic decides where to jump next or to end the loop.
Priority decisions make sure that the proper looping sematics are followed.

The rest of the downstream datapath is responsible for proper handshaking and cycle synchroniazation between the
*metadata* and *instruction* streams. It ensures that the *instruction stream* is fully back-pressurable.


## Instantiation

This modules [package](./aic_dp_cmd_gen_pkg.md) comes with parameters and functions to configure a respective command block.

!!! example "Parameters for `cmdblock`"

    ```systemverilog
    logic                            cmd_done;
    aic_dp_cmd_gen_pkg::cmdb_cmd_t   cmdb_cmd_packed;
    aic_dp_cmd_gen_pkg::cmd_format_t cmdb_cmd_format;
    aic_dp_cmd_gen_pkg::cmd_config_t cmdb_config;
    aic_dp_cmd_gen_pkg::cmdb_cmd_t   cmdb_cmd;
    logic cmdb_valid, cmdb_ready;

    cmdblock #(
      ...
      .DYNAMIC_CMD_SIZE(aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
      .CMD_CONFIG_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CONFIG_WIDTH),
      .CMD_FIFO_WIDTH  (aic_dp_cmd_gen_pkg::CMD_BLOCK_CMD_FIFO_WIDTH),
      .NR_FORMATS      (aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
      .FORMAT_NR_BYTES (aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_BYTES),
      ...
    ) u_cmd_block (
      ...
      // Command
      .cmd_done           (cmd_done),
      .cmd_data           (cmdb_cmd_packed.view_vector),
      .cmd_format         (cmdb_cmd_format),
      .cmd_config         (cmdb_config),
      .cmd_vld            (cmdb_valid),
      .cmd_rdy            (cmdb_ready)
    );

    cmdblock_cmd_unpack #(
      .NR_FIELDS        (aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FIELDS),
      .NR_FORMATS       (aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
      .TOT_WIDTH        (aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
      .FIELD_SIZE       (aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_SIZES),
      .FIELD_OUTP_IDX   (aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_OUTP_IDX),
      .FIELD_DEFAULT_VAL(aic_dp_cmd_gen_pkg::CMD_BLOCK_DEFAULTS),
      .FORMAT_IDX       (aic_dp_cmd_gen_pkg::CMD_BLOCK_FORMAT_IDX)
    ) u_cmdblock_cmd_unpack (
      .format(cmdb_cmd_format),
      .inp   (cmdb_cmd_packed.view_vector),
      .outp  (cmdb_cmd.view_vector)
    );

    aic_dp_cmd_gen #(
      ...
    ) u_aic_dp_cmd_gen (
      ...
      .i_cmdb_command         (cmdb_cmd),
      .i_cmdb_format          (cmdb_format),
      .i_cmdb_config          (cmdb_config),
      .i_cmdb_valid           (cmdb_valid),
      .o_cmdb_ready           (cmdb_ready),
      .o_cmdb_done            (cmd_done),
      ...
    );
    ```


::: hw/ip/aic_common/default/rtl/aic_dp_cmd_gen.sv:aic_dp_cmd_gen
