---
title: "AI-Core Control Dispatcher (AIC_CD)"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

!!! tip

    For more details about the respective sub-units of the *AI-Core Control Dispatcher (AIC_CD)*, please refer to the
    [Microarchtitectural Description](microarchitecture/index.md).

## Description

Key Features of the AI-Core Control Dispatcher ([aic_cd]({{link_repo_file("hw/ip/aic_control_dispatcher/default")}})):

- Simple memory-mapped device with status CSRs and interrupts
- Offloads AI Core Datapath control operations from the CVA6V_AIC
- Provides a similar control flow as the AI Core Datapath Driver using a HW FSM

Architectural Details of the Control Dispatcher:

- CVA6V_AI sends a pointer to a task list as a command to the Control Dispatcher
- Optional interrupt back to the CVA6V_AI when command has been completed
- Contains an internal address map for each AI Core Block (CMD FIFO and PRG MEM)
- Connected to the token network with at least one consume/produce pair to each AI Core Block
- Execution done pulse signals from each AI Core Block to pessimistically determine CMD FIFO status
- Multiple channels sharing one AXI master port to handle read and copy operations
- Pre-fetching of its own list of instructions/tasks which are executed sequentially
- [Patching of addresses](./address_patching.md) within commands to anchor them to the corresponding memory pool
- Timestamp triggering with a 2-bit ID similar to SW triggered timestamps

In order to offload the control overhead for the AI Core Datapath, the CVA6V_AI can instead employ the Control
Dispatcher by sending it a pointer to an AI Core task list.  Since the AI Core Datapath control consists of mostly copy
operations from some memory to the CMD FIFO and the PRG MEM of the various AI Core Blocks, task list is primarily a list
of copy operations.  Apart from the copy operations encded as control instructions, there are also some synchronization
related instructions to facilitate the concurrent execution within the AI Core Datapath and between different AI Cores.
As an optional feature the Control Dispatcher can trigger a timestamp with an ID similar to the RISC-V.

The CVA6V_AI can poll the status CSR of the Control Dispatcher to determine whether a task list has been completed or
alternatively can be directly notified via an interrupt and/or token upon completion.

The usage of the CVA6V_AI and the Control Dispatcher to offload control is mutually exclusive to avoid concurrency
issues and proper gates are inserted in the fabric to ensure this on the lowest level.  In other words, the control mux
in the AI Core interconnect is configurable such that only one master may access both the datapath and the DMAs at
a time (with the exception of CSRs).

!["AIC_CD: Integrated in a System"](./figures/aic_cd_in_system.drawio.svg)


### Instruction Channel

The [instruction fetch](./microarchitecture/instruction_fetch/index.md) continuously pre-fetches instructions from the
offloaded task list until completion and stores the fetched instructions in the instruction FIFO.  Pre-fetching should
guarantee no overfill of the FIFO and should not fetch beyond the indicated size of the task list.

The instruction channel shares an AXI master port with other channels using a static AXI ID assignment.

Any encountered AXI error should be signaled via CSR and IRQ to the CVA6V. Furthermore, the channel needs to account
for the 4k AXI transaction boundary.


### Copy Channels

The [copy unit](./microarchitecture/copy_unit/index.md) uses read and write channel to copy data from the SPM to the
CMD FIFOs and PRG memories of the various AI Core blocks.  A data FIFO acts as an intermediate buffer between both
channels and its depth should be 32 to ensure that fabric latencies do not impact copy performance.  This FIFO should be
implemented with a memory macro to alleviate PD pressure.

Headers of commands copied to the CMD FIFOs need to be modified such that the acd_end trigger is enabled to ensure that
the completion of the command is notified via a pulse back to the Control Dispatcher.

The channels share an AXI master port with other channels using a static AXI ID assignment.

Any encountered AXI error should be signaled via CSR and IRQ to the CVA6V. Furthermore, the channels need to account for
the 4k AXI transaction boundary.

Data which needs to be copied is always stored at a word-aligned pointer in the SPM but may be copied to an unaligned
address and/or length (see send_prg instruction).  In the case of an unaligned transfer, the data *needs* to be stored
with padding to avoid the need for data rotation.  The write channel is responsible for setting the correct AXI strobe
bits to ensure that unaligned transfers are correctly executed.


### Token Unit

The [token unit](./microarchitecture/token_unit.md) blocks the execution of further instructions until all requested
token handshakes have been completed. It either handles intra-core tokens or top-level tokens at a time.


### Fill Counters

[Local fill counters](./microarchitecture/copy_unit/fill_counters.md) guarantee that commands sent to CMD FIFOs of the
AI Core blocks are not dropped due to a full FIFO there.  They pessimistically estimate the fill state of the CMD FIFOs
of the AI Core blocks by incrementing the counter on offload of a command and decrementing after completion of the
execution signaled by the acd_end triggered done pulse.

If the fill counter indicates that the targeted CMD FIFO can currently not consume another command, the execution should
be stalled until the fill counter is sufficiently decremented.

Commands have a variable size and can take multiple CMD FIFO slots. The effective number of slots needs to be calculated
on the fly based on information provided in the CSRs (`DST_CMDBLOCK_PARAMS`) and the size provided by the command
offload instruction.  The calculated number should then be used as increment and stored in a FIFO of at least depth 16
for later use as decrement again.


### Patch Unit

The [address patch unit](./microarchitecture/copy_unit/address_patching.md) [modifies the commands](./address_patching.md)
copied to the CMD FIFOs of AI Core blocks based on a preset pattern stored in the CSRs.  Specifically, it adds memory
pool base addresses on top of addresses provided in the offloaded command.  This allows the addresses of the AI Core
block commands to be relative to a base address which can be derived dynamically during runtime rather than being
absolute physical addresses (memory allocation).

The `patch mode` of the offload instruction indicates which of the preset patching patterns stored in the CSRs is to be
applied.  A patch mode may patch up to two different address fields within the offloaded command. The memory pool base
address for each patch is provided via a table stored a-priori in the CSRs and accessed via the patch IDs provided in
the offload instruction.

!!! tip "Disable Patching"

    A patch mode of 'b0 disables this feature.

A patch pattern consists of the command word index of the field to be patched (4-bit wide) and the byte width of the
field (4-bit wide).

!!! note

    Patching may only be applied to fields aligned to a word boundary.


## Programming Model

<!-- TODO(@wolfgang.roenninger) Reference to new chapter if this is a bit more fleshed out by Architecture.-->

The programming model will be prototyped with Drv-FIAT using the Verification SDK.  It will generally consist of
rendering the pre-existing task list into a Control Dispatcher compatible binary which is then kicked-off by the
CVA6V_AI (after switching the control access over to the Control Dispatcher).

Omega ATEX compatibility ensures that any Omega ATEX can be rendered to such a Control Dispatcher compatible binary.


## Configuration

The following configurations via CSRs are **required**:

- Setting up the control data memory region which by *default* is set to the SPM. *(optional)*
    - `CTRL_DATA_BASE_ADDR`: To point to the memory to copy data from.
- Setting up the internal address map of the CMD FIFOs and PRG MEMs for each AI Core Block. **(REQIRED)**
    - `DST_ADDR_COMMAND`: For the CMD FIFO locations.
    - `DST_ADDR_PROGRAM`: For pointing to the respective program memories.
- Setting up the command fifo parameters for each destination. **(REQIRED)**
    - `DST_CMDBLOCK_PARAMS`: Specify number of lines and bytes per line for each CMD FIFO. Needed for the fill counters.
- Setting up the patch table and patterns for memory pool addresses *(optional)*
    - `PATCH_MODE`: Specify how and where to patch in a command.
    - `PATCH_TABLE`: Specify the memory patterns for patching.
- Enabling the Control Dispatcher including the command done interrupt if desired. *(optional)*
    - `IRQ_EN`: Enable the respective Interrupts.


!!! tip "Interrupts"

    *All* interrupts are enabled by default. Including the *command done* interrupt.


## Runtime Interactions

During compilation a properly encoded task list must be placed in the dedicated control data memory region, the location
of which is then to be provided to the Control Dispatcher via a command from the CVA6V_AI.  The task list consists
mostly of control instructions which encode copy operations of commands and programs to the various AI Core Blocks.
The below diagram summarizes the interaction.

![AIC_CD: Control Flow](./figures/aic_cd_control_flow.drawio.svg)

Generally, the task list is expected to have a final token instruction to report back to the CVA6V_AI.
Alternatively, the core can poll a status CSR of the Control Dispatcher or an IRQ can be raised.
