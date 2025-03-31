---
title: "Manager Address Calculation"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---


The actual addresses for AXI request on the *manager port* are **offset** from the values in the instructions by
various mechanisms.

- Via a **static port** `i_aic_base_addr`: This port is constant set and corresponds to the respective ai-core where the
  `aic_cd` is instantiated.
- Via the **CSR** `CTRL_DATA_BASE_ADDR`: This CSR should be set up once and not be changed whilst a task list is in flight.
- Via the *command* `control_offset`: This is given via the command and usually unique for each task list.
- Via the *instruction* fields: This gives the final offsets or indices to look addresses up in the *CSRs*.

To summarize, we list each address type and the corresponding offsets to consider:

| Address Type   | Calculation for final Address                                                                      |
|:-------------- |:-------------------------------------------------------------------------------------------------- |
| Task List      | `i_aic_base_addr + csr.ctrl_data_base_addr + command.task_list_ptr`                                |
| Command Source | `i_aic_base_addr + csr.ctrl_data_base_addr + command.control_offset + instruction.cmd.command_ptr` |
| Program Source | `i_aic_base_addr + csr.ctrl_data_base_addr + command.control_offset + instruction.prg.program_ptr` |
| Command Target | `i_aic_base_addr + csr.dst_addr_command[instruction.cmd.dst_id]`                                   |
| Program Target | `i_aic_base_addr + csr.dsr_addr_program[instruction.prg.dst_id] + instruction.prg.dst_address`     |
