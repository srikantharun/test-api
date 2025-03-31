---
title: Error Detection & Interrupts
doc:
  status: review
  version: [2, 0, 0]
  confidentiality: internal
---

**TODO(@wolfgang.roenninger): Update this when the command generation gets replaced by `aic_dp_cmd_gen`!**

# Error Detection & Interrupts

The DWPU detects different illegal program conditions. These are signaled in the IRQ CSRs as follows:

| IRQ Name             | Size (bits) | Edge/Level | Polarity | Description |
|:-------------------- |:-----------:|:----------:|:--------:|:----------- |
| ERR_ACT_STREAM_IN    | 1           | Level      | High     | Active input stream while terminating command stream according to [triton#88](https://git.axelera.ai/ai-hw-team/triton/-/issues/88) |
| ERR_ACT_STREAM_OUT   | 1           | Level      | High     | Active output stream while terminating command stream according to [triton#88](https://git.axelera.ai/ai-hw-team/triton/-/issues/88) |
| ERR_ILLEGAL_FORMAT   | 1           | Level      | High     | The provided format index of the command header is unexpected. |
| ERR_EMPTY_PROGRAM    | 1           | Level      | High     | Program is empty, i.e., the combined lengths of all sections is zero. |
| ERR_INIT_LEN         | 1           | Level      | High     | The `init` section length is larger than available instruction memory. |
| ERR_OUTER_LEN        | 1           | Level      | High     | The `outer` section length is larger than available instruction memory. |
| ERR_INNER0_LEN       | 1           | Level      | High     | The `inner0` section length is larger than available instruction memory. |
| ERR_INNER1_LEN       | 1           | Level      | High     | The `inner1` section length is larger than available instruction memory. |
| ERR_INNER0_SEGFAULT  | 1           | Level      | High     | The `inner0` section exceeds the boundaries of the `outer` section. |
| ERR_INNER1_SEGFAULT  | 1           | Level      | High     | The `inner1` section exceeds the boundaries of the `outer` section. Or `inner1_start` > `inner0_start`. |
| ERR_INNER1_NO_INNER0 | 1           | Level      | High     | The `inner1` section is present without an `inner0` section. |
| ERR_INNER1_OVERLAP   | 1           | Level      | High     | The `inner1` and `inner0` sections are overlapping. |
| CMDBLK_CMD_DROPPED   | 1           | Level      | High     | The command block dropped a command. |
| SWDP_CMD_DROPPED     | 1           | Level      | High     | The software command was dropped. |

The behavior of DWPU upon encountering certain error detection conditions can be changed using the `SKIP_ILLEGAL_PROG`
CSR according to the following table:

| Detected Error      | Behavior if `SKIP_ILLEGAL_PROG = 0`      | Behavior if `SKIP_ILLEGAL_PROG = 0`      |
|:------------------- |:---------------------------------------- |:---------------------------------------- |
|ERR_ACT_STREAM_IN    | Program terminates, streams corrupted    | Program terminates, streams corrupted    |
|ERR_ACT_STREAM_OUT   | Program terminates, streams corrupted    | Program terminates, streams corrupted    |
|ERR_ILLEGAL_FORMAT   | Skip program without signaling `dp_done` | Skip program without signaling `dp_done` |
|ERR_EMPTY_PROGRAM    | Skip program without signaling `dp_done` | Skip program without signaling `dp_done` |
|ERR_INIT_LEN         | Program executes, instr. address wraps   | Skip program without signaling `dp_done` |
|ERR_OUTER_LEN        | Program executes, instr. address wraps   | Skip program without signaling `dp_done` |
|ERR_INNER0_LEN       | Program executes, instr. address wraps   | Skip program without signaling `dp_done` |
|ERR_INNER1_LEN       | Program executes, instr. address wraps   | Skip program without signaling `dp_done` |
|ERR_INNER0_SEGFAULT  | Program executes but structure undefined | Skip program without signaling `dp_done` |
|ERR_INNER1_SEGFAULT  | Program executes but structure undefined | Skip program without signaling `dp_done` |
|ERR_INNER1_NO_INNER0 | Program executes but structure undefined | Skip program without signaling `dp_done` |
|ERR_INNER1_OVERLAP   | Program executes but structure undefined | Skip program without signaling `dp_done` |
