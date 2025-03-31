# 🔧 fw_trace_utils

## Introduction

In simulation or emulation, CPUs have the ability to generate traces describing which instructions were executed, at what time and from which address. Once matched against the disassembly file generated at compile time, the full program execution is uncovered. `fw_trace_utils` automates this matching process to make easier for the user to navigate the trace.

A full video tutorial is available [here](https://axeleraai.atlassian.net/wiki/spaces/Silicon/pages/772079713/19+09+2024+-+DV+Tips+and+Tricks+C+test+debugging+w+Antoine).

## Required files

In order to work properly, `fw_trace_utils` requires 3 files:

- a trace file named `instruction_dump_<whatever>_id<specified hart id>.log`
- a disassembly file that ends with `.S`
- a binary named like the disassembly file minus `.S`

If you are compiling your C tests with `verifsdk`, the disassembly and binary files are automatically generated in the same directory.

To generate trace files in simulation, specify the `--debug` option when running your test: 

```bash
./run.sh --debug
```
In emulation, specify one of (or both) `--dump_ax65_instructions` and `--dump_cva6v_instructions`:
```bash
./run <test name> --dump_ax65_instructions --dump_cva6v_instructions
```

## Open fw_trace_utils

Launch `fw_trace_utils` within your test folder:

```bash
fw_trace_utils -i <core id>
```
By default, it looks to open the trace of core 0.

### Normal mode

Without the `--nvim` option, `fw_trace_utils` displays a quick summary of the program's execution and exits:

```
#---------------------------------------------------
# function calls
#---------------------------------------------------
1225.00 ns:resume:@0000000007000000
1225.00 ns:ipipe:0:reset 0007000000
1225.00 ns:resume:@0000000007000000
1225.00 ns:ipipe:0:reset 0007000000
57175: 7000000 _start
234575: 70037e4 _init
941025: 70066ea main
10217625: 7005a6a uvm_sw_ipc_quit

#---------------------------------------------------
# function exec times
#---------------------------------------------------
uvm_sw_ipc_quit                       : [18000]
_start                                : [10178450]
_init                                 : [10001050]
main                                  : [9294600]
```

### UI Mode

To navigate the CPU trace, specify the option `--nvim`. This switch instructs `fw_trace_utils` to display the trace alongside the disassembly in a neovim window:

![fw_trace_utils start screen](./img/fw_trace_utils_nvim_win.png)

The disassembly window automatically updates whenever the cursor changes line inside the trace window.

The toolbar at the top of the trace window possess clickable buttons to display additional information:

- **Prev call**: position the cursor on the line of the previous function call
- **Next call**: position the cursor on the line of the next function call
- **Main**: position the cursor on the first line of the main function
- **List calls**: display a window that lists all functions calls in the program, in order of appearance. Clicking on an entry automatically updates the trace window.
- **Source code**: toggle source code display. If the program has been compiled with debug symbols (it is the case for `verifsdk` tests), `fw_trace_utils` can find the source code corresponding to the current instruction and display it.
- **Sync Cores**: Update all other tabs with regard to the current timestamp of the current tab. See [multicore mode](TODO)
- **Reload**: close and re-open the UI. `fw_trace_utils` preserves the current line.
- **Quit**: Close `fw_trace_utils`.

Shortcuts for these buttons exist:

| Mapping | Corresponding Button |
|------|------|
| `[l` | Prev call |
| `]l` | Next call |
| `]m` | Main |
| `C` | List calls |
| `S` | Source code |

To customize them, refer to the [user config section](TODO) below.

#### Multicore mode

`fw_trace_utils` can display several trace logs at once to allow debugging in a multicore setting. Its argument `-i` accepts a list of core ids:

```bash
fw_trace_utils -n -i <core id 1> <core id 2> <core id 3>
```

This will launch `fw_trace_utils` with one tab per core. Synchronization between these cores is achieved through the timestamps present in the trace files. By clicking on **Sync Cores**, all other tabs will be updated so that their current instruction is the one executed at the same time as the selected instruction in the current tab.

## User config

You can define your own keymaps and options for `fw_trace_utils`.

To do so, create a file called `~/.config/fw_trace_utils/config.lua`.

It will be automatically sourced by `fw_trace_utils` whenever you open it.

Here is an example of it:


```lua
-- You can look up key symbols here:
-- https://neovim.io/doc/user/map.html#map-which-keys

-- Mappings for toolbar actions
-- These values correspond to the default mappings
local toolbar_keymaps = {
  prev_func = "[l",
  next_func = "]l",
  jump_to_main = "]m",
  reload = nil,
  -- If a value is nil,
  -- no mapping is set for the corresponding button.
  -- Here the quit button is not mapped to anything.
  quit = nil,
  function_calls = "C",
  source_code = "S",
  toggle_sync_cores = nil
}

-- Additional mapping to map CTRL+F to search
vim.keymap.set("n", "<C-f>", "/")

-- If you're feeling fancy you can even change the colorscheme :)
vim.cmd.colorscheme("elflord")

-- You must return the toolbar keymaps so that fw_trace_utils can process them
return toolbar_keymaps
```

