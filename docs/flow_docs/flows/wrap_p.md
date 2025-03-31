# Wrapper generation using subip hjson files

The `gen_p_wrapper.py` script does the physical wrapping of partition subips. It generates the following system verilog files.

- `subip_name_p.sv`  - Physical wrapper file (contains pipeline reg, spill reg, clock gating, etc)

## General usage

The `gen_p_wrapper.py` can be invoked in through the top-level makefile, or manually. Regardless of the invoking method, the script uses the `subip_name_p.hjson` file as a source of truth to do the generation for each partition/subip. It combines the information it finds in this files with the parsed `subip_name.sv` verilog file to generate the wrapper.

### Manually

When invoking the script manually, the target argument `-t` must be set. Further optional arguments

- `--fpga` - Generate sources for FPGA emulation. Default is `False`.
- `-debug` - Enable generation of debug hjson files (debug files are generated in the cwd).

```console
export REPO_ROOT=<replace>
python3 -m venv .venv
.venv/bin/activate
export PATH=${PATH}:${REPO_ROOT}/hw/scripts/gen_files/
cd hw/impl/europa/blocks/ai_core
pip install anytree hjson mako dataclasses
python3 $REPO_ROOT/hw/scripts/gen_files/gen_p_wrapper.py -i data/aic_infra_p.hjson -p $REPO_ROOT/hw/scripts/gen_files/protocol -r $REPO_ROOT/hw/scripts/gen_files/sv_rule.hjson
cd -```

## `subip_name_p.hjson`

This file controls both the `_p` file generation and the constraints generation(not enabled for europa). It contains all the settings that are specific to the subip. It consists of the following sections.

- `stubbing` - boolean, whether to include the `ifndef QSYN_STUB` guarding to turn the `_p` in a black box with just an interfaces.
- `constraints` - boolean, whether to generate the constraints for the subip. (not enabled for europa)
- `wrap_p` - boolean, whether to generate the `_p` wrapper file.
- `rtl_file` - string, the top-level rtl file that needs to be wrapped for the given subip.
- `clocks` - dict, settings of all functional clocks in the subip
- `resets` - dict, settings of all functional resets in the subip
- `internal_constraints` - dict, settings of all internal constraints in the subip. (not enabled for europa)
- `dft_settings` - dict, dft specific settings, both for wrapping and constraints generation
- `ports` - dict, settings for all ports of all supported protocols

### `clocks`

In the clock field all functional clocks of the subip are defined. For each clock the following settings must be provided.

- `freq` - float, clock frequency in MHz.
- `divider` - dict, whether to add a clock divider on this clock in the wrapper, the dict specifies info about the divder (see below)
- `gate` - dict, whether to add a clock gating on this clock in the wrapper, the dict specifies info about the gating (see below)

Note, `gate` and `divider` are mutually exclusive. If both are set, this will lead to an error.

Example of the clock field taken from `ai_core_mvm_p.hjson`.

```json
clocks : {
    clk : {
        freq : 800
        divider : {
            reset : rst_n
            ctrl_clk : clk
            ctrl_rst : rst_n
        }
        gate : false
    }
    jtag_tcki : {
        freq : 100
        divider : false
        gate : false
    }
}
```

#### `divider` (not enabled for europa)

If no divider is desired, the `divider` field must be set to `false`. Otherwise, the following settings must be provided.

- `reset` - string, the reset signal that is used to reset the divider.
- `ctrl_clk` - string, the clock that drives the control signals of the divider (optional, if not given, a new clock is added to the partition)
- `ctrl_rst` - string, the reset that drives the control signals of the divider (optional, if not given, a new reset is added to the partition)
- `test_enable` - string, the test_enable signal of the port. If this field is not given, the scan_mode signal is used here.

#### `gate` (not enabled for europa)

If no gating is desired, the `gate` field must be set to `false`. Otherwise, the following settings must be provided.

- `enable` - string, the enable signal that is used to control the clock gate. If this is not yet a port of the partion, a new port is created with the given name.
- `test_enable` - string, the test_enable signal of the port. If this field is not given, the scan_mode signal is used here.

### `resets`

In the reset field all functional resets of the subip are defined. Each defined reset is a dict with as keys all the clocks it relates to. Within each clock dict, a synchronisation field indicates whether or not this reset needs a synchroniser for the that clock.

Example of the reset field taken from `ai_core_mvm_p.hjson`.

```json
resets : {
    rst_n : {
        clk : {
            synchronise : false
        }
    }
    jtag_resetni : {
        jtag_tcki : {
            synchronise : false
        }
    }
}
```

### `internal_constraints` (not enabled for europa)

This fields contains information about the internal timing constraints of a partition. It is a dict with the following keys.

- `tool_dependent_variables` - dict, contains variables that are tool dependent. The keys are variable names, the values dicts in which each key is a tool with as value the value of the variable for that tool. If the tool `others` is used, this value is used for all tools that are not explicitly defined. This tool should be set last.
- `clock_groups` - dict, defines the clock groups for the partition. The keys are the names of the clock groups you with to define, value are the settings of the clock group
    - `clocks` - list, list of clocks that are part of this clock group
    - `relation` - string, the relation between the clocks in this clock group. Can be `asynchronous`, `physically_exclusive`, `logically_exclusive` or `exclusive`
    - `allow_paths` - bool/dict, indicate how you want to treat the paths between the clocks of this clock group.
        - `false`, all paths between the clocks are set as false paths (default when defining and async clock group)
        - `true`, all paths between the clocks are timed as if they are synchronous (you mannually have to relax them to avoid timing violations)
        - `max_delay` - int, all paths between the clocks get a max delay constraint for setup and a false path for hold. Only supported for clock groups of exactly 2 clocks.
- `false_paths` - list of dicts, each dict in the list describes one false path command. The dict can have the following fields.
    - `from` - string, the source pins/cells of the false path as tcl cmd/list/string
    - `to` - string, the destination pins/cells of the false path as tcl cmd/list/string
    - `through` - string, the through pins/cells of the false path as tcl cmd/list/string
    - `setup` - bool, whether to only disable setup or not
    - `hold` - bool, whether to only disable hold or not
    - `options` - string, additional options from the snps set_false_path cmd to be added
    - `post_synth` - bool, whether to only add the false path for post_synth or not
    - `comment` - string, a comment to be added to the false path constraint
- `max_delays` - list of dicts, each dict in the list describes one max delay command. The dict can have the following fields
    - `from` - string, the source pins/cells of the max delay as tcl cmd/list/string. If a tcl cmd is used and it starts with `get_cells`, it will be appended with `get_pins -of_objects [original cmd] -filter "full_name=~*/CK"` for use outside of `dc_shell`
    - `to` - string, the destination pins/cells of the max delay as tcl cmd/list/string If a tcl cmd is used and it starts with `get_cells`, it will be appended with `get_pins -of_objects [original cmd] -filter "full_name=~*/Q"` for use outside of `dc_shell`
    - `through` - string, the through pins/cells of the max delay as tcl cmd/list/string
    - `options` - string, additional options from the snps set_max_delay cmd to be added
    - `delay` - float, the max delay in ns
    - `post_synth` - bool, whether to only add the max_delay for post_synth or not
    - `comment` - string, a comment to be added to the max delay constraint
- `multi_cycle` - list of dict, each dict in the list describes one multi_cycle path comand. The dict can/must have the following fields
    - `from` - string, the source pins/cells of the multi cycle path as tcl cmd/list/string
    - `to` - string, the destination pins/cells of the multi cycle path as tcl cmd/list/string
    - `through` - string, the through pins/cells of the multi cycle path as tcl cmd/list/string
    - `options` - string, additional options from the snps set_multicycle_path cmd to be added
    - `comment` - string, a comment to be added to the multi cycle path constraint
    - `cycles` - int, the number of cycles for the multi cycle path
    - `setup` - boolean, indicates that this is a setup multi cycle path
    - `hold` - boolean, indicates that this is a hold multi cycle path, if both setup and hold are true, hold is set to the setup cycles -1. I.e., the hold bring back is added automatically in this case.
    - `post_synth` - boolean, whether to only add the multi cycle path for post_synth or not
- `case_analysis` - list, here set_case_analysis statements can be listed. For now, the whole statement without the `set_case_analysis` keyword must be provided. (see example below)
- `disable_timing` - dict, each key is a cell with as value a list of pin pairs between which timing arcs should be disabled for this cell.
- `manual_exceptions_file` - string, path to manual exceptions file (temp solution till all the fields above are in use)
- `sub_partitions` - dict, keys define the sub partitions of this partition. Value of each keys must be `flat` or `hierarchical`. If `flat`, relevant constraints from the sub partition will be used for this partition as well in all constraints. If `hierarchical`, relevant constraints from the sub partition are guarded behind `FLAT_TIMING_ANALYSIS` which should only be set when doing full flat timing analysis.

Example usage of the `internal_constraints` field taken from `ai_core_infra_p.hjson`.

```json
internal_constraints : {
    tool_dependent_variables : {
        i_aipu : {
          dc_shell : i_aipu/
          dcnxt_shell : i_aipu/
          others : i_aipu_
        }
    }
    clock_groups : {
        clk_vs_pvt_clk_i : {
            clocks : ['clk', 'pvt_clk_i']
            relation : asynchronous
            allow_paths : {
                max_delay : 1.25
            }
        }
    }
    false_paths : false
    max_delays : [
        {
            from : [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_test1*] -filter  "full_name=~*/q[0]"]
            to : [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_test_rnm*] -filter  "full_name=~*/q[0]"]
            delay : 2.0
            comment : "max delay between test1 and test_rnm"
        }
    ]
    multi_cycle : [
        {
          from : 'from_path'
          through : 'through_path'
          to : 'to_path'
          cycles : 2
          setup : true
          hold : true
          comment : "multi cycle path example that sets setup 2 and hold 1"
        }
    ]
    case_analysis : [
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_test1*] -filter  "full_name=~*/q[0]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_test_rnm*] -filter  "full_name=~*/q[0]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_rme*] -filter  "full_name=~*/q[0]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_rm*] -filter  "full_name=~*/q[0]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_rm*] -filter  "full_name=~*/q[1]"]'
    '1 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_rm*] -filter  "full_name=~*/q[2]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_rm*] -filter  "full_name=~*/q[3]"]'
    '1 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_wa*] -filter  "full_name=~*/q[0]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_wa*] -filter  "full_name=~*/q[1]"]'
    '1 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_wa*] -filter  "full_name=~*/q[2]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_wpulse*] -filter  "full_name=~*/q[0]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_wpulse*] -filter  "full_name=~*/q[1]"]'
    '0 [get_pins -of_objects [get_cells -hier *u_sram_sw_controllable_wpulse*] -filter  "full_name=~*/q[2]"]'
    ]
    disable_timing : {
        i_sram2p : [
            'CLKA CLKB'
            'TCLKA TCLKB'
        ]
    }
    manual_exceptions_file : false
    sub_partitions : {}
}
```

### `dft_settings` (not enabled for europa)

The `dft_settings` field lists dft related settings for the wrapping and functional dft clock and resets for the constraints. It has the following subfields.

- `wrap_file` - string, also run the physicall wrapping on this (dft related) file.
- `gen_tb_wrapper` - string, generate a tb wrapper for this dft related file in which dft ports are tied off. dft ports are discoverd by a diff between the port on the original file and the dft file.
- `scan_mode` - string, port name of the scan mode signal. If not set, scan_mode related ports will be tied to 0 (a warning is issued when this happens).
- `mbist` - dict, empty if partition does not have mbist, following keys if it has.
    - `original_sdcs` - string, path to the location of the mbist sdcs files produced by the mbist tooling
    - `slow_clocks` - list, list of the slow mbist clocks for this partition
    - `fast_clocks` - list, list of the fast mbist clocks for this partition
- `clocks` - dict, similar to the clocks field described above, but for clocks only present in rtl with dft.
- `resets` - dict, similar to the resets field described above, but for resets only present in rtl with dft.
- `clock_groups` - dict, similar to the clock_groups field described above, but for clock groups only present in rtl with dft.
- `internal_constraints` - dict, similar to the internal_constraints field described above, but for internal constraints only present in rtl with dft.
- `dft_ports` - dict, similar to the ports described below, but for dft ports only present in rtl with dft.

Example from `ai_core_infra_p.hjson`.

```json
dft_settings: {
    wrap_file : false
    gen_tb_wrapper : f'{os.environ["REPO_ROOT"]}/subip/ai_core/subsys/ai_core_infra/rtl/dft/mbist/ai_core_infra_p.sv'
    scan_mode : scan_mode
    mbist : {
        original_sdcs : 'subip/ai_core/subsys/ai_core_infra/dft/mbist_constr'
        slow_clocks : ['vl_srv_WRCK']
        fast_clocks : ['clk']
    }
    clocks : {
        vl_srv_WRCK : {
            freq : 100
        }
    }
    resets : {
        vl_srv_WRSTN : {
            vl_srv_WRCK : {
            synchronise : false
            }
        }
    }
    clock_groups : {
        clk_vs_vl_srv_WRCK : {
            clocks : ['clk', 'vl_srv_WRCK']
            relation : asynchronous
            allow_paths : false
        }
    }
    dft_ports : {
        defaults : {
            clock_edge : rising
            clock : async
            reset : ''
            static : {}
        }
        vl_* : {
            clock : vl_srv_WRCK
            reset : vl_srv_WRSTN
        }
    }
}
```

### `ports`

The `ports` field configures the physical wrapping of each port of the partition. It determines whether or not to add pipelining for a given port, links ports to a clock and reset for constraints generation, and allows to indicate static ports. It does this per protocol. For each protocol (`axi`, `axis`, `token`, `apb`, `misc`) default settings must be given. These can then be overwritten for a specific port within the protocol. The overwriting support simple `*` wild cards to cover ports with the same pre/post-fix. The following keys are supported.

- `clock_edge` - string, either `rising`, `falling` or `both`, indicating the clock edge on which the port is sampled.
- `pipe` - bool/int, whether or not to add pipelining/spill registers for this port. Integer value can be used to set more than one stage.
- `clock` - string, name of the clock to which this port related. If `async` is used the port becomes asynchronous to all clocks. (For now only one clock is supported)
- `reset` - string, name of the reset to which this port related. If the `clock` is `async`, this field can be an empty string. (For now only one reset is supported)
- `rate_adapter` - bool, whether or not to add a rate adaptation for this port when a (synchronous) divider is placed on the clock. (Only supported on `axi` and `axis` protocols)
- `static` - dict, indicate for which constraints mode this port is static and gives the value. (Only supported for `misc` protocol)
- `multicycle` - dict, indicate whether the port needs a multicycle path. If the port is an input then a multicycle path -from that input is added. If the port is an output, then a multicycle path -to that ouput is added. Setup and hold values can be defined for the multicycle path
- `max_delay` - float, indicate the maximum delay for the port. If set together with `multi_cycle`, `max_delay` takes priority (just like it does in the timing tools). (Only supported for `misc` protocol).
- `internal` - bool, indicate whether port should remain internal to the wrapper or not. `true`, port is not included in the wrapper. `false`, port is included in the wrapper. (Only supported for `misc` protocol)

Simple example

```json
ports : {
    axi : {
        defaults : {
            pipe : true
            clock : clk
            reset : rstn
            rate_adapter : false
        }
        other_clk_axi : {
            clock : other_clk
            reset : other_reset
        }
    }
    axis : {
        defaults : {
            pipe : true
            clock : clk
            reset : rstn
            rate_adapter : false
        }
    }
    token : {
        defaults : {
            pipe : 2
            clock : clk
            reset : rstn
            rate_adapter : false
        }
    }
    apb : {
        defaults : {
            pipe : true
            clock : clk
            reset : rstn
            rate_adapter : false
        }
    }
    misc : {
        defaults : {
            clock_edge : rising
            pipe : true
            clock : clk
            reset : rstn
            rate_adapter : false
            static : false
            multi_cycle : false
        }
        a_static_port : {
            static : {
                func : '0'
                scan_shift : false
                scan_atspeed : false
            }
        }
        a_async_port : {
            clock : async
            reset : ''
            pipe : false
        }
        *_no_pipeline_ports : {
            pipe : false
        }

        a_multicycle_port: {
          multi_cycle: {
            setup: 2
            hold: 0
          }
        }

    }
}
```

#### Port timing budgeting (not enabled for europa)

The constraints contain a input/output delay for each synchronous port. The delay value is controlled by the BE constraints configuration file. This allows to have different values for different corners and budgeting schemes. Besides the BE constraints configurations files per corner per partition, a default constraints configuration file exists for every partition. This default file is generated during the sdc generation for a partition. The default values it contains are read from `scripts/flow/default_constraints_config_settings.hjson`

#### Details on pipelining/spill registers (not enabled for europa)

The figure below show the effect of using the `pipe` field for both axi related protocols and sideband signals (`misc` protocol)

- axi related -> spill registers
- `misc` -> pipeline registers

Example for `l2`

![spill-reg-example-core](omega_p_wrappers.drawio.png)

## Debugging using python debugger in vscode

When making modifications to the hjson files, python code or make templates, debugging can be quite the hassle due to the many nested dictionaries. Using the vscode python debugger can help a lot, but it requires a custom setup in the launch.json vscode file. Below is an example of this setup.

``` json
{
    "name": "wrap_p",
    "type": "python",
    "request": "launch",
    "program": "hw/scripts/gen_files/p_wrapper/gen_p_wrapper.py",
    "console": "integratedTerminal",
    "justMyCode": true,
    "cwd": "/home/projects_2/workspace/desekhri/sandbox_europa/europa",
    "args": [
        "-t",
        "ai_core",
    ],
    "env": {
        "REPO_ROOT" : ".",
    }
}
```

Besides this setup, you will need your python version to be 3.7 or higher (the vscode debugger does not support lower anymore). Further you might have to install some pip packages(anytree hjson mako dataclasses) to your local python environment.
