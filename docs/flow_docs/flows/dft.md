## Environment setup

Environment setup is identical to the design flow. No one-time setup is needed but some modules should be loaded on every new shell.

### Per-shell setup:

Load environment defaults:
```shell
. .env-default-modules
module load cookiecutter
```

(Optional) Select DFT release:

```shell
# List available releases
module avail dft -l
# Show release information
module show dft/shared-scratch
# Switch to one of the releases
module switch dft/shared-scratch
```

Loading the dft module exports the `DFT_HOME` environment variable which is used for releasing RTL and compiling DFT inserted RTL.

## DFT module variants

There are three kinds of DFT modules:

- `dft/local-scratch`: Set `DFT_HOME` inside the current git repo. Only you can access the generated DFT files. Used for pipe cleaning blocks.
- `dft/shared-scratch`: Set `DFT_HOME` to a common scratch area. Everyone loading the module has the same view of the generated DFT files. Used for trials and sharing partially complete work.
- `dft/<YYYY-MM-DD>`: Set `DFT_HOME` to a tag-aligned RTL release. Read-only. Used for CI and to pass on to PD.

## Creating DFT insertion directory

Similarly to IP generation, a `cookiecutter` setup is available for generating DFT RTL insertion scripts.

Example for L2 block:

```shell
cd hw/impl/europa/blocks/l2
cookiecutter ../../../../scripts/cookiecutter/block_dft_directory
```

This will create a DFT scripts directory at `hw/impl/europa/blocks/l2/dft`:

```
dft
├── insertion
│   ├── logic_test
│   │   ├── logic_test.do
│   │   ├── removed_files.lst
│   │   └── run.sh -> ../../../../../dft/scripts/run.sh
│   └── memory_test
│       ├── memory_test.do
│       └── run.sh -> ../../../../../dft/scripts/run.sh
├── Makefile -> ../../../../../scripts/flow_makefiles/dft.mk
├── release.sh -> ../../../dft/scripts/release.sh
└── tessent_setup.tcl -> ../../../dft/dofiles/tessent_setup.tcl
```

## Running DFT insertion

Run `memory_test` and `logic_test` insertion, in that order, as available:

```shell
make -C dft rtl_insertion
```

### Other commands

You can run each stage individually, for example:

```shell
make -C dft logic_test
```

A `clean` command is available. This will clean all `tsdb_outdir`, `build_*` and `*.log` directories and files found within the DFT directory:

```shell
make -C dft clean
```

## Releasing RTL

After running insertion, you can push the generated RTL so it is visible to other users of the same `DFT_HOME`:

```shell
make -C dft rtl_release
```

## Compiling DFT inserted RTL

Use the same command as design compile but point to the DFT Bender.yml and use the DFT bender target:

```shell
make -C sim-questa BENDER_MANI_LOC=../rtl/dft BENDER_TARGETS_EXT=dft compile_vsim
```

If no Bender.yml exists at that location, create one that depends on `..` (non-DFT RTL) and `$DFT_HOME/<block_name>` (DFT release).

## Simulate DFT inserted RTL

The `simulation_config.dft.mk` is setting up the simulation flow to point to the dft inserted rtl

```shell
make -C sim-questa/ SIM_FLOW_CONFIG=simulation_config.dft.mk run_vsim
```

You need to load the dft module to export the `DFT_HOME` environment variable.

## Simulate DFT inserted RTL

The `simulation_config.mbist.mk` is setting up the simulation flow to point to the dft inserted rtl.
It is been used to run the mbist block simulations

```shell
make -C sim-questa/ SIM_FLOW_CONFIG=simulation_config.mbist.mk PATTERN_NAME=MemoryBist_P1 run_vsim
```

You need to load the dft module to export the `DFT_HOME` environment variable.
The available options for the PATTERN_NAME are:
 - ICLNetwork
 - MemoryBisr_BisrChainAccess
 - MemoryBist_P1
 - MemoryBist_ParallelRetentionTest_P1

## Generate PD constraints

The following scripts are expected by PD:

- `<block>.preserveDFT.tcl`: Exclude Tessent blocks from FC synthesis optimization
- `<block>.insertDFT.tcl`: Stitch scan chains in FC
- `<block>.cnsMbist.sdc`: MBIST modal constraints
- `<block>.cnsAtspeed.sdc`: Fast capture modal constraints
- `<block>.cnsShift.sdc`: Shift modal constraints

For flow description, check the section **FC scripts and SDC constraints development flow** at https://axeleraai.atlassian.net/wiki/spaces/Silicon/pages/734757077/DFT+deliveries+and+milestones .

### `sdc_gen` flow

After you have a `<block>.insert_dft.v` netlist from PD, you can use the semi-automated `sdc_gen` flow to generate `cnsMbist.sdc`, `cnsAtspeed.sdc`, `cnsShift.sdc`:

1. Copy `aic_infra/dft/sdc_gen` to your block at `<block>/dft/sdc_gen` (cookiecutter flow not supported).
2. `cd <block>/dft/sdc_gen`
3. Find the DFT TSDB that originated the netlist:
   - It's the path starting with `/data/releases/europa/dft/` in the `read_rtl.tcl` sourced by PD
   - Navigate to `/data/releases/europa/dft/.../<block>/<date>/tsdb/logic_test/tsdb_outdir`
4. If a `*.hierfix.sdc` file is NOT present in the released TSDB, run `import_sdc` flow:
   - Edit `import_sdc.sh` by pointing `infile` to the correct TSDB
   - `./import_sdc.sh`: This will generate a `*.hierfix.sdc` in the current folder
5. Edit `sdc_gen_mbist.tcl`, `sdc_gen_atspeed.tcl`, `sdc_gen_shift.tcl`:
   - Change the `DESIGN` variable to your block's name
   - If needed, edit netlist path
   - If needed, edit `*.hierfix.sdc` path
6. `./run.sh`: This will generate all required `<block>.cns*.sdc` constraints
   - Set SDC_SIMPLIFIER=0 if you don't want to use the sdc_simplifier.py
7. Hand edit constraints as required
   - See examples at https://axeleraai.atlassian.net/wiki/spaces/Silicon/pages/734757077/DFT+deliveries+and+milestones
   - See https://git.axelera.ai/ai-pd-team/europa/-/issues/144
8. Copy constraints to `<block>/synth-rtla/constraints/dft`

### Releasing SDC

When your constraints are ready in `<block>/synth-rtla/constraints/dft`, you can release them into the PD area as such:

```shell
make -C dft sdc_release
```

This script will do the following:

1. Identify the correct release directory (`/data/europa/pd/europa/constraints/dev_<block_name>_p/src/exceptions/dft`)
2. Perform renaming (e.g. `<block_name>.cnsMbist.sdc` -> `<block_name>.dft.mbist.tcl`)
3. If file already exists, appends `.old` to the previous version

## ATPG (sanity check level)

1. Optional: Find TSDB associated with netlist

```shell
make -C dft find_dft_release_of_netlist NETLIST=/data/europa/pd/(...).insert_dft.v
```

2. Create ATPG directory

```shell
make -C dft create_subblock_atpg_dir
```

3. Run ATPG

```shell
make -C dft atpg
```
