# Formal Verification Flow
This document presents the steps to populate the structure required to run VC Formal.

## Required tools

Load environment defaults:
```shell
source .env-default-modules
module load cookiecutter
```

## Generate the structure

Similarly to IP generation, a `cookiecutter` setup is available for generating Formal Verification structure.

If you want to run at IP level:
```shell
cd hw/ip/<ip>/default
cookiecutter ../../../scripts/cookiecutter/fv_directory
```

If you want to run at block level:
```shell
cd hw/impl/europa/blocks/<block>
cookiecutter ../../../../scripts/cookiecutter/fv_directory
```

This will create a Formal Verification directory at `fv` with the scrips required and the basic `SV` and `tcl` files to complete:

```
fv
├── cc
│   ├── connections.csv
│   ├── run.tcl
│   └── settings.tcl
├── dpv
│   ├── host.qsub
│   ├── run.tcl
│   └── settings.tcl
├── dpv_model
│   └── <model>.cpp
├── fpv
│   ├── run.tcl
│   └── settings.tcl
├── Makefile
└── src
    ├── Bender.yml
    ├── bind_<design>_sva.sv
    └── <design>_sva.sv

```

### Files to complete

#### CC

The connection descriptions needs to be included in the `connections.csv` file. If you wish, you can create multiple `CSV` files and add them in the `settings.tcl` file.

Check the `settings.tcl` file to ensure the settings are aligned with your design: design name, blackboxes, and the `CSV` files to be included.

#### FPV

The properties required to validate the design needs to be added in the <name>_sva.sv file. It's important to keep the name like the example otherwise the flow will disable them.\
You can split the properties into different files as far as you bind them using the `bind_<design>_sva.sv` file.

Check the `settings.tcl` file to ensure the settings are aligned with your design: design name, clks, resets, etc.\
If you need to snip drivers or blackbox designs, you can do it in the `settings.tcl` file.

### DPV

The abstract model is populated in the `<model>.cpp`.\
The `settings.tcl` file is import to define the constraints for the input and to stablish the output relationship between both spec and impl. Other important variables are set in the `settings.tcl` file.

## Running VCF

The generic command to run FPV - Formal Property Verification - is:

```shell
make -C fv run_fpv
```

To run CC - Connectivity Checking - is:

```shell
make -C fv run_cc
```

To run DPV - DataPath Validation - is:

```shell
make -C fv run_dpv
```

There are some option that can be used:
- `GUI=1` - if you pretend to run with GUI
- `FV_TOP=<top-level-name>` - Only required if you need to change the top-level name defined in the settings file (like in cc_lib)
