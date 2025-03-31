# Synthesis

Currently RTL-Architect is supported by the Europa synthesis flow
1. [RTL-Architect](https://www.synopsys.com/implementation-and-signoff/rtl-synthesis-test/rtl-architect.html)

RTL-Architect (rtl-a) is currently the default synthesis tool.

## Setting Up A Synthesis Environment

Synthesis should be run in a dedicated synthesis directory which can be generated using cookiecutter.
For Information on Cookiecutter see [IP generation](ip_generation.md)

Run the following commands to setup the rtl-a synthesis directory structure:
```shell
cd <PATH TO IP/Block>
cookiecutter  --verbose <PATH TO europa>/hw/scripts/cookiecutter/synth_directory/
cd synth_rtla
```

### Configuring The Synthesis runs

In the synth_rtla directory there must be a link to the [rtla_synth.mk](../../../../hw/scripts/flow_makefiles/rtla_synth.mk).

The synthesis can be configured by including local:

| Configuration File | Purpose |
| ------------------ | ------- |
| rtla_setup.tcl | Synthesis configuration and run options specific to the IP/Partition |

The actual tool specfic run commands are present in the rtla_setup.tcl file. 
All the RTL-A commands that are custom for the particular IP/Block should be included here.

## Grid Submission

By default all CPU intensive commands (compile, run etc.) are submitted to the Slurm grid.

In order to efficiently run the grid tokens are used to model license and timeouts are set to avoid consuming machine resources.

### Tokens

Grid tokens are used to model licenses.

The relationship between tokens and actual licenses can be tracked: [in grafana](https://10.1.2.113:3000/d/c78e4919-68c8-4b8c-9ba3-582429d4622c/slurm-token-usage?orgId=1&from=now-7d&to=now)

## Run

```shell
make help
```

```shell
make run_<RTLA STEP>
```

| Command | Description |
| ------ | ----------- |
| run_rtla_elab | Run RTL-Architect till the Elaboration step |
| run_rtla_cond | Run RTL-Architect till the Conditioning step |
| run_rtla_est | Run RTL-Architect till the Estimation step |
| run_rtla | Run RTL-Architect till the chosen step - default Elaboration |
| all | Run RTL-Architect till the chosen step - default Elaboration |

### Running with Debug and / or GUI
 TBD

### Checks and Exit Status

The exit status of the make command is generated from:
- The exit status of the synthesis tool.

## Cleaning
TBD

