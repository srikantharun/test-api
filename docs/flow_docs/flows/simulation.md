# Simulation

Two simulators are supported by the Europa simulation flow
1. [QUESTA](https://eda.sw.siemens.com/en-US/ic/questa/simulation/advanced-simulator/)
2. [VCS](https://www.synopsys.com/verification/simulation/vcs.html)

Questa is the default simulator due to license allocation.

## Setting Up A Simulation Environment

All simulations should be run in a sim directory as defined in the [verification directory structure documentation](../../europa_verification/dv_directory_structure.md).

By default all simulations should support both VCS and Questa. However, if there is a specific reason only a single simulator is supported the directory should be named appropriately (sim_questa, sim_vcs).

### Configuring The Simulation

Each sim directory should support a single configuration of a simulation environment. i.e. all compile and elaboration time options must remain constant for all runs in that directory.

i.e.
- +defines
- parameters etc.

In the sim directory there must be a link to the [simulation.mk](../../../hw/scripts/flow_makefiles/simulation.mk).

The simulation can be configured by including local:

| Configuration File | Purpose |
| ------------------ | ------- |
| simulation_config.mk | Makefile options common to all simulators|
| questasim_config.mk | Makefile options specific to Questa |
| vcs_config.mk | Makefile options specific to VCS |

#### Common Simulation Options

| Option | Description |
| ------ | ----------- |
| TIMESCALE | Default simulation timescale (default=1ns/1ps) |
| GLOBAL_DEFINES | +define+ options applied to all compiled source |
| PLUSARGS | +<> options applied to all runs |
| GUI | Run with gui (default=0) |
| COVERAGE | Run with coverage enabled (default=0) |
| DEBUG | Run with all waves collected and all debug option enabled (default=0 / 1 when GUI=1) |

#### Simulator Specific Options

- Questa options are prefixed **VSIM_**

| Option | Description |
| ------ | ----------- |
| VSIM_VLOG_OPTS | Additional options passed to compiliation stage|
| VSIM_VOPT_OPTS | Additional options passed to optimization stage|
| VSIM_ELAB_OPTS | Additional options passed to elaboration stage|
| VSIM_RUN_OPTS | Additional options passed to run stage|


- VCS options are prefixed **VCS_**

| Option | Description |
| ------ | ----------- |
| VCS_VLOGAN_OPTS | Additional options passed to compiliation stage|
| VCS_ELAB_OPTS | Additional options passed to elaboration stage|
| VCS_RUN_OPTS | Additional options passed to run stage|

## Grid Submission

By default all CPU intensive commands (compile, run etc.) are submitted to the Slurm grid.

In order to efficiently run the grid tokens are used to model license and timeouts are set to avoid hogging machines.

### Timeouts

The user can configure:

| Option | Description |
| ------ | ----------- |
| SIM_COMPILE_TIME_MINUTES | Timeout for compile stages (default=15mins) |
| SIM_RUN_TIME_MINUTES | Timeout for run stages (default=1h 12h when GUI=1) |
| SIM_COVERAGE_TIME_MINUTES | Timeout for coverage stages (default=60mins) |

Its the users responsibility to ensure these settings are optimal (but reliable) for their testbenches. The timeouts should be set to catch bad jobs.

### Tokens

Grid tokens are used to model licenses. For both simulators these are split into batch and interactive licenses.

The interactive tokens are to be used by humans (not bots) to get a slot and license quickly when then are running jobs. The batch tokens are used in regressions and CI jobs.

To get an interactive token:

```shell
make run_vsim DEBUG=1
make run_vsim GUI=1 # GUI option automatically adds debug
```

Alternatively you can explicitly set:

```shell
make run_vsim QUESTA_LICENSE_TYPE=questa_interactive
make run_vcs  VCS_LICENSE_TYPE=vcs_batch
```

The relationship between tokens and actual licenses can be tracked: [in grafana](https://10.1.2.113:3000/d/c78e4919-68c8-4b8c-9ba3-582429d4622c/slurm-token-usage?orgId=1&from=now-7d&to=now)


## Compile and Elaboration

Each simulator builds 2 exectuables:
- Optimised for regression
    - No signal visibility
    - No runtime access (force, release, break etc.)
    - Highest simulation throughput
- Optimised for debug
    - All signals automatically captured to waves
    - Full runtime access (force, release, break, etc.)
    - Able to collect coverage (if requested)
    - Slower simulation throughput

Both builds should produce the same results for the same testcase / seed combination.

**NOTE:** Simulation equivalence for same seed is not guarenteed between simulators

```shell
# Compile for Questa
make compile_vsim
```
```shell
# Compile for VCS
make compile_vcs
```

### UVM

By defining UVM=1 in the configuration the makefiles automatically build the UVM libraries provided by the simulators and add the correct compile and run-time options for optimal debug.

In simulation_config.mk:
```shell
UVM ?= 1
```

The following defines are also added:

```shell
##% UVM @@ {(0), 1 } @@ Automatically build for UVM
UVM       ?= 0
ifneq ("$(UVM)", "0")
override GLOBAL_DEFINES += +define+UVM_NO_DPI
override GLOBAL_DEFINES += +define+UVM_NO_DEPRECATED
endif
```

### +defines

As [Bender](https://git.axelera.ai/ai-hw-team/docs/-/wikis/User-Guides/Bender-Guideline) is responsible for the compilation commands and is simulator agnostic, +defines for the verification code should be defined in the bender.yaml file.

Details on how to do this can be found [here](https://git.axelera.ai/ai-hw-team/docs/-/wikis/User-Guides/Bender-Guideline#sources-defines-optional).

e.g.
```yaml
# Source files
sources:
  - target: simulation
    defines:
      MY_DEFINE_WITH_VALUE: 1
      MY_DEFINE_WITHOUT_VALUE: 
    files:
        - some_file.sv
```

Additionally the user can define GLOBAL_DEFINES either on the commandline or makefile. These are applied to all compile commands.

e.g.
```shell
override GLOBAL_DEFINES += +define+FROM_MAKEFILE
```
```shell
make run_vsim GLOBAL_DEFINES=+define+FROM_CMDLINE
```



## Run

The specific test to be run is define by 2 options:
- TESTNAME
- SEED

If SEED is no explicity defined a random seed will be generated.

**NOTE**: By default TESTNAME is aliased to UVM_TESTNAME

```shell
# Run on Questa
make run_vsim TESTNAME=my_test SEED=1
```

```shell
# Run on VCS
make run_vcs TESTNAME=my_test SEED=1
```

### Pre and Post Run commands

Hooks are provided to allow the user to define make targets that get execute before and after the main run stage.

These can be defined in the simulation_config.mk.

```shell
PRE_SIM_TARGETS += my_pre_target

my_pre_target:
  cd $(VSIM_RUN_DIR)
  echo "01 02 03 04" > somefile.txt


POST_SIM_TARGETS += my_post_target
my_post_target:
  cd $(VSIM_RUN_DIR)
  if [ ! -f some_expected_file.txt ] -a [ -f PASSED ]; then \
    mv PASSED FAILED; \
  fi

```

### +plusargs

+plusargs are commonly used to configure tests.

The case be supplied on the commandline:

```shell
make run_vsim PLUSRAGS=+x1
```

Multiple plusargs must be captured within quotes.

```shell
make run_vsim PLUSARGS="+x1 +x2=123"
```

Or added to the simulation_config.mk

```make
override PLUSARGS += +y1 +y2 +y3=abc
```

**NOTE**: The override is important to allow commandline and makefile defined options to be used together. Without the override the commandline would superseed the makefile variables.

### sv_libs

sv_libs are used to link C libraries used for SystemVerilog DPI funcions.

The syntax is common accross simulators so can be defined in the common simulation_config.mk.

```shell
SV_LIBS += -sv_lib MY_LIBS
```

You can also use the following variables to automatically compile and link sv_libs:

| Option | Description |
| ------ | ----------- |
| DPI_C_SRC | Source files to compile together |
| DPI_C_OPTS | Extra args to pass to the compiler |
| DPI_C_INCDIR | Include directories |


### Running without recompiling

Adding NODEPS=1 will avoid any recompilation. This is the default for all sims when run under regression.

```shell
# Run without re-compiling
make run_vcsim TESTNAME=my_test SEED=1 NODEPS=1
```

### Running with Debug and / or GUI

By default simulation run in the optimised mode.

To run with debug:
- DEBUG=1

To run with a gui:
- GUI=1 (automatically enables DEBUG=1 unless explicitly overriden)

Once generated, waveforms can be opened with `waves`

### Checks and Exit Status

The exit status of the make command is generated from:
- The exit status of the simulator
and
- A grep for simulator specific error and fatal strings

The simulators are configured to:
- Error on assert
- Exit on first error

A clear message of status should also be reported at the end of a sim e.g.

```shell
 _____         _____ _____ ______ _____  
|  __ \ /\    / ____/ ____|  ____|  __ \ 
| |__) /  \  | (___| (___ | |__  | |  | |
|  ___/ /\ \  \___ \\\___ \|  __| | |  | |
| |  / ____ \ ____) |___) | |____| |__| |
|_| /_/    \_\_____/_____/|______|_____/ 
```

## Regressions

Regressions are controlled by `verifsdk` (in-house tool developped by the FW team) and CTest.

Together they are responsible for:
- Compiling the design
- Running simulations in parallel
- Merging coverage results into a single report

### Defining a Regression

Regressions are defined with labels and platforms affected to every test within a `test_*.yaml` file. These YAML files are located inside `$REPO_ROOT/verifsdk`.

Labels and platforms are defined inside [config.yaml](../../../verifsdk/config.yaml):

```yaml

-platforms:
  - name: uvm.MY_PLATFORM_NAME
    run_script: ./run_uvm.sh
    flags: --test_bench=/path/to/my/tb/sim/directory
    default_flavors: [sim.VSIM]

#...

labels:
  -name: MY_REGRESSION_NAME
```

Tests are located inside [tests_uvm.yaml](../../../verifsdk/tests_uvm.yaml). You can also put them in a separate file as long as it resides inside `verifsdk/` and match `tests_*.yaml`.

To know more about how to define a test, read the corresponding [README](../../../verifsdk/README.md).

Add the label to the tests you wish to run.

```yaml
  - name: my_test
    labels: [MY_REGRESSION_NAME]
    platforms: [uvm.MY_PLATFORM_NAME]
    # ...
    repeat_count: 6
    seeds: [4444,333,22] 
```

The configuration above would run 6 simulations:

3 with fixed seeds:

- my_test.4444
- my_test.333
- my_test.22

3 with random seeds 

### +plusargs

You can specify plusargs for your test in the following manner:

```yaml
  - name: test_soc_periph_axi_tb
    # ...
    flags: [+foo, +bar]
```

Every flag starting with a `+` will be interpreted as a plusarg. The example above would result in `PLUSARGS="+foo +bar"` being passed to the makefile.

### Running a Regression

To run a regression, you need to provide:
- a label
- the platform name you want to run the regression on

```shell
# Run under Questa
make regress_vsim REGRESS_VERIFSDK_LABEL=MY_REGRESSION_NAME \
                  REGRESS_VERIFSDK_PLATFORM=MY_PLATFORM_NAME

# Run under VCS
make regress_vcs REGRESS_VERIFSDK_LABEL=MY_REGRESSION_NAME \
                  REGRESS_VERIFSDK_PLATFORM=MY_PLATFORM_NAME
```

By default, jobs are run one by one. To increase parallelism, you can set the environment variable `CTEST_PARALLEL_LEVEL` to the number of concurrent jobs you want.

```shell
# Configure CTest to run 10 jobs in parallel
export CTEST_PARALLEL_LEVEL=10
make regress_vsim ...

# Equivalent syntax
CTEST_PARALLEL_LEVEL=10 make regress_vsim ...
```

## Coverage

### Collecting Coverage

Coverage can be enabled by adding COVERAGE=1 to the command lines.

```shell
make run_vsim COVERAGE=1
```

```shell
make regress_vsim ... COVERAGE=1
```

By default all code and functional coverage is collected.

### Viewing Coverage

Coverage reports are generated automatically at the end of regressions, but can be generated on the fly.

The report will automatically merge all coverage that has been collected in the workspace.

```shell
make report_vsim_coverage
```

The report will be place in <build_dir>/<sim>_coverage/html

Alternatively the results can be viewed in the simulator specific gui.

```shell
make view_vsim_coverage
```

```shell
make view_vcs_coverage
```

## Cleaning

```shell
# Clean Questa
make clean_vsim

# Clean VCS
make clean_vcs

# Clean everything
make clean
```


## Utils

### Using sf5a models


For tech cells by default functionnal models are used.
For technology selection a tuple of [Bender targets](https://doc.axelera.ai/prod/europa/0.0/flow_docs/guides/bender_style_guide/#sources-target-technology-specifier) are used to select the relevant source files.
It is possible to use the sf5a models by updating the simulation_config.mk and questasim_config.mk as follows:

In simulation_config.mk :

```shell
BENDER_TARGETS_EXT += asic sf5a
```

If running non-timing annotated simulations one should additionally turn off timing specifications by adding to questasim_config.mk:

```shell
VSIM_ELAB_OPTS_EXT += +nospecify
```

!!! note "+nospecify" 
    This plusarg is used to turn off time delay modelling in the simulation. 

    If for RTL simulations the models add timing delays, stimuli application can desync between the testbench and RTL. Because some of the clock trees might add additional delays causing the flops to have a different clock skew compared to the testbench code driving them. This then dealings the clock with the rest of the signals.

