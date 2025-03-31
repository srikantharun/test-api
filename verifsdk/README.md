# Verification SDK

The Verification SDK (also VerifSDK, `verifsdk`) is the centralized tool for running any sort of verification tests on Europa.

Its primary purposes are
* specifying platforms on which we can run tests ranging from simulation to Veloce and Skyray,
* specifying test lists including multiple test types (UVM, firmware, ...),
* configuring the target platform,
* launching the tests (using `ctest`).
Optionally, one can compile C code and provide binaries to be loaded on specific platforms.

Its primary purposes are
* specifying test lists including multiple test types (UVM, firmware, ...),
* compiling the firmware tests themselves, and
* configuring and launching the test driver (`ctest`).

It has support for multiple platforms (e.g., simulation, Veloce, Skyray, ...), flavors, and labels.

[[_TOC_]]

## Quickstart Guide

VerifSDK is available in `$PATH`  after sourcing the relevant `$REPO_ROOT/.env-*` file.

First, create a build directory to avoid polluting the source tree:
```sh
europa $ mkdir -p sw/build
europa/sw/build $ cd sw/build
```

Second, run `verifsdk`  with the relevant arguments. For example, to build and run all tests with label `SMOKE_SKYRAY` on the Skyray platform, execute the following command:
```sh
europa/sw/build $ verifsdk -P SKYRAY -L SMOKE_SKAYRAY --ctest
Test project /local-ssd/mwipfli/europa/sw/build
      Start  1: test_coremark
 1/15 Test  #1: test_coremark ...........................   Passed    4.28 sec
      Start  2: test_dhrystone
 2/15 Test  #2: test_dhrystone ..........................   Passed    3.89 sec
[...and so on...]
      Start 15: test_nested_critical_sections
15/15 Test #15: test_nested_critical_sections ...........   Passed    3.97 sec

100% tests passed, 0 tests failed out of 15

Total Test time (real) =  59.27 sec
```

> **Note:** For running tests on the Skyray platform, the `skyray` CLI needs to be installed and available in `$PATH`.

For more information on what arguments to pass to `verifsdk`, refer to the sections below.

## The `verifsdk` Tool

When running `verifsdk`, the tool performs multiple steps:

1. Parse CLI arguments and YAML files.
2. Configure the tests to run and their behavior based on the CLI arguments.
3. (if needed) Compile and link the firmware sources into an ELF file (only for firmware tests).
4. Create a run script to execute the tests.
5. Execute the tests using the `ctest` driver (only if `--ctest` is specified).

### CLI Arguments

`verifsdk` takes a multitude of command line arguments.
The most commonly used ones are explained below.
For the full list, see `verifsdk --help`.

* **Platform (`-P`):**
  This specifies the target platform for executing the tests.
  For firmware tests, this could be `top.SKYRAY`, `aicore.VELOCE`, or similar.
  For UVM tests, the format is `uvm.*`, where the suffix specifes the test bench (e.g., `uvm.SIM_SOC_PERIPH_AXI`).
* **Label (`-L`):**
  This can be used to select a subset of tests to run.
  For example, to run all tests that are run by the Skyray smoke-test CI, use `-L SMOKE_SKYRAY`.
* **Flavors (`-F`):**
  Flavors are used to modify the behavior of tests.
  For example, to print via UART, add the `-F printf.UART` flavor.
  Multiple flavors may be specified by separating them with a space.
  Some platforms define default flavors that are applied automatically (unless they are explicitly overridden).
  It is not possible to specify multiple flavors with the same prefix (i.e., only one `printf.*` can be active at a time).
* **Run `ctest` (`--ctest`):**
  By default, the tool prepares everything for testing without executing the tests themselves.
  This flags makes `verifsdk` run the tests at the end.

> **Note:**
> All command line arguments after `--ctest` are forwared to the `ctest` execution.
> This allows specifying `--verbose` to see the test outputs, for example.

### Examples

All examples assume the environment has been set up by sourcing the relevant `$REPO_ROOT/.env-*` file.

> **Note:**
> Most platforms are only available in certain environments due to hardware/software requirements.
> For example, `*.VELOCE` platforms are only available on the Veloce server.
> Further setup may be required for some platforms.

#### Compile and Run All (Compatible) Tests on Skyray

```sh
sw/build:$ verifsdk -P top.SPIKE --ctest
```

#### Compile And Run All Tests With Label SMOKE_SKYRAY on SKYRAY

First, install the Skyray CLI on the machine:
```bash
europa:$ python3.10 -m venv .venv
europa:$ source .venv/bin/activate
europa:$ pip install skyray
```

Then, call `verifsdk`:
```sh
europa:$ mkdir -p sw/build && cd sw/build
europa/sw/build:$ verifsdk -P SKYRAY -L SMOKE_SKYRAY --ctest
```

## YAML configuration

The `verifsdk` tool is configured using a series of YAML files:
* `config.yaml`: contains supporting configuration (platforms, flavors, labels, library sources)
* `tests_*.yaml`: contains definitions of individual tests

### `config.yaml`

This file contains all configuration which is not specific to individual tests.

This includes the following sections:
* `platforms`:
  A platform must provide a run script located within the `$REPO_ROOT/sw/scripts/run` folder.
  This script is called by `ctest` to run the test.
* `labels`:
  Each label defines a regression.
  For example, this is used to select tests to run during a `SMOKE_SKYRAY`.
* `flavors`:
  Flavors allow to fine tune tests based on some requirements.
  It allows to specify additional flags or files to alter the compilation flow.
  For example, it can be used to define a set of DDR flavors.
* `lib`:
  These are the sources which get compiled for all the tests.
  It contains mostly drivers and general settings.
  The corresponding include directories are specified automatically by the build flow.

> **Important Notice I: Additional flags and files:**
> For each of the two `platforms`, and `labels` one can provide additional compiler flags and files to be used during the compilation process.
>
> By default, these files are only added to the "main" processor (i.e., APU for the top-level).
> This can be adjusted by specifing the `processors` attribute.

> **Important Notice II: Default flavors:**
  For each `platforms` one can provide `default_flavors`.
  They are overwritten by any CLI arguement with the same flavor tag.

> **Important Notice III: Flavors tagging:**
  Each flavor requests a prefixed tag.
  The tag can be seen as a group of flavors.
  Each test can either support individual flavors or flavor tags.
  For example, if there are 20 DDR flavors all marked with `ddr.SOME_TYPE_OF_DDR`, `ddr.SOME_OTHER_TYPE_OF_DDR`, it is sufficient to mark a test with the tag to support all flavors within the tagged group `flavors: [ddr.*]`.

### `tests_*.yaml`

These files include the definition of individual tests.
The tests are split up into multiple files according to their nature (e.g., firmware vs. pure UVM tests).

Each test defines the following attributes:
* `name`: Name of the test, required to be globally unique.
* `description`: 1-3 sentence description of what the test does and what it verifies.
* `owner`: Person responsible for the test. First point of contact if the test fails or there are any questions.
* `requirement_ids`: Requirement IDs linked to the test. ID = prefix_block_category_optional_description_index
* `platforms`: Platforms which the test can run on. If `verifsdk` is called with another platform, the test will be filtered out by `verifsdk`.
* `labels`: Labels for the test, mostly used to specify different regressions. The test will be filtered out if a label is specified on the command line that is not present here.
* `flavors`: Flavors which are required by this test. The test will be filtered out if this flavor is not present.
* `flags`: Defines the flags to use at build time or runtime.
  **Important:** If a flag start with a single dash, it will be consumed by the build process. Else they will be forwarded to the run script.
* **(firmware tests only)** Test-specific C and assembly source files for the different processors. Paths must be specified relative to `$REPO_ROOT/sw/src/tests/`.
  * `apu`: source files for the APU,
  * `aicore0`: source files for AICORE 0,
  * `aicore1`: source files for AICORE 1,
  * and so on...
* **(UVM tests only)**
  * `repeat_count`: Number of times a test should be run. (default: 1)
  * `seeds`: List of fixed seeds.
    If `len(seeds) < repeat_count`, `verifsdk` generates the missing seeds.
    If `repeat_count`  is omitted, no seeds are generated.

### Adding Tests

#### Firmware Tests

To add a firmware test (example: `test_foo`), create the directory `src/tests/test_foo` and add a C file (preferably named `test_foo.c`).

In this file, define a `main` function and add your test as follows:
```c
#include <printf.h>
#include <testutils.h>

int main() {
  testcase_init();

  CHECK_TRUE(2 * 4 == 8, "2 times 4 is not 8.");

  return testcase_finalize();
}
```
For a reasonably complex test, take a look at `src/tests/test_decoder_reg/apu/test_decoder_reg_info.c`.

Then, add your test to `tests_fw.yaml` as follows:
```yaml
  - name: test_foo
    description: Test to check if math works as it should.
    requirement_ids: [] # add IDs of requirements that are checked by this test
    labels: [] # add labels where this test should be included
    platforms: [top.*] # test runs on top-level (i.e., APU)
    owner: John Doe
```

To build an run the test (e.g., on Veloce), run
```sh
europa/sw/build:$ verifsdk -P top.VELOCE_TOP_LIGHT -R test_foo --ctest --verbose
```

#### Pure UVM Tests

Each testbench maps to a separate `uvm.*` platform.
Pure UVM tests that do not require any kind of software use a common run script: `run_uvm.sh`.
To add support for a new testbench, define it as follows (in `config.yaml`):
```yaml
  - name: uvm.SIM_SOC_PERIPH_AXI # your testbench name. Must start with 'uvm' for clarity.
    run_script: ./run_uvm.sh # The script to use
    flags: --test_bench=hw/impl/europa/blocks/soc_periph/dv/axi_tb/sim # Sim directory location from $REPO_ROOT
    default_flavors: [sim.VSIM] # Default simulator to use, either sim.VSIM or sim.VCS
```

To add a test, define it as follows (in `tests_uvm.yaml`):
```yaml
  - name: test_soc_periph_axi_tb
    description: "Pure-UVM test that stresses SOC_PERIPH AXI bus"
    requirement_ids: [] # Fill in requirement IDs
    labels: [SOC_PERIPH_NIGHTLY]
    platforms: [uvm.SIM_SOC_PERIPH_AXI] # specify on which tb the test runs
    repeat_count: 6 # How many times we repeat the test
    seeds: [4444,333,22] # What seeds to use
    flags: ["UVM_VERBOSITY=UVM_DEBUG"] # Put optional makefile args here
    flavors: [] # Add additional flavors if needed
    owner: Jerome Sauger # Register as owner of the test
```

To build and run the test, run
```sh
europa/sw/build:$ verifsdk -P uvm.SIM_SOC_PERIPH_AXI -F sim.VCS -R test_soc_periph_axi_tb --ctest --verbose
```

If you want to pass arguments to `make` on-the-fly, add them to the `verifsdk` command before `--ctest`

##### Plusargs

You can specify plusargs for your test in the following manner:

```yaml
  - name: test_soc_periph_axi_tb
    # ...
    flags: [+foo, +bar]
```

Every flag starting with a `+` will be interpreted as a plusarg. The example above would result in `PLUSARGS="+foo +bar"` being passed to the makefile.

##### Reuse the same UVM test

By default, the test name is passed to the makefile as `TESTNAME` which is the default value of `UVM_TESTNAME`. It must be unique to avoid clashes. `verifsdk` will issue an error if there are duplicates. To run the same UVM test but with different plusargs/flags, specify `UVM_TESTNAME` in the flags:

```yaml
  - name: test_foo
    # ...
    flags: [UVM_TESTNAME="test", +foo]

  - name: test_bar
    # ...
    flags: [UVM_TESTNAME="test", +bar]
```
