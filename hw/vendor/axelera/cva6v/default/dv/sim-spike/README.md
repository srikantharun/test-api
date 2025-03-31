
# Spike - Only Regressions Documentation

To run spike-only regressions for a specific test list or C test, use the commands below.

## Common Directories

- OSS YAML Test list path: `$CVA6_VERIF_HOME/tests/`
- C test path: `$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/c/manual_tests/`

## Setup Environment and Modules

```sh
source $REPO_ROOT/.env-default-modules
cd $REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/sim-spike
```

# Compiling the testbench

The testbench compiles like all others, (vsim strongly recommended due to license availability)

```sh
make compile_vsim
```

or

```sh
make compie_vcs
```

# Instructions for Running Spike Tests with VerifSDK

## Open source testsuites

Open source testsuites can be found here: [$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/deps/tests](../deps/tests)

As many of these tests contain gcc specific pragmas they are not compiled as part of verifsdk.

All the open source testsuites are pre-compiled as a prerequisite of the testbench compilation. The commands for this can be found here: [$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/cva6v_oss_config.mk](../cva6v_oss_config.mk).

All tests are compiled by default, regardless of if you run them. This should take around 30 seconds, but is a big simplification of the flow.

Although compiled seperately all tests are run under verifsdk (see next section).

## Preparation

1. **Add YAML with Test List**
   - Add the test list YAML file in `$REPO_ROOT/verifsdk`.

2. **Add Tests**
   - Add your tests in the directory: `sw/src/tests/test_cva6v_dv_<yourtestsuite>`.

3. **Update Configuration**
   - Add any new labels in `sw/verifsdk/config.yaml`.

### Labels

Labels should be used to group tests into sensible, well defined categories.

- All CVA6V tests should be labelled `CVA6V_DV_TESTS`.
- More labels should be added as appropriate.

For example:
```sh
tests:
  - name: cva6v_oss_riscv_arch_rv64i_m-add-01
    description: "TODO"
    labels: [CVA6V_DV_TESTS, CVA6V_DV_OSS_TESTS, CVA6V_DV_OSS_ARCH_TESTS]
    requirement_ids: []
    platforms: [cva6v.*]
    owner: Abhilash Chadhar
    flags: [ELF=$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/deps/tests/build/riscv-arch-test/riscv-test-suite/rv64i_m/I/src/add-01]
```

This is an open source architecture test. As such it has the labels:
- CVA6V_DV_TESTS (indicates it's a CVA6V test)
- CVA6V_DV_OSS_TESTS (indicates it's an Open Source test)
- CVA6V_DV_OSS_ARCH_TESTS (indicates it's an Open Source architecture test)

The lable `CVA6V_DV_MR_TESTS` should be used to add the test to the MR CI job (on all CVA6V testbenches).

### Open Source Tests

When adding open source tests to the regression (see above), not no cva6v source files are in the test declaration.

Alternatively a flag containing ELF=`<path to elf file>` indicates the test binary.

## Compilation

1. **Create Build Directory**
   ```sh
   mkdir $SIM_SPIKE/build
   ```

2. **Compile Tests**
   - Use the following command to compile tests with specific platform and label:
     ```sh
     verifsdk -P <platform> -L <label>
     ```
   - Example:
     ```sh
     verifsdk -P cva6v.SPIKE_COVERAGE -L CVA6V_DV_C_TESTS -v
     ```

3. **Compile Single Test**
   - To compile a single test, use:
     ```sh
     verifsdk -P <platform> -L <label> -R <testname>
     ```

## Running Tests

1. **Navigate to Test Directory**
   ```sh
   cd <testname>
   ```

2. **Run the Test**
   ```sh
   ./run.sh
   ```

## Running Regression

- For running regression tests, use the following command from the spike-sim directory:
  ```sh
  make regress_vsim REGRESS_VERIFSDK_LABEL=<label> REGRESS_VERIFSDK_PLATFORM=<platform>
  ```

---

### Notes:
- For CVA6V tests 2 make variables must be provided:
   - TESTNAME (indicates the directory name to run inside)
   - ELF (indicates the binary to be loaded)
- Replace `<platform>`, `<label>`, and `<testname>` with the appropriate values for your setup.
- Ensure that all paths and environment variables are correctly set before executing the commands.

### Run Spike

A makefile fragment makes running spike simple:
- [$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/cva6v_spike_config.mk](../cva6v_spike_config.mk)

### Convert to CSV

```bash
cva6_spike_log_to_trace_csv --log /path/to/output/test_spike.log --csv /path/to/output/test_spike.csv
```

### Generate Object Dump

```bash
riscv64-unknown-elf-objdump -d /path/to/output/test.o > /path/to/output/test.S
```
