# 💾 top-level simulation
Run your tests in simulation

For more info, see the [top-level verification documentation](https://doc.axelera.ai/prod/europa/latest/europa_verification/top_level)

## 👅 Top-level Flavors

All top level flavors are based on the real top platform (`hw/impl/europa/emulation/src/hdl/top`).
The main goal is to provide smaller platforms to reduce the load on veloce. It is achieved by stubbing modules in the real top.
In simulation the main goal is to have the same platforms than in emulation and also to reduce compile and elaboraiton time.


### Available flavors

- `top`: full top with IMC banks bypassed - 17 boards
- `top_light`: 6 boards
    - APU
    - SOC_MGMT
    - SOC_PERIPH
    - SYS_PERIPH
    - SYS_SPM
    - All L2
    - DCD
    - PVE0
    - PCIe
    - All fake LPDDR
- `top_aic0`: 9 boards
    - APU
    - SOC_MGMT
    - SOC_PERIPH
    - SYS_PERIPH
    - SYS_SPM
    - All L2
    - All fake LPDDR
    - Full AIC0

### How to stub

To stub modules global defines are used. They are specified in the `simulation.mk` (`hw/impl/europa/dv/<top_name>/`).
Currently only the modules instantiated in [aipu.sv](https://git.axelera.ai/prod/europa/-/blob/main/hw/impl/europa/asic/rtl/generated/aipu.sv) can be stubbed.

## 🚀 Usage
### Environment
```sh
cd <EUROPA_REPO>
source .env-default-modules
source .env-verifsdk-helper
```

### Run
#### With fw Function
`fw()` is a helper function for human usage only. It allows to choose between platform and tests easily.
```sh
fw # choose SIM_TOP_LIGHT and test_hello_world
cd test_hello_world
./run.sh --force_compile --debug
```

##### Compile another test
Once you have chosen a platform, `fw` generates the build files for all the associated tests.
This why if you invoke it and a build folder for the platform already exists, it won't prompt you to choose
tests to compile.
If you want to compile another test for the same platform, you can simply do:

```sh
fw # Brings you back to the build directory
ninja <test name>
cd <test name>
./run.sh --debug #...
```

Or call verifsdk as in the section below.

#### Without fw Function
```sh
mkdir build_light
cd build_light
verifsdk -P SIM_TOP_LIGHT --only test_hello_world
cd test_hello_world
./run.sh --force_compile --debug
```
#### Recompile a test

`.env-verifsdk-helper` provides a `recompile` command to easily recompile the test in the current directory:

```sh
cd test_hello_world
./run.sh #...
# Do some debug and modify the C code
recompile
./run.sh #...
```

#### Regressions
How to run a regression label:
```sh
# e.g.: run SIM_TOP_LIGHT_NIGHTLY label
export CTEST_PARALLEL_LEVEL=8
cd hw/impl/europa/dv/top_light
make regress_vsim REGRESS_VERIFSDK_LABEL=SIM_TOP_LIGHT_NIGHTLY
```

| Regression            | Description                  | Source                                                                      | Link                                                                                                                                                                                                             |
| ----------            | -----------                  | ------                                                                      | ----                                                                                                                                                                                                             |
| SIM_TOP_LIGHT_NIGHTLY | run C tests on top_light DUT | [Gitlab pipelines](https://git.axelera.ai/prod/europa/-/pipeline_schedules) | [Grafana dashboard](https://grafana.htz1.axelera.ai/d/d9a8bbfa-a146-4c4a-8e7f-f5320866ff12/verifsdk-dashboard?orgId=1&var-selected_platform=top.SIM_TOP_LIGHT&var-selected_labels=SIM_TOP_LIGHT_NIGHTLY)   |

#### 📦 Simulation Releases
You can use the `--release` instead of `--force_compile` to use the CI releases instead of compiling the top-level yourself:
```sh
./run.sh --release # no waves
./run.sh --release --debug # waves
```

#### 🌊 Waveforms & CPU Traces
Waveforms and CPU traces are generated when passing the `--debug` option to `./run.sh`.

⚠Waveform buffering can be an issue when simulation is stopped via CTRL-C; use --gui instead⚠

When the simulation is done:

* call `waves` to open the wavesforms
* call `fw_trace_utils -n` to navigate CPU traces

#### 🎦 GUI
You can invoke the GUI to avoid waveform buffering and to allow interactive debugging:
```sh
./run.sh --gui # '--gui' and '--gui --debug' are equivalent
```

#### 🚄 Profiling
To know why your simulation is slow, you can profile it:
```sh
./run.sh PROFILE=1 --force_compile
visualizer -fprofile+perf fprofile/vsim_*.fdb
```
