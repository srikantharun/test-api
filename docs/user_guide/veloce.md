# ⚡️ emulation
Compile and run your tests on the emulator

For more info, see the [top-level verification documentation](https://doc.axelera.ai/prod/europa/latest/europa_verification/top_level)

## ✨ Features
- fast: runtime x1000 faster than simulation
- clear: look at info.txt and filelists/ to know how your database was compiled
- debug: triggers, waveforms on the whole design, etc

## ⚠ Limitations
- clocks: frequency cannot be changed through register access
- analog modules: PLL, PVT etc are blackboxed
- cycle based: delays are not modeled

## 🖥 IT
```sh
# from Hetzner
ssh 10.4.1.10

# to be run only once per user
/home/tools/scripts/setup_hosts.sh
```

Clone your repo and work in `/home/data2/$USER`

If you don't have any account on the Veloce infrastructure, please contact:

- amedeo.scuotto@axelera.ai
- antoine.madec@axelera.ai

### VNC

By default, VNC access is not set up on the veloce machine, but you can enable it.
On the veloce machine, run the following command:

```bash
vncserver -geometry 1920x1080 # Adjust the resolution depending on the screen you use
```

You will be prompted to input a password. Once done, the following message is printed out:

```bash
New 'caq-jj45-main3:<desktop id> (<username>)' desktop is caq-jj45-main3:<desktop id>
```

On your laptop, open your VNC client and connect to `10.4.1.10:<desktop id>`. Then enter the password you typed in and voila!

## 🤖 CI
Tests are running on the Veloce in the [nightly/weekly CI](https://git.axelera.ai/prod/europa/-/pipeline_schedules) CI:

- Veloce CI tests are defined in `.gitlab/ci/pipelines/dynamic/emulation.gitlab-ci.yml` and `pipemaster_metadata.yml`
- regular FW tests can be found in `sw/src/tests/tests.yaml`


## 🚀 Usage
### Environment
```sh
cd <EUROPA_REPO>
source .env-setup-veloce
```

### Compile
Compilation info is logged in `info.txt`

Figures:

- available boards: 32
- `./compile --dut top --bypass_imc_bank_on_all_cores `: 5h30; 420 kHz; 17 boards
- `./compile --dut top_light`: 3h20; 420 kHz; 6 boards
- `./compile --dut top_aic0`: 4h; 530 kHz; 9 boards

#### Veloce Releases
Release builds are compiled nightly by the CI:
```sh
cp -rf /home/data2/builds/release/europa/<build_name> .
```

#### Manual Build
You can also manually build a database:
```sh
# compile
cd $REPO_ROOT/hw/impl/europa/emulation
./compile --dut DUT_NAME -o DATABASE_NAME

# usage
./compile -h
```

#### How to stub

To see what is stubbed and to change it, the file `global_defines.cfg` in `hw/impl/europa/emulation/inputs/compilation/<top_name>/` is used.
Currently only the modules instantiated in [aipu.sv](https://git.axelera.ai/prod/europa/-/blob/main/hw/impl/europa/asic/rtl/generated/aipu.sv) can be stubbed.


### Run
```sh
cd DATABASE_NAME

# run sanity test
./run sanity

# list test
./run -l

# usage
./run -h
```

TCL prompt:
```tcl
help_ax
help_ax command
```

To run multiple tests without having to reload the database each time:
```sh
# Start the emulator and launch a tcl server on it
./run -t

# In another terminal send commands to this server to run tests
./run -a sanity
./run -a hello_world
```
Note: this is how regressions are run in the nightly.

#### Regressions
How to run a regression label:
```sh
# e.g.: run VELOCE_TOP_LIGHT_NIGHTLY label
cd <DATABASE_NAME>
# This script calls verifsdk under the hood
$REPO_ROOT/hw/impl/europa/emulation/bin/ci/run_fw_tests -L VELOCE_TOP_LIGHT_NIGHTLY
```
To re-run a single regression test:
```bash
cd build/<test name>
./run.sh
```

| Regression                  | Description                 | Source                                                                      | Link                                                                                                                                                                                                    |
| ----------                  | -----------                 | ------                                                                      | ----                                                                                                                                                                                                    |
| VELOCE_TOP_LIGHT_NIGHTLY | run C tests on top_light DUT | [Gitlab pipelines](https://git.axelera.ai/prod/europa/-/pipeline_schedules) | [Grafana dashboard](https://grafana.htz1.axelera.ai/d/d9a8bbfa-a146-4c4a-8e7f-f5320866ff12/verifsdk-dashboard?orgId=1&var-selected_platform=top.VELOCE&var-selected_labels=VELOCE_TOP_LIGHT_NIGHTLY) |

#### SW compilation
`./run` uses `verifsdk` to compile the C code that will be backdoor loaded in memories.

The SW code used is in `$REPO_ROOT/sw`.
Make sure to have a version of the SW code that is compatible with the HW used to compile the database.
See `./info.txt` to get the git sha1sum used to compile the database.

To clean the SW build, do:
```sh
rm -rf ./build
```

#### Instruction Dump (traces)
```sh
# AX65 dump (APU)
./run my_test --dump_ax65_instructions

# CVA6V dump
./run my_test --dump_cva6v_instructions

# then, to navigate the instructions
fw_trace_utils -n
```

#### Waveforms
```sh
./run <test_name> -i

# in tcl prompt, there are 3 options:

# 1: continuously dump all the waves; VERY SLOW
> dump_waves <dir_name>  # dir_name can be any name, this will open the velwavegen server and store waves in veloce.wave/<dir_name>.stw
# wait for tcl prompt, then you can use the following commands
> run # start test execution and wave dump
> stop # stop test execution (might not be necessary if test runs until the end)
> exit # exit velwavegen and interactive mode

# 2: one shot: dump waveform buffer featuring the 100k last cycles only
> run # start test execution
> stop # stop test execution when desired
> dump_buffer <dir_name> # dir_name can be any name, this will open the velwavegen server and store waves in veloce.wave/<dir_name>.stw
# wait for the velwavegen process to complete
> exit # exit velwavegen and interactive mode

# 3: continuously dump signals passed at compile time; almost no runtime impact
# groups are defined in hw/impl/europa/emulation/input/compilation/<dut>/xwave_siglist.txt file
# and add "rtlc -xwave_siglist xwave_siglist.txt" in veloce.config
> dump_xwaves <group>
> run
# on test completion, click enter to get to tcl prompt and then
# (test can be stopped any time with "stop")
> exit

# visualize waves:
# make sure velwavegen process are done running in background
# THIS COMMAND REQUIRES TO BE RUN FROM A TERMINAL WITHIN A VNC SESSION!!!!
# To setup a VNC session, see the 'VNC' section above.
vis -tracedir veloce.wave/<dir_name>.stw
# click on the double edge arrow to see the waves on the full time range
```

To run for a specified number of nanoseconds, use the following command. This is particularly useful in combination with `fw_trace_utils` to execute up to a specific instruction of interest and capture the waveforms at that point in time.

```sh
# run for exaclty 1000ns
> run 1000ns
```

#### UART
UART TX is always:

- printed on the Veloce stdout
- written in `./uart_0.log`

For interactive UART terminal:
```sh
# uart terminal
# wait for the emulator to start

./uart
# to invoke in xterm: ./uart -x
```

## 🚧 TODO
- JTAG/gdb
- PCIe/qemu
