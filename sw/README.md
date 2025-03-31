# Firmware Verification

This directory contains the software tests for Europa, as well as supporting files.

Building and running the tests is done using our tool `verifsdk`.
For more information on VerifSDK and how to add firmware tests, see [`verifsdk/README.md`](verifsdk/README.md).

[[_TOC_]]

## Supported Platforms

Firmware tests can be run on various platforms, each of which has a different set of trade-offs.
Some of these are documented [here](https://axeleraai.atlassian.net/wiki/spaces/SOFTWARE/pages/370278404/Emulators+FPGA+VELOCE).

The platforms include:
* Skyray (fastest)
* Veloce (medium fast, close to silicon)
* Simulation (slowest, easy access to waves)
* Real Silicon (after tapeout)
* Spike (accurate, processor only without access to any MMIO)

These platforms are usually only available on certain hosts due to availability of software and/or hardware.
Certain platforms also provide (interactive) debugging support via JTAG.

### Veloce

TODO

### Simulation

TODO

### Skyray

Skyray is an custom in-house FPGA emulation platform.
It is the fastest non-silicon platform we have access to.
However, mapping to Skyray requires modifications to the RTL which make it slightly less true to the final design.

> For example, the Skyray mapping of the APU contains only a single RISC-V core (instead of 6).
> Furthermore, a custom crossbar setup and memory map are used instead of the final NoC.

#### Availability

Skyray requires the correct FPGA hardware, which is available on certain hosts in the Zürich office.
A list of these hosts and their allocation to users/teams is [avaliable on Confluence](https://axeleraai.atlassian.net/wiki/spaces/archrd/pages/556007425/Skyray+for+Europa#%F0%9F%96%A5%EF%B8%8F-Hardware-Allocation).

#### Setup

First, follow the
[Skyray Quick Start Guide](https://axeleraai.atlassian.net/wiki/spaces/archrd/pages/556007425/Skyray+for+Europa#%F0%9F%9A%80-Quick-start-Guide)
to set up permissions, the Skyray CLI, and program the correct bitstream.

Second, ensure `skyray` is avaliable in your `$PATH` (output may differ depending on bitstream version):
```sh
europa:$ skyray info shell
Emulated design: apu
Shell ID string: apu_r2_shell_id5r5
Shell git SHA: 4fa2a793ca31a675
Emulation git SHA: 9a2fa526b57ed94c
```

Third, set up the Europa environment:
```sh
europa:$ source .env-setup-silverlight
```

Fourth, create a build directory and `cd` to it:
```sh
europa:$ mkdir -p sw/build
europa:$ cd sw/build
```

Fifth, use `verifsdk` to build and run firmware tests (with the `top.SKYRAY` platform):
```sh
europa/sw/build:$ verifsdk -P top.SKYRAY -R test_hello_world --ctest --verbose
```

### JTAG

> **Note:** Currently, JTAG is only supported when using the Skyray platform.

Skyray supports running and debugging tests using JTAG.
For this, add `--jtag`  to the `verifsdk` command line (before `--ctest`).

This does not affect the build process of the test binaries.
However, it adapts the run script so it launches OpenOCD and GDB to connect to the target using JTAG.

To run a single test (example: `test_hello_world`), execute its run script:
```sh
europa/sw/build:$ cd test_hello_world
europa/sw/build/test_hello_world:$ ./run.sh
```
This will run the test non-interactively and report success or failure at the end.

For interactive debugging, add the `--debug` option to the run script.
This will open the GDB prompt.
To load the binary, set breakpoints at `main` and `exit`, and run the test, perform the following steps:
```sh
europa/sw/build/test_hello_world:$ ./run.sh --debug
(gdb) load
(gdb) break main
(gdb) break exit
(gdb) run
```

> It is strongly recommended to use UART printing (`-F printf.UART`) when using JTAG.
> This is because the front-end server (FESVR) printing used with Skyray by default does not work with GDB.
> If FESVR printing is still used, the test will hang in `fesvr_syscall` every time it attempts to print.
