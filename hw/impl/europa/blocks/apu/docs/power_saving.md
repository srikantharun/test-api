# Power saving


## Andes AX65

The automatic power saving features are implemented at the cluster level.

### Core clock gating

Each core of the APU will be gated when in Waiting For Interrupt (WFI) mode.

The core will ungate if there is a pending interrupt, nmi or debugint.

!!! tip "Power Efficiency"

    Firmware should make sure to filter incoming interrupts at the PLIC/SWPLIC
    level else the core may never gate

### Core DCU clock gating

At cluster level, when for a given gated core, the data coherency is disabled,
the dcu_clk can be gated.

This clock is driving the logic to handle the data coherency between the core
and l2c.

!!! tip "Power Efficiency"

    Firmware should make sure to disable core data coherency before entering WFI

### L2c clock gating

At cluster level, when all the cores DCU clocks are gated, the l2c can be gated.


## AXI Fabric

When no AXI transaction is sensed in the apu fabric, part of the modules are
gated. Detection/tracking is done in some edge manager module.

The number of `IDLE_DELAY` cycles can be set in the AO CSR (up to 255 cycles).

The bus clock will ungate if a transaction is pending from 1 of the edge manager
(using `aw`/`ar` valid input).

Not affected by this gating:
- PLIC: check incoming IRQs
- PLMT: not losing track of time
- token_manager: responding to external requests
- Bus multicuts: outside of `apu.sv` scope
- AX65 AXI bus: too much risk/low reward to touch Andes internal files
