# How to integrate a new macro into the Europa flow

## Step 1

1. Get the macros generated/into hetzner by PD (Sebastiaan), for a RAM you will need:
  - data width
  - number of words
2. Ask IT (Amedeo) to sync the new macros to Veloce (else your CI jobs will not find the new macros)

## Step 2

How do we go from having a macro to having the instance in our IPs (adding it to the flow and all of that)

1. add the new macro definitions in https://git.axelera.ai/prod/europa/-/blob/main/hw/ip/tech_cell_library/default/data/ips.yml?ref_type=heads
2. declare that your block is using the new macros in https://git.axelera.ai/prod/europa/-/blob/main/hw/ip/tech_cell_library/default/data/axe_tcl_config.yml?ref_type=heads
3. add to the sf5a modules, depending on type in:
  - ram 1rwp: https://git.axelera.ai/prod/europa/-/blob/main/hw/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_ram_1rwp.sv?ref_type=heads
  - ram 1rp 1wp: https://git.axelera.ai/prod/europa/-/blob/main/hw/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_ram_1rp_1wp.sv?ref_type=heads
  - rom: https://git.axelera.ai/prod/europa/-/blob/main/hw/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_rom_1p.sv?ref_type=heads

## Step 3

We instantiate the respective `axe_tcl_ram_*` module.

!!! note "Implementation specific Sideband Signals"

    Each technology is different in terms of sidebands signals to the macros. To make sure your IP is truly reusable,
    **propagate** the memory sideband types from the top of the IP. In a concrete implementation they can be fixed.


For the implementation specific parameters, define on all hierarchies of the IP from the top level to the macro instantiation something on the lines of:

```verilog
  /// Memory Implementation Key
  parameter MemImplKey = "default",
  /// Sideband input signal type to axe_tcl_ram
  parameter type ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from  to axe_tcl_ram
  parameter type ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t,
```

The respective sideband ports should then be defines on your port list like:

```verilog
  /////////////////////////////
  // Memory Sideband Signals //
  /////////////////////////////
  /// Memory sideband input signals
  input  ram_impl_inp_t i_ram_impl,
  /// Memory sideband output signals
  output ram_impl_oup_t o_ram_impl,
```

!!! note "Multiple memories in an IP"

    If there are multiple memories in your IP, consider of defining different types per functionally different memory.
    If the memories are banked by your IP, but will be the same, then use [axe_tcl_sram_cfg](https://git.axelera.ai/prod/europa/-/blob/main/hw/ip/tech_cell_library/default/rtl/functional/axe_tcl_sram_cfg.sv)
    to split the implementation sideband signals.
