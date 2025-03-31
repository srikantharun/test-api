# Spike RISCV model for simulation

This directory contains the necessary functions and compilation options to add the spike, a RISCV processor model, to any simulation testbench.
This enables us to write C tests to drive the RTL, without the cost of integrating an actual CPU to the testbench. Communication from C to RTL is achieved through DPI calls.

## How to use

### DPI functions export

To enable the spike to make accesses to peripherals, you need to create and export systemverilog tasks for read and write operations.


```systemverilog
// Export tasks
export "DPI-C" task periph_write;
export "DPI-C" task periph_read;


// Declare tasks
task automatic periph_write(input bit [31:0] addr, input bit [63:0] data, input int len,
                            output byte resp);
// ...
endtask

task automatic periph_read(input bit [31:0] addr, output bit [63:0] data, input int len,
                           output byte resp);
// ...
endtask
```

Exported tasks must have the signature presented above, in order to match what is expected on the C side.

Macros are provided in [sv/spike_dpi_macros.svh](./sv/spike_dpi_macros.svh) to declare and export tasks in one go. The example above becomes:

```systemverilog
`include "spike_dpi_macros.svh"


`SPIKE_DPI_TASK_READ(periph);
// ...
endtask

`SPIKE_DPI_TASK_WRITE(periph);
// ...
endtask
```

### Spike instantiation and compilation

Copy [spike_main_template.cpp](./spike_main_template.cpp) to your test directory and edit the `TODO` parts.

```bash
cp spike_main_template.cpp /path/to/your/tb/spike_main.cpp
```

In you sim directoy, create a symlink to [spike_compile.mk](./spike_compile.mk):

```bash
ln -s ../relative/path/to/hw/dv/spike_spi/spike_compile.mk spike_compile.mk
```

Include it in `simulation_config.mk` and add `spike_main.cpp` to the SPI sources:

```make
include spike_dpi.mk

DPI_C_SRC += ../path/to/spike_main.cpp
```

### Starting the spike from a simulation

Function `spike_main` in `spike_main.cpp` is the entry point to starting the spike. To call it from the UVM, import it and call it from your code:

```systemverilog

import "DPI-C" context task spike_main(input string elf);

// ...

task my_test::run_phase(uvm_phase phase);
  byte exit_code;
  phase.raise_objection(this);

  // Optional: wait for memories to be preloaded
  wait_for_spm_preload();

  spike_main(m_config.m_elf, exit_code);

  if (exit_code != 0) begin
    `uvm_error(get_type_name(), $sformatf("Program exited with error code: %0d!", exit_code))
  end

  phase.drop_objection(this);
endtask : run_phase
```

#### UVM SW IPC

TODO
