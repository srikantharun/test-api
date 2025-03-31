`ifndef SPIKE_DPI_MACROS_SVH
`define SPIKE_DPI_MACROS_SVH

`define SPIKE_DPI_TASK_READ(periph_name) \
  export "DPI-C" task ``periph_name``_read; \
  task automatic ``periph_name``_read(input bit [31:0] addr, \
                                      output bit [63:0] data, \
                                      input int len, \
                                      output byte resp)

`define SPIKE_DPI_TASK_WRITE(periph_name) \
  export "DPI-C" task ``periph_name``_write; \
  task automatic ``periph_name``_write(input bit [31:0] addr, \
                                      input bit [63:0] data, \
                                      input int len, \
                                      output byte resp)

`endif  // SPIKE_DPI_MACROS_SVH
