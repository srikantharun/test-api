package tb_axi_pkg;

typedef struct {
  int req_time;
  int id;
  int addr;
  int len;
  bit [3:0] size;
  bit [1:0] burst;
} t_req;

`include "axi_mt_driver.sv"
`include "axi_sl_driver.sv"
`include "axi_cmdblock_driver.sv"

endpackage
