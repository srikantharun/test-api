// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Simple AXIS driver
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _AXIS_DRIVER_SV_
`define _AXIS_DRIVER_SV_

`include "axis_intf.sv"

typedef struct packed {
  logic [512-1:0] data;
  logic [512/8-1:0] strb;
  logic last;
} t_axis_token;

class axis_driver;
  virtual axis_intf axis_if;
  bit master = 0;

  int perc_stall_rdy = 0;

  mailbox axis_in, axis_out;

  function new(virtual axis_intf axis_if, bit master);
    //getting the interface
    this.axis_if = axis_if;
    this.master  = master;  // if master or slave
  endfunction

  task reset_check;
    forever
      @(posedge axis_if.clk, negedge axis_if.rst_n) begin
        if (axis_if.rst_n == 0) begin
          if (this.master) axis_if.mt_cb.vld <= 0;
          else axis_if.sl_cb.rdy <= 0;
        end else begin
          if (!this.master) begin
            axis_if.sl_cb.rdy <= ($urandom_range(0, 100) < perc_stall_rdy) ? 0 : 1;
          end
        end
      end
  endtask

  task write(input t_axis_token axis);
    axis_if.mt_cb.vld  <= 1;
    axis_if.mt_cb.data <= axis.data;
    axis_if.mt_cb.strb <= axis.strb;
    axis_if.mt_cb.last <= axis.last;
    @(posedge axis_if.clk iff axis_if.rdy);
    axis_if.mt_cb.vld <= 0;
  endtask

  task read(output t_axis_token axis);
    @(axis_if.sl_cb iff (axis_if.rdy && axis_if.sl_cb.vld));
    axis.data = axis_if.sl_cb.data;
    axis.strb = axis_if.sl_cb.strb;
    axis.last = axis_if.sl_cb.last;
  endtask

  task chk_write();
    t_axis_token axis;
    forever begin
      axis_out.get(axis);
      write(axis);
    end
  endtask

  task chk_read();
    t_axis_token axis;
    forever begin
      read(axis);
      axis_in.put(axis);
    end
  endtask

  task run;
    fork
      reset_check;
      if (master) chk_write;
      if (!master) chk_read;
    join_none
  endtask
endclass

`endif  //_DPCMD_DRIVER_SV_
