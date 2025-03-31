// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple AXI slave driver, respond with random data
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _I_AXI_SL_DRIVER_SV_
`define _I_AXI_SL_DRIVER_SV_

`define RD_RESP_DELAY 16
`define WR_RESP_DELAY 16

class axi_sl_driver #(
  parameter DW = 512,
  parameter AW = 36,
  parameter IDW = 9
);
  virtual axi_intf #(.DW(DW), .AW(AW), .IDW(IDW)) axi_if;
  string name;
  int cur_cnt = 0;

  logic block_wr_data;

  mailbox mail_write_req = new();
  mailbox mail_read_req = new();
  mailbox mail_write_data = new();
  mailbox mail_wresp_req = new();

  logic [DW-1:0] mem[longint];
  logic mem_set[longint];

  typedef struct {
    int req_time;
    int id;
    longint addr;
    int len;
    logic write;
    int size;
    int burst;
  } t_req;

  typedef struct {
    logic [DW-1:0] data;
    logic [DW/8-1:0] strb;
    logic last;
  } t_data;

  function new(string name, virtual axi_intf #(.DW(DW), .AW(AW), .IDW(IDW)) axi_if);
    //getting the interface
    this.name   = name;
    this.axi_if = axi_if;

    $display("AXI Slave driver \"%s\" created.", this.name);
  endfunction
  ;

  virtual function logic [DW-1:0] get_rdata(longint addr);
    logic [DW-1:0] rand_rdata;
    if (mem_set.exists(addr)) rand_rdata = mem[addr];
    else begin
      void'(std::randomize(rand_rdata));
      mem_set[addr] = 1;
      mem[addr] = rand_rdata;
    end

    return rand_rdata;
  endfunction

  virtual function void set_wdata(longint addr, logic [DW-1:0] wdata, logic [DW/8-1:0] wstrb = '1);
    mem_set[addr] = 1;
    mem[addr] = wdata;
  endfunction

  task reset_and_cnt_check;
    forever
      @(posedge axi_if.clk, negedge axi_if.rst_n) begin
        if (axi_if.rst_n == 0) begin
          // mail_write_req = new();
          // mail_read_req = new();

          axi_if.sl_cb.rid <= 0;
          axi_if.sl_cb.rdata <= 0;
          axi_if.sl_cb.rresp <= 0;
          axi_if.sl_cb.rlast <= 0;
          axi_if.sl_cb.rvalid <= 0;

          axi_if.sl_cb.bid <= 0;
          axi_if.sl_cb.bresp <= 0;
          axi_if.sl_cb.bvalid <= 0;
          cur_cnt <= 0;
        end else begin
          cur_cnt <= cur_cnt + 1;
        end
      end
  endtask

  task ready_drive_handle;
    forever
      @(axi_if.sl_cb, negedge axi_if.rst_n) begin
        if (axi_if.rst_n == 0) begin
          axi_if.sl_cb.awready <= 1;
          axi_if.sl_cb.arready <= 1;
          axi_if.sl_cb.wready  <= 1;
        end else begin
          axi_if.sl_cb.awready <= ($urandom_range(0, 10) < 3) ? 0 : 1;
          axi_if.sl_cb.arready <= ($urandom_range(0, 10) < 3) ? 0 : 1;
          axi_if.sl_cb.wready  <= ($urandom_range(0, 10) < 2) ? 0 : 1;
        end
      end
  endtask

  task write_req_handle;
    t_req write_req;
    forever begin
      @(axi_if.sl_cb iff (axi_if.sl_cb.awvalid && axi_if.sl_cb.awready));  // valid write req
      write_req.req_time = cur_cnt;
      write_req.id = axi_if.sl_cb.awid;
      write_req.addr = axi_if.sl_cb.awaddr;
      write_req.write = 1;
      write_req.len = axi_if.sl_cb.awlen;
      write_req.size = axi_if.sl_cb.awlen;
      write_req.burst = axi_if.sl_cb.awburst;
      // $display("%s: Received write request! %p @ %0t", this.name, write_req, $time());
      mail_write_req.put(write_req);
    end
  endtask

  task read_req_handle;
    t_req read_req;
    forever begin
      @(axi_if.sl_cb iff (axi_if.sl_cb.arvalid && axi_if.sl_cb.arready));  // valid read req
      read_req.req_time = cur_cnt;
      read_req.id = axi_if.sl_cb.arid;
      read_req.addr = axi_if.sl_cb.araddr;
      read_req.write = 0;
      read_req.len = axi_if.sl_cb.arlen;
      read_req.size = axi_if.sl_cb.arlen;
      read_req.burst = axi_if.sl_cb.arburst;
      // $display("%s: Received read request! %p @ %0t", this.name, read_req, $time());
      mail_read_req.put(read_req);
    end
  endtask

  task read_resp_handle;
    t_req   read_req;
    integer item;
    forever begin
      // $display("%s: Wait for read request in mailbox", this.name);
      mail_read_req.get(read_req);
      //   $display("%s: Got a read request! %p @ %0t", this.name, read_req, $time());

      while (cur_cnt - read_req.req_time < `RD_RESP_DELAY)
        @(axi_if.sl_cb);  // delay before returning data

      //   $display("%s: Start returning read data... @ %0t", this.name, $time());
      for (item = 0; item <= read_req.len; item++) begin
        axi_if.sl_cb.rlast <= (item == read_req.len) ? 'b1 : 'b0;
        axi_if.sl_cb.rid <= read_req.id;
        axi_if.sl_cb.rdata <= get_rdata(read_req.addr + (item * DW / 8));
        axi_if.sl_cb.rvalid <= 'b1;

        @(posedge axi_if.clk iff axi_if.rready);
      end
      axi_if.sl_cb.rvalid <= 'b0;
    end
  endtask

  task write_handle;
    t_data write_data;
    forever begin
      @(axi_if.sl_cb iff (axi_if.sl_cb.wready && axi_if.sl_cb.wvalid));
      write_data.data = axi_if.sl_cb.wdata;
      write_data.strb = axi_if.sl_cb.wstrb;
      write_data.last = axi_if.sl_cb.wlast;

      // $display("%s: Write received @ %0t", this.name, $time());
      mail_write_data.put(write_data);
    end
  endtask

  task write_rcv_handle;
    t_req   write_req;
    t_data  write_data;
    t_req   wresp_req;
    integer item;
    forever begin
      // $display("%s: Wait for write request in mailbox (%0d items)", this.name, mail_write_req.num());
      mail_write_req.get(write_req);
      // $display("%s: Waiting for write data for %p @ %0t", this.name, write_req, $time());

      item = 0;
      while (item <= write_req.len) begin
        mail_write_data.get(write_data);
        set_wdata(write_req.addr + (item * DW / 8), write_data.data, write_data.strb);
        item++;
        // $display("%s: Write data set (item nr: %0d of %0d) @ %0t", this.name, item, write_req.len, $time());
      end
      wresp_req.id = write_req.id;
      wresp_req.req_time = cur_cnt;
      // $display("%s: Put wresp req @ %0t", this.name, $time());
      mail_wresp_req.put(wresp_req);
    end
  endtask

  task wresp_handle;
    t_req wresp_req;
    forever begin
      // $display("%s: Wait for wresp request in mailbox", this.name);
      while (!mail_wresp_req.try_get(wresp_req)) @(axi_if.sl_cb);

      // $display("%s: Got a wresp request! %p @ %0t", this.name, wresp_req, $time());

      if (cur_cnt - wresp_req.req_time < `WR_RESP_DELAY) begin
        while (cur_cnt - wresp_req.req_time < `WR_RESP_DELAY)
          @(axi_if.sl_cb);  // delay before returning data
      end

      // $display("%s: Send response data... @ %0t", this.name, $time());
      axi_if.sl_cb.bid <= wresp_req.id;
      axi_if.sl_cb.bresp <= '0;  // random read data
      axi_if.sl_cb.bvalid <= 'b1;

      @(axi_if.sl_cb iff (axi_if.sl_cb.bvalid && axi_if.sl_cb.bready));
      axi_if.sl_cb.bvalid <= 'b0;
    end
  endtask

  virtual task run;
    fork
      reset_and_cnt_check;
      ready_drive_handle;
      read_req_handle;
      write_req_handle;
      read_resp_handle;
      write_handle;
      write_rcv_handle;
      wresp_handle;
    join_none
  endtask
endclass

`endif  //_I_AXI_SL_DRIVER_SV_
