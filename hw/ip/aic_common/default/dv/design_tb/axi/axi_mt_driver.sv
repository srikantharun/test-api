// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple AXI master driver, respond with random data
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _I_AXI_MT_DRIVER_SV_
`define _I_AXI_MT_DRIVER_SV_

class axi_mt_driver #(
  parameter DW = 512,
  parameter AW = 36,
  parameter IDW = 9
);
  string name;
  virtual axi_intf #(.DW(DW), .AW(AW), .IDW(IDW)) axi_if;
  int dw = 64;

  int cur_cnt = 0;
  logic rresp_busy;
  logic wresp_busy;
  logic rd_busy;
  logic wr_busy;
  logic wd_busy;

  mailbox mail_write_req = new();
  mailbox mail_read_req = new();
  mailbox mail_wresp_req = new();
  mailbox mail_write_data = new();
  mailbox mail_read_data[int];

  function new(string name, virtual axi_intf #(.DW(DW), .AW(AW), .IDW(IDW)) axi_if, int dw = 64);
    //getting the interface
    this.name = name;
    this.axi_if = axi_if;
    this.dw = dw;

    $display("AXI Master driver \"%s\" created.", this.name);
  endfunction

  function is_busy();
    return write_busy() | read_busy();
  endfunction

  function write_busy();
    return ((write_req_busy() + wresp_busy) > 0);
  endfunction

  function write_req_busy();
    return ((mail_write_req.num() + wr_busy + wd_busy) > 0);
  endfunction

  function read_busy();
    return ((mail_read_req.num() + rresp_busy + rd_busy) > 0);
  endfunction

  virtual function void set_wdata(t_req wr_req);
    logic [DW-1:0] rand_wdata;

    if (!mail_write_data.try_get(rand_wdata)) void'(std::randomize(rand_wdata));
    // shift based on address:
    axi_if.mt_cb.wdata <= rand_wdata << 8 * (wr_req.addr % (this.dw / 8));
  endfunction

  task push_write_data(logic [$bits(axi_if.mt_cb.wdata)-1:0] wdata);
    mail_write_data.put(wdata);
  endtask

  task get_read_data(output logic [$bits(axi_if.mt_cb.rdata)-1:0] rdata,
                     input integer id = 0);
    if (!mail_read_data[id]) mail_read_data[id] = new();
    mail_read_data[id].get(rdata);
  endtask

  virtual function void set_wstrb(t_req wr_req);
    logic [(DW/8)-1:0] wstrb;

    // get base strb:
    wstrb = ((1 << (2 ** wr_req.size)) - 1);

    // shift based on address:
    axi_if.mt_cb.wstrb <= wstrb << wr_req.addr % (this.dw / 8);
  endfunction

  task reset_and_cnt_check;
    forever
      @(posedge axi_if.clk, negedge axi_if.rst_n) begin
        if (axi_if.rst_n == 0) begin
          axi_if.mt_cb.awid    <= 0;
          axi_if.mt_cb.awaddr  <= 0;
          axi_if.mt_cb.awlen   <= 0;
          axi_if.mt_cb.awsize  <= 0;
          axi_if.mt_cb.awburst <= 0;
          axi_if.mt_cb.awlock  <= 0;
          axi_if.mt_cb.awcache <= 0;
          axi_if.mt_cb.awprot  <= 0;
          axi_if.mt_cb.awvalid <= 0;

          axi_if.mt_cb.arid    <= 0;
          axi_if.mt_cb.araddr  <= 0;
          axi_if.mt_cb.arlen   <= 0;
          axi_if.mt_cb.arsize  <= 0;
          axi_if.mt_cb.arburst <= 0;
          axi_if.mt_cb.arlock  <= 0;
          axi_if.mt_cb.arcache <= 0;
          axi_if.mt_cb.arprot  <= 0;
          axi_if.mt_cb.arvalid <= 0;

          axi_if.mt_cb.wdata   <= 0;
          axi_if.mt_cb.wstrb   <= 0;
          axi_if.mt_cb.wlast   <= 0;
          axi_if.mt_cb.wvalid  <= 0;

          axi_if.mt_cb.rready  <= 0;
          axi_if.mt_cb.bready  <= 0;

          cur_cnt              <= 0;
        end else begin
          cur_cnt <= cur_cnt + 1;
        end
      end
  endtask

  task ready_drive_handle;
    forever
      @(axi_if.mt_cb, negedge axi_if.rst_n) begin
        if (axi_if.rst_n == 0) begin
          axi_if.mt_cb.rready <= 1;
          axi_if.mt_cb.bready <= 1;
        end else begin
          axi_if.mt_cb.rready <= ($urandom_range(0, 10) < 2) ? 0 : 1;
          axi_if.mt_cb.bready <= ($urandom_range(0, 10) < 4) ? 0 : 1;
        end
      end
  endtask

  task write(t_req write_req);
    // $display("%s: Got write request %p @ %0t", this.name, write_req, $time());
    wr_busy = 1;
    axi_if.mt_cb.awvalid <= 1'b1;
    axi_if.mt_cb.awid    <= write_req.id;
    axi_if.mt_cb.awaddr  <= write_req.addr;
    axi_if.mt_cb.awlen   <= write_req.len;
    axi_if.mt_cb.awsize  <= write_req.size;
    axi_if.mt_cb.awburst <= write_req.burst;

    @(axi_if.mt_cb iff (axi_if.mt_cb.awvalid && axi_if.mt_cb.awready));  // valid write req
    axi_if.mt_cb.awvalid <= 1'b0;
    // $display("%s: Write request send! %p @ %0t", this.name, write_req, $time());
    mail_write_req.put(write_req);
    wr_busy = 0;
  endtask

  task read(t_req read_req);
    rd_busy = 1;
    axi_if.mt_cb.arvalid <= 1'b1;
    axi_if.mt_cb.arid    <= read_req.id;
    axi_if.mt_cb.araddr  <= read_req.addr;
    axi_if.mt_cb.arlen   <= read_req.len;
    axi_if.mt_cb.arsize  <= read_req.size;
    axi_if.mt_cb.arburst <= read_req.burst;

    @(axi_if.mt_cb iff (axi_if.mt_cb.arvalid && axi_if.mt_cb.arready));  // valid read req
    axi_if.mt_cb.arvalid <= 1'b0;
    // $display("%s: Read request send! %p @ %0t", this.name, read_req, $time());
    mail_read_req.put(read_req);
    rd_busy = 0;
  endtask

  task automatic rnd_wait(int min_cycles, int max_cycles);
    logic [4:0] wait_cycles;
    void'(std::randomize(
        wait_cycles
    ) with {
      wait_cycles dist {
        min_cycles :/ 2,
        [min_cycles + 1 : max_cycles] :/ 2
      };
    });
    repeat (wait_cycles) @(posedge axi_if.clk);
  endtask

  task write_snd_handle;
    t_req write_req;
    t_req wresp_req;
    forever begin
      // $display("%s: Wait for write request in mailbox (%0d items)", this.name, mail_write_req.num());
      mail_write_req.get(write_req);
      wd_busy = 1;
      // $display("%s: Got write request %p @ %0t", this.name, write_req, $time());

      //rnd_wait(0, 4);
      for (int item = 0; item <= write_req.len; item++) begin
        axi_if.mt_cb.wvalid <= 1'b1;
        set_wdata(write_req);
        set_wstrb(write_req);
        axi_if.mt_cb.wlast <= (item == write_req.len) ? 'b1 : 'b0;
        // increment addr with size sent. This is mainly used for the data and strb alignment:
        write_req.addr += (2 ** write_req.size);
        @(axi_if.mt_cb iff (axi_if.mt_cb.wvalid && axi_if.mt_cb.wready));
        // axi_if.mt_cb.wdata <= get_wdata(write_req.addr);
      end
      axi_if.mt_cb.wvalid <= 1'b0;
      wresp_req.id = write_req.id;
      wresp_req.req_time = cur_cnt;
      // $display("%s: Put wresp req @ %0t", this.name, $time());
      mail_wresp_req.put(wresp_req);
      wd_busy = 0;
    end
  endtask

  task read_resp_handle;
    t_req   read_req;
    integer item;
    forever begin
      // $display("%s: Wait for read request in mailbox", this.name);
      if (mail_read_req.try_get(read_req)) begin
        // $display("%s: Got a read request! %p @ %0t", this.name, read_req, $time());

        rresp_busy = 1;
        for (item = 0; item <= read_req.len; item++) begin
          logic exp_last = (item == read_req.len) ? 'b1 : 'b0;
          @(axi_if.mt_cb iff (axi_if.mt_cb.rready && axi_if.mt_cb.rvalid));
          // $display("%s: Got read response!! @ %0t", this.name, $time());
          if (axi_if.mt_cb.rlast != exp_last)
            $error("%s: Unexpected last from read response (%0d instead of %0d)... @ %0t",
                   this.name, axi_if.mt_cb.rlast, exp_last, $time());
          //   if (axi_if.mt_cb.rid != read_req.id)
          //     $error("%s: Unexpected ID from read response (%0d instead of %0d)... @ %0t", this.name,
          //            axi_if.mt_cb.rid, read_req.id, $time());
          if (!mail_read_data[axi_if.mt_cb.rid]) mail_read_data[axi_if.mt_cb.rid] = new();
          // shift data if address requires this (subword read):
          mail_read_data[axi_if.mt_cb.rid].put(
              axi_if.mt_cb.rdata >> 8 * (read_req.addr % (this.dw / 8)));
          read_req.addr += (2 ** read_req.size);
        end
        rresp_busy = 0;
      end else begin
        @(axi_if.mt_cb);
        if (axi_if.mt_cb.rvalid && axi_if.mt_cb.rready)
          $error("%s: Received read data beat, but didn't expect one!... @ %0t", this.name,
                 $time());
      end
    end
  endtask

  task wresp_handle;
    t_req wresp_req;
    forever begin
      // $display("%s: Wait for wresp request in mailbox", this.name);
      if (mail_wresp_req.try_get(wresp_req)) begin
        // $display("%s: Got a wresp request! %p @ %0t", this.name, wresp_req, $time());
        wresp_busy = 1;

        @(axi_if.mt_cb iff (axi_if.mt_cb.bvalid && axi_if.mt_cb.bready));  // wait for resp
        // $display("%s: Wresp received! @ %0t", this.name, $time());

        // if (axi_if.mt_cb.bid != wresp_req.id)
        //   $error("%s: Unexpected ID from write response (%0d instead of %0d)... @ %0t", this.name,
        //          axi_if.mt_cb.bid, wresp_req.id, $time());
        wresp_busy = 0;
      end else begin
        @(axi_if.mt_cb);
        if (axi_if.mt_cb.bvalid && axi_if.mt_cb.bready)
          $error("%s: Received write response beat, but didn't expect one!... @ %0t", this.name,
                 $time());
      end
    end
  endtask

  virtual task run;
    rd_busy = 0;
    wr_busy = 0;
    rresp_busy = 0;
    wresp_busy = 0;
    wd_busy = 0;
    fork
      reset_and_cnt_check;
      ready_drive_handle;
      read_resp_handle;
      write_snd_handle;
      wresp_handle;
    join_none
  endtask
endclass

`endif  //_I_AXI_MT_DRIVER_SV_
