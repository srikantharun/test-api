// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple cmdblock driver, using AXI driver.
// One or more cmdblock drivers can connect to single AXI driver by using the AXI driver semaphores
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _I_AXI_CMDBLOCK_DRIVER_SV_
`define _I_AXI_CMDBLOCK_DRIVER_SV_

class axi_cmdblock_driver #(
  parameter DW = 32,
  parameter AW = 36,
  parameter IDW = 9,
  parameter DYN_CMD_W = 24,
  parameter NR_FORMATS = 1,
  parameter int FORMAT_NR_BYTES[NR_FORMATS] = {(DYN_CMD_W + 64 + 7) / 8}
)  extends axi_mt_driver #(.DW(DW), .AW(AW), .IDW(IDW));

  string name;
  int csr_base[int];
  int cmd_base[int];
  int axi_id[int];

  mailbox mail_payload_check = new();

  function new(string name, virtual axi_intf #(.DW(DW), .AW(AW), .IDW(IDW)) axi_if, int dw = 64);
    // set the interface
    super.new(name, axi_if, dw);

    $display("AXI DPcmd Master driver \"%s\" created.", this.name);
  endfunction

  function set_id(int id, int dev=0);
    axi_id[dev] = id;
    $display("Set ID for dev %0d to %0d", dev, id);
  endfunction

  function set_csr_base(int base, int dev=0);
    csr_base[dev] = base;
    $display("Set CSR base for dev %0d to %0h", dev, base);
  endfunction

  function set_cmd_base(int base, int dev=0);
    cmd_base[dev] = base;
    $display("Set CMD base for dev %0d to %0h", dev, base);
  endfunction

  function set_bases(int csr, int cmd, int dev=0);
    set_csr_base(csr, dev);
    set_cmd_base(cmd, dev);
  endfunction

  function int get_id(int dev=0);
    if (axi_id.exists(dev))
      return axi_id[dev];
    else
      return 0;
  endfunction

  function int get_csr_base(int dev=0);
    if (csr_base.exists(dev))
      return csr_base[dev];
    else
      return 0;
  endfunction

  function int get_cmd_base(int dev=0);
    if (cmd_base.exists(dev))
      return cmd_base[dev];
    else
      return 0;
  endfunction

  task automatic chk_csr_reg(int reg_idx, logic [DW-1:0] exp, logic exp_fail = 0, int dev=0);
    logic [DW-1:0] rddata;
    csr_rd(reg_idx, rddata, dev);
    if (exp_fail) begin
      if (rddata == exp)
        $error(
            "%s: Unexpected read from reg_idx %0d, should have been anything but 0x%0H, but was 0x%H",
            name, reg_idx, exp, rddata);
    end else begin
      if (rddata != exp)
        $error("%s: Unexpected read from reg_idx %0d, should have been 0x%0H, but was 0x%0H", name,
               reg_idx, exp, rddata);
    end
  endtask

  task automatic snd_cmd(int did, int tprod, int tcons, logic [DYN_CMD_W-1:0] payload,
               int cmd_format = 0, int dev=0);
    localparam HEADER_DW = 64;
    localparam ALLIGN_HEADER_DW = ((HEADER_DW + DW - 1) / DW) * DW;
    localparam ALLIGN_DYN_CMD_W = ((DYN_CMD_W + DW - 1) / DW) * DW;
    logic [DW-1:0] axi_d;
    logic [HEADER_DW-1:0] header;
    logic [ALLIGN_DYN_CMD_W-1:0] axi_payload;
    int payload_bytes;
    t_req axi_wr_req;

    if (NR_FORMATS > 1) payload_bytes = FORMAT_NR_BYTES[cmd_format];
    else payload_bytes = ALLIGN_DYN_CMD_W / 8;  // translate bits to bytes

    // $display("ID: %0d, TPROD: %0b, TCONS: %0b, payload %0d", id, tprod, tcons, payload_bytes);
    header = 'h0 | did | (tprod << 16) | (tcons << 32) | (cmd_format << 48);
    // $display("Header: %0h", header);
    axi_payload = 'h0 | payload;

    axi_wr_req.addr = get_cmd_base(dev);
    axi_wr_req.burst = 2'b01;
    axi_wr_req.len = 0;
    axi_wr_req.size = $clog2(DW / 8);
    axi_wr_req.id = get_id(dev);

    axi_if.wr_sema.get();
    // header:
    for (int i = 0; i < (ALLIGN_HEADER_DW / DW); i++) begin
      push_write_data(header >> (i * DW));
      write(axi_wr_req);
    end


    axi_wr_req.len = (payload_bytes / (DW / 8)) - 1;  // burst entire payload
    // payload
    for (int i = 0; i < (payload_bytes / (DW / 8)); i++) begin
      push_write_data(axi_payload >> (i * DW));
    end
    write(axi_wr_req);
    axi_if.wr_sema.put();

    mail_payload_check.put(axi_payload);
  endtask

  task automatic csr_wr(int reg_idx, logic [DW-1:0] data, integer dev = 0);
    t_req axi_wr_req;

    axi_wr_req.addr = (reg_idx * DW / 8) + get_csr_base(dev);
    axi_wr_req.burst = 2'b00;
    axi_wr_req.len = 0;
    axi_wr_req.size = $clog2(DW / 8);
    axi_wr_req.id = get_id(dev);

    axi_if.wr_sema.get();
    push_write_data(data);
    write(axi_wr_req);
    axi_if.wr_sema.put();
  endtask

  task automatic csr_rd(input int reg_idx, output logic [DW-1:0] data, input integer dev = 0);
    t_req axi_rd_req;

    axi_rd_req.addr = 'h0000 + (reg_idx * DW / 8) + this.get_csr_base(dev);
    axi_rd_req.burst = 2'b00;
    axi_rd_req.len = 0;
    axi_rd_req.size = $clog2(DW / 8);
    axi_rd_req.id = get_id(dev);

    axi_if.rd_sema.get();
    read(axi_rd_req);
    get_read_data(data, get_id(dev));
    axi_if.rd_sema.put();
  endtask

endclass

`endif  //_I_AXI_CMDBLOCK_DRIVER_SV_
