// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_NOC_MEM_DRV
`define GUARD_NOC_MEM_DRV

class noc_mem_drv extends uvm_driver#(noc_mem_item);

  virtual noc_mem_rd_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))) rd_vif;
  virtual noc_mem_wr_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))) wr_vif;

  noc_mem_env_cfg                  m_env_cfg;
  noc_mem_item                     item;

  logic [`DATAW-1:0]               m_mem[int unsigned];

  uvm_analysis_port#(noc_mem_item) ap;

  `uvm_component_utils(noc_mem_drv)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    assert(uvm_config_db#(noc_mem_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));
    assert(uvm_config_db #(virtual noc_mem_rd_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::get(this, "", "rd_vif",  rd_vif));
    assert(uvm_config_db #(virtual noc_mem_wr_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::get(this, "", "wr_vif",  wr_vif));
    ap = new("ap", this);
  endfunction

  virtual task reset_phase (uvm_phase phase);
    reset();
  endtask : reset_phase

  virtual function void process_item(noc_mem_item t);

    if (t.rd_en) begin
      if (!m_mem.exists(t.rd_addr))
        m_mem[t.rd_addr] = '0;

      t.rd_data = m_mem[t.rd_addr];
    end

    if (t.wr_en) begin
      if (!m_mem.exists(t.wr_addr))
        m_mem[t.wr_addr] = '0;

      m_mem[t.wr_addr] &= ~(t.wr_ben);
      m_mem[t.wr_addr] |= (t.wr_ben & t.wr_data);
    end

    if (t.wr_en || t.rd_en)
      ap.write(t);
  endfunction : process_item

  virtual task reset();
    rd_vif.en   <= 1'b0;
    rd_vif.addr <= '0;

    wr_vif.en   <= 1'b0;
    wr_vif.addr <= '0;
    wr_vif.data <= '0;
    wr_vif.ben  <= '0;
  endtask : reset


  virtual task run_phase(uvm_phase phase);
    this.m_env_cfg.print();
    reset();

    @(posedge rd_vif.clk iff rd_vif.rst_n);

    fork
      forever begin
        seq_item_port.get_next_item(req);

        // Send to ap as base class (required for comparision)
        item = new("from_driver");
        item.copy(req);
        process_item(item);

        rd_vif.en   <= req.rd_en;
        rd_vif.addr <= req.rd_addr;

        wr_vif.en   <= req.wr_en;
        wr_vif.addr <= req.wr_addr;
        wr_vif.data <= req.wr_data;
        wr_vif.ben  <= req.wr_ben;

        @(posedge rd_vif.clk iff rd_vif.rst_n);

        reset();
        seq_item_port.item_done();
      end
    join
  endtask
endclass

`endif // GUARD_NOC_MEM_DRV

