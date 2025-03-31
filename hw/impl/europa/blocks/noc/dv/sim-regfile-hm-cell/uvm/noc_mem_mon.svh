// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_NOC_MEM_MON_SVH
`define GUARD_NOC_MEM_MON_SVH

class noc_mem_mon extends uvm_monitor;

  noc_mem_env_cfg                                                m_env_cfg;
  virtual noc_mem_rd_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))) rd_vif;
  virtual noc_mem_wr_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))) wr_vif;

  `uvm_component_utils(noc_mem_mon)

  uvm_analysis_port#(noc_mem_item) ap;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    assert(uvm_config_db#(noc_mem_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));
    assert(uvm_config_db #(virtual noc_mem_rd_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::get(this, "", "rd_vif",  rd_vif));
    assert(uvm_config_db #(virtual noc_mem_wr_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::get(this, "", "wr_vif",  wr_vif));
    ap = new("ap", this);
  endfunction : build_phase

  virtual task monitor_reset(uvm_phase phase);
    @(negedge rd_vif.rst_n);
    `uvm_info(get_full_name(), $sformatf("Reset was seen on the interface and monitor will be reset"), UVM_LOW)

    @(posedge rd_vif.rst_n);
    `uvm_info(get_full_name(), $sformatf("Reset done!"), UVM_LOW)
  endtask : monitor_reset

  virtual task monitor(uvm_phase phase);
    forever begin
      @(posedge rd_vif.clk iff rd_vif.rst_n);

      if (rd_vif.en || wr_vif.en) begin
        noc_mem_item item;

        item          = new("from_monitor");
        item.wr_en    = wr_vif.en;
        item.wr_addr  = wr_vif.addr;
        item.wr_data  = wr_vif.data;
        item.wr_ben   = wr_vif.ben;

        item.rd_en    = rd_vif.en;
        item.rd_addr  = rd_vif.addr;

        item.begin_tr();

        fork begin
          automatic noc_mem_item _item = item;
          @(posedge rd_vif.clk iff rd_vif.rst_n);
          _item.rd_data = rd_vif.data;
          _item.end_tr();
          ap.write(_item);
        end
        join_none
      end
    end
  endtask : monitor

  virtual task run_phase(uvm_phase phase);
    fork
      monitor_reset(phase);
      monitor(phase);
    join_none

    wait fork;
  endtask : run_phase
endclass : noc_mem_mon

`endif // GUARD_NOC_MEM_MON_SVH
