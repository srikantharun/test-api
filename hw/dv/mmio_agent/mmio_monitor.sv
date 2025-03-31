`ifndef MMIO_MONITOR_SV
`define MMIO_MONITOR_SV

// Monitors mmio req/resp transactions. makes sure that every req has a resp, and every resp comes after a req.
class mmio_monitor#(int DATA_WIDTH = 512, int ADDR_WIDTH = 22) extends uvm_monitor;
  `uvm_component_param_utils(mmio_monitor#(DATA_WIDTH, ADDR_WIDTH))
  
  typedef mmio_item#(DATA_WIDTH, ADDR_WIDTH) mmio_item_t;

  mmio_config m_cfg;
  virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH) m_vif;

  uvm_analysis_port#(mmio_item_t) ap;
  uvm_analysis_port#(mmio_item_t) scb_ap;

  mmio_item_t m_req_q[$];
  int unsigned m_req_vld_to_rdy_timeout_count;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    scb_ap = new("scb_ap", this);

    if ( ! uvm_config_db#( mmio_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "m_cfg" ), .value( m_cfg ) ) ) begin
      `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
    end
  endfunction : build_phase

  virtual task monitor_req();
    mmio_item_t req_item;
    int timeout_cycles;
    forever begin
      @(m_vif.mon);
      if (m_vif.mon.req.valid === 1'b1) begin
        timeout_cycles = m_cfg.m_int_req_vld_to_rdy_timeout_cycles;
        if (m_vif.mon.rsp.ready === 1'b1) begin
          req_item = mmio_item_t::type_id::create("req_item", this);
          req_item.m_addr = m_vif.mon.req.addr;
          if (m_vif.mon.req.we === 1'b1) begin
            req_item.m_we = 1;
            req_item.m_wdata = m_vif.mon.req.data;
          end else begin
            req_item.m_we = 0;
          end
          req_item.m_type  = MMIO_REQ;
          ap.write(req_item);
          m_req_q.push_back(req_item);
          m_req_vld_to_rdy_timeout_count = 0;
        end
        m_req_vld_to_rdy_timeout_count += 1;
      end
    end
  endtask : monitor_req

  virtual task monitor_rsp();
    mmio_item_t rsp_item;
    mmio_item_t txn_item;
    bit check_rsp_ready;
    forever begin
      @(m_vif.mon);
      if (m_vif.mon.rsp.ack === 1'b1 && (m_cfg.m_has_scoreboard == 1'b1 || m_vif.mon.req.rsp_ready === 1'b1)) begin  // in case of rvv (that's when ascoreboard is on), rsp_ready is not in use, so well make it 1.
        rsp_item = mmio_item_t::type_id::create("rsp_item");
        rsp_item.m_rdata = m_vif.mon.rsp.data; // sample regardless of the txn direction
        rsp_item.m_error = m_vif.mon.rsp.error;
        rsp_item.m_type  = MMIO_RSP;
        if (m_req_q.size() == 0) begin
          `uvm_error(get_name() , $sformatf("MMIO Response Without Request! %s", rsp_item.convert2string()))
        end else begin
          // send only valid responses
          txn_item = m_req_q.pop_front();
          txn_item.m_rdata = rsp_item.m_rdata;
          txn_item.m_error = rsp_item.m_error;
          txn_item.m_type  = MMIO_TXN;
          ap.write(rsp_item);
          ap.write(txn_item);
          scb_ap.write(txn_item);
          `uvm_info(get_name(), $sformatf("MMIO Transaction! %s", txn_item.convert2string()), UVM_HIGH)
        end
      end
    end
  endtask : monitor_rsp

  virtual task run_phase(uvm_phase phase);
    bit init_done;
    super.run_phase(phase);
    forever begin
      @ (posedge m_vif.rst);
      m_req_q.delete();
      `uvm_info(get_name(), "Reset Done!", UVM_MEDIUM)
      fork
        begin
          fork
            monitor_req();
            monitor_rsp();
          join
        end
        begin
          @ (negedge m_vif.rst);
          `uvm_info(get_name(), "Reset Detected!", UVM_MEDIUM)
        end
      join_any
      disable fork;
    end
  endtask : run_phase

  // added check phase to make sure that arent any requests left unanswered (needed for rvv. in dmc axi will make sure of that)
  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (m_req_q.size() != 0 ) begin
      `uvm_error(get_name() , $sformatf("MMIO Requests queue size should be 0, but it is %0d instead!", m_req_q.size()))
    end
  endfunction: check_phase
endclass : mmio_monitor
`endif // TOKEN_AGENT_MONITOR_SV
