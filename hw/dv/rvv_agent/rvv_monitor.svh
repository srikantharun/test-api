`ifndef RVV_MONITOR_SV
`define RVV_MONITOR_SV

// RVV monitor - this is just a placeholder for future needs. RVV monitor isn't really needed, as RVV is just an umbrellad for several MMIO ports. They are independent of each other, and their respective req/resp are happening inside mmio monitor.
class rvv_monitor#(int DATA_WIDTH = 128, int ADDR_WIDTH = 22) extends uvm_monitor;
  `uvm_component_param_utils(rvv_monitor#(DATA_WIDTH, ADDR_WIDTH))

  typedef mmio_item#(DATA_WIDTH, ADDR_WIDTH) mmio_item_t;
  rvv_config                                m_rvv_cfg;
  // Virtual interface array
  virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH)  m_mmio_vif[];

  uvm_analysis_port#(mmio_item_t) ap;
  mmio_item_t m_req_q[$];

  function new (string name, uvm_component parent);
      super.new (name, parent);
  endfunction

  // virtual function void build_phase(uvm_phase phase);
  //   super.build_phase(phase);
    
  //   ap = new("ap", this);
  //   if ( ! uvm_config_db#( rvv_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "m_rvv_cfg" ), .value( m_rvv_cfg ) ) ) begin
  //     `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
  //   end
  //   m_mmio_vif = new[m_rvv_cfg.connections_num];
  // endfunction

  // virtual task run_phase(uvm_phase phase);
  //   mmio_item_t req_item;

  //   super.run_phase(phase);
  //   forever begin
  //     @(posedge m_mmio_vif[0].rst);
  //     m_req_q.delete();
  //     `uvm_info(get_name(), "Reset Done!", UVM_LOW)
  //     forever @(m_mmio_vif[0].mon) begin
  //       for (int i = 0; i < m_mmio_vif.size(); i++) begin
  //         if (m_mmio_vif[i].mon.req.valid) begin
  //           // Create a new transaction item
  //           req_item = mmio_item_t::type_id::create("rsp_item");
  //           if (m_mmio_vif[i].mon.rsp.ready === 1'b1) begin
  //             req_item = mmio_item_t::type_id::create("req_item", this);
  //             req_item.m_addr = m_mmio_vif[i].mon.req.addr;
  //             if (m_mmio_vif[i].mon.req.we === 1'b1) begin
  //               req_item.m_we = 1;
  //               req_item.m_wdata = m_mmio_vif[i].mon.req.data;
  //               `uvm_info(get_name(), $sformatf("Write transaction: address = 0x%0h, data = 0x%0h", req_item.m_addr, req_item.m_wdata), UVM_MEDIUM)
  //             end else begin
  //               req_item.m_we = 0;
  //               `uvm_info(get_name(), $sformatf("Read transaction: address = 0x%0h", req_item.m_addr), UVM_MEDIUM)
  //             end
  //             req_item.m_type  = MMIO_REQ;
  //             ap.write(req_item);
  //             m_req_q.push_back(req_item);
  //           end
  //         end
  //       end
  //     end
  //   end
  // endtask : run_phase
endclass : rvv_monitor
`endif // RVV_MONITOR_SV

