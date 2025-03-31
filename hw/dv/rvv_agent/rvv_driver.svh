`ifndef RVV_DRIVER_SV
`define RVV_DRIVER_SV

// RVV Driver
class rvv_driver #(parameter int DATA_WIDTH = 128, parameter int ADDR_WIDTH = 22) extends uvm_driver#(rvv_sequence_item#(DATA_WIDTH, ADDR_WIDTH));
    `uvm_component_param_utils(rvv_driver#(DATA_WIDTH, ADDR_WIDTH))
  
    rvv_config                                m_rvv_cfg;
    // Virtual interface array
    virtual mmio_if#(DATA_WIDTH, ADDR_WIDTH)  m_mmio_vif[];
  
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
  
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
  
      if ( ! uvm_config_db#( rvv_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "m_rvv_cfg" ), .value( m_rvv_cfg ) ) ) begin
        `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
      end
      m_mmio_vif = new[m_rvv_cfg.connections_num];
    endfunction
  
    virtual task run_phase(uvm_phase phase);
      rvv_sequence_item trans;
      int unsigned index;
      int fork_num;
      forever begin
        seq_item_port.get_next_item(trans);
  
        // Padding with 0's just in case
        for (int i = 0; i < m_rvv_cfg.connections_num; i++) begin
          m_mmio_vif[i].req.valid <= 0; // pad with 0
          m_mmio_vif[i].req.addr <= 0;
          m_mmio_vif[i].req.we <= 0;
          m_mmio_vif[i].req.wbe <= 0;
          m_mmio_vif[i].req.data <= 0;
        end
        `uvm_info(get_name(), $sformatf("transaction generated: num_ports = %0d", trans.num_ports), UVM_MEDIUM)
        // we're using a combination of fork and loop to make a fork - join on the valid ports. wait for all rsp.ready signals to go up and only then drive the valid down.
        fork 
          begin : isolating_thread
            foreach (trans.valid_ports[i])  begin
              fork
                int index = trans.valid_ports[i];
                begin
                  `uvm_info(get_name(), $sformatf("transaction details: port = %0d, address = 0x%0h, we = 0x%0h, data = 0x%0h", index, trans.address[index], trans.we[index], trans.data[index]), UVM_MEDIUM)
                  m_mmio_vif[index].req.valid <= 1'b1;
                  m_mmio_vif[index].req.addr <= trans.address[index];
                  m_mmio_vif[index].req.we <= trans.we[index];
                  if (trans.we[index] == 1) begin  // we = 1 means it's a write
                    m_mmio_vif[index].req.wbe <= '1;  // strobe, should be 1's
                    m_mmio_vif[index].req.data <= trans.data[index];
                  end
        
                  //wait for response.ready to set the valid to 0's
                  @(posedge m_mmio_vif[index].clk);
                  while (m_mmio_vif[index].drv.rsp.ready != 1) begin
                    @(posedge m_mmio_vif[index].clk);
                  end
                  `uvm_info(get_name(), $sformatf("got ready signal for %d", index), UVM_HIGH)
        
                  // Clear valid signal
                  m_mmio_vif[index].req.valid <= 0;
                  `uvm_info(get_name(), $sformatf("clearing valid for%d", index), UVM_HIGH)
                end
              join_none;
            end
          wait fork;
          end : isolating_thread
        join
        
        seq_item_port.item_done();
        
      end
    endtask
  endclass

  `endif // RVV_DRIVER_SV
  
