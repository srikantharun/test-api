// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description : IRQ (UVM) Monitor
// Owner       : Sultan Khan

`ifndef __IRQ_MONITOR_SV__
`define __IRQ_MONITOR_SV__

class irq_monitor extends uvm_monitor;
    `uvm_component_utils(irq_monitor)

    uvm_analysis_port#(irq_seq_item)  ap;
    virtual irq_if                    vif;

    //==========================================================================
    function new(string name = "irq_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap",this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    //==========================================================================
    task automatic monitor_irq(int idx);
      irq_seq_item    item;
      bit             send_msg;
      logic           prev_irq;
      logic           curr_irq;

      item = irq_seq_item::type_id::create("item");

      forever
      begin
          
        vif.wait_n_clks(1);
        
        curr_irq = vif.get_irq_state(idx);
        case ({prev_irq, curr_irq})
            2'b01:  begin    send_msg = 1;    item.change = IRQ_JUST_RAISED;    item.irq_line_state[idx] = 1'b1;  end
            2'b10:  begin    send_msg = 1;    item.change = IRQ_JUST_CLEARED;   item.irq_line_state[idx] = 1'b0;  end
            2'b11:  begin    send_msg = 1;    item.change = IRQ_REMAINS_HIGH;   item.irq_line_state[idx] = 1'b1;  end
            
            default:  // Avoid Sending any Messages when IRQ remains LOW (as that is the default state)
                    begin    send_msg = 0;    end
        endcase
        if (send_msg)
        begin
            `uvm_info("IRQ_MONITOR", $sformatf("Sending %s to analysis port for IRQ[%0d][irq_line_state=%4b]", item.change.name(), idx, item.irq_line_state), UVM_LOW)
            void'(item.begin_tr());
            item.end_tr();
            ap.write(item);
        end
        prev_irq = curr_irq;
      end
    endtask
    
    //==========================================================================
    task run_phase(uvm_phase phase);
      for (int i=0; i < NUM_IRQ_LINES; i++) begin
        automatic int idx;
        idx = i;
        
        fork
          monitor_irq(idx);
        join_none
      end
    endtask

endclass : irq_monitor

`endif // __IRQ_MONITOR_SV__
