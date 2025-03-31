`ifndef RVV_SEQ_ITEM_SV
`define RVV_SEQ_ITEM_SV

// RVV sequence item - defines the data for a sequence - how many ports will be valid, how many will be read/write and so on
class rvv_sequence_item#(int DATA_WIDTH = 128, int ADDR_WIDTH = 22) extends uvm_sequence_item;
    `uvm_object_param_utils(rvv_sequence_item#(DATA_WIDTH, ADDR_WIDTH))
  
    // Parameters for the transaction
    rand bit [ADDR_WIDTH-1:0] address[$]; // Address array for each port
    rand bit [DATA_WIDTH-1:0] data[$];    // Data array for each port
    rand bit we[$];                       // Write enable array for each port
    rand int valid_ports[];                // Valid ports indices array
    rand int unsigned num_ports;          // Number of ports that are valid
  
    // Configuration parameters
    int unsigned connections_num;
    int unsigned address_alignment;
    bit [ADDR_WIDTH-1:0] forced_address; // Address array for each port
  
    function new(string name = "");
      super.new(name);
    endfunction
  
    // Random constraints
    constraint ports_num_c {
      num_ports inside {[1:connections_num]};      // Ensure at least one port is valid
    }

    constraint data_size_c {
      valid_ports.size() == num_ports;
      address.size() == num_ports;
      data.size() == num_ports;
      we.size() == num_ports;
    }

    constraint address_in_l1_c {
      foreach (address[i]) {
        address[i]%address_alignment == 0; // Make sure that randomly generated address can be divided by address size.
      }
    }

    // Constraint for valid ports randomization
    constraint valid_ports_c {
      foreach (valid_ports[i]) {
        valid_ports[i] inside {[0:connections_num-1]};
        unique {valid_ports};
      }
    }

    // If we're trying to force an address, make sure it appears, at least once (and try to make it appear more than once)
    constraint forced_address_c {
      if (forced_address != '0) {
        foreach (address[i]) {
          foreach (valid_ports[j]) {
            if (i == valid_ports[j]) {
              if (j == 0) {
                address[i] == forced_address;
              }
              else if (j < num_ports/2) {
                address[i] dist {forced_address:/50, ['0:'1]:/50};
              }
              else {
                address[i] dist {forced_address:/20, ['0:'1]:/80};
              }
            }
          }
        }
      }
    }

    // make sure that if we have more than 1 request with the same address, both requests are reads. it's the only way to ensure correct ordering (it's also the expected behavior)
    constraint we_on_same_addresses_c {
      foreach (address[i]) {
        foreach (address[j]) {
          if (i!=j && address[i] == address[j]) {
            we[i] == 0;
            we[j] == 0;
          }
        }
      }
    }

    // make sure we only use read during concurrency tests
    constraint we_on_forced_address_c {
      if (forced_address != '0) {
        foreach (address[i]) {
          if (address[i] == forced_address) {
            we[i] == 0;
          }
        }
      }
    }

    constraint c_solver {
      solve num_ports before valid_ports;
      solve valid_ports before address;
      solve address before we;
    }

    virtual function rvv_sequence_item#(DATA_WIDTH, ADDR_WIDTH) do_clone();
      rvv_sequence_item#(DATA_WIDTH, ADDR_WIDTH) l_item;

      if(!$cast(l_item, this.clone()))
        `uvm_fatal(get_full_name(), "Clone failed")
      return l_item;
    endfunction : do_clone
    
    virtual function void do_copy(uvm_object rhs);
      rvv_sequence_item#(DATA_WIDTH, ADDR_WIDTH) seq_rhs;

      if(rhs == null)
        `uvm_fatal(get_full_name(), "do_copy from null ptr");

      if(!$cast(seq_rhs, rhs))
        `uvm_fatal(get_full_name(), "do_copy cast failed");

      super.do_copy(rhs);
      this.address = seq_rhs.address;
      this.data = seq_rhs.data;
      this.we = seq_rhs.we;
      this.num_ports = seq_rhs.num_ports;
      this.connections_num = seq_rhs.connections_num;
      
    endfunction : do_copy

    virtual function string convert2string();
        string s = super.convert2string();
        s = {s, $sformatf("\n-----------------------------------------------") };
        s = {s, $sformatf("\n  name           :   %s"   , get_name()        ) };
        s = {s, $sformatf("\n  connections    :   %0d"   , connections_num   ) };
        s = {s, $sformatf("\n  addr_alignment :   %0d"   , address_alignment ) };
        s = {s, $sformatf("\n  num_ports      :   %0d"   , num_ports         ) };
        s = {s, $sformatf("\n  valid_ports    :   %p"   , valid_ports       ) };
        if (forced_address != '0) begin
          s = {s, $sformatf("\n  forced_address    :   0x%0x"   , forced_address       ) };
        end
        s = {s, $sformatf("\n-----------------------------------------------") };
        return s;
      
    endfunction : convert2string

  endclass // rvv_sequence_item
  `endif // RVV_SEQ_ITEM_SV
