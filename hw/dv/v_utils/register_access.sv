`ifndef GUARD_REGISTER_ACCESS_SV
`define GUARD_REGISTER_ACCESS_SV

// Register Access Utility
class register_access #(type T, int ADDR_W=36, int DATA_W=64) extends uvm_component;
  `uvm_component_param_utils(register_access#(T, ADDR_W, DATA_W))

  T m_regmodel;
  typedef bit[ADDR_W-1:0] addr_t;
  typedef bit[DATA_W-1:0] data_t;
  
  function new(string name, uvm_component parent);
        super.new(name, parent);
  endfunction: new

  task write_reg (input data_t     data,
                  input string     name  = "",
                  input string     field = "",
                  input addr_t     addr  = 0,
                  input uvm_path_e path  = UVM_FRONTDOOR);

    uvm_reg curr_reg;
    uvm_reg_field curr_field;
    uvm_status_e rw_status;

    if (!get_register(curr_reg, name, addr)) begin
      `uvm_error(get_name(), $sformatf("write_reg(): Register '%s' unknown", name))
       return;
    end

    if (field != "") begin
      curr_field = curr_reg.get_field_by_name(field);
      if (curr_field == null) begin
        `uvm_error(get_name(), $sformatf("write_reg(): Register field '%s' unknown", field))
         return;
      end else begin
        // set the register-field (only local in register model)
        curr_field.set(data);
        // this writes the whole register
        curr_reg.update(.status(rw_status), .path(path));
      end
    end else begin
      if (curr_reg.get_rights() inside {"RW", "WO"}) begin
        curr_reg.write(rw_status, data, path);
      end else begin
        `uvm_error(get_name(), $sformatf("Trying to write to: %s which is not writable", curr_reg.get_full_name()))
      end
    end
  endtask

  task read_reg (output data_t     data,
                 input  data_t     exp_data = 0,
                 input  bit        compare = 0,
                 input  string     name     = "",
                 input  string     field    = "",
                 input  addr_t     addr     = 0,
                 input  uvm_path_e path     = UVM_FRONTDOOR);

    uvm_reg curr_reg;
    uvm_status_e rw_status;
    int unsigned n,m;
    data_t mask_field;
    uvm_reg_field fields[$];
    bit compare_done = 0;
    int field_data;

    if (!get_register(curr_reg, name, addr)) begin
        `uvm_error(get_name(), $sformatf("read_reg(): Register '%s' unknown", name))
        return;
    end else begin
      if (curr_reg.get_rights() inside {"RW", "RO"}) begin
        curr_reg.read(rw_status, data, path);
      end else begin
        `uvm_error(get_name(), $sformatf("Trying to read to: %s which is not readable: %s", curr_reg.get_full_name(), curr_reg.get_rights()))
      end
      `uvm_info(get_name(), $sformatf("read_reg() data: 0x%0x", data), UVM_DEBUG)
      curr_reg.get_fields(fields);
      foreach(fields[i]) begin
        mask_field = '0;
        n          = fields[i].get_lsb_pos();
        m          = fields[i].get_n_bits();

        // whole register comparison
        if (field == "") begin
          // UVM reg standard with R: no effect
          if(fields[i].get_access() inside {"RW", "RO", "WC", "WS", "W1C", "W1S", "W1T", "W0C", "W0S", "W0T", "W1"} ) begin
            for(int k=n; k<n+m; k++) begin
              mask_field[k] = 1'b1;
            end
            if((data & mask_field) != (exp_data & mask_field) && compare) begin
              `uvm_error(get_name(),$sformatf("Field value mismatch for %s! : Act: 0x%0x, Exp: 0x%0x Mask: 0x%0x", fields[i].get_full_name(), data, exp_data, mask_field))
            end
          end
          compare_done = 1;
        // given field comparison only
        end else begin
          if (field == fields[i].get_name()) begin
            // UVM reg standard with R: no effect
            if(fields[i].get_access() inside {"RW", "RO", "WC", "WS", "W1C", "W1S", "W1T", "W0C", "W0S", "W0T", "W1"} ) begin
              for(int k=n; k<n+m; k++) begin
                field_data[k-n] = data[k]; // get the field value
              end
              if(field_data != exp_data && compare) begin // masking is not considered here since user wants to intentionally compare the field, as long as it is readable
                `uvm_error(get_name(),$sformatf("Field value mismatch for %s! : Act: 0x%0x, Exp: 0x%0x", fields[i].get_full_name(), field_data, exp_data))
              end
              data = field_data; // return field only instead of whole register
            end
            compare_done = 1;
            break;
          end
        end
      end
      if (compare_done==0 && compare) begin
          `uvm_warning(get_name(), $sformatf("read_reg(): Comparison did not happen at all for register %s", curr_reg.get_name()))
      end
    end
  endtask

  protected function bit get_register(output uvm_reg curr_reg,
                                      input  string  name,
                                      input  addr_t  addr);
    if (name == "") begin
      curr_reg = m_regmodel.default_map.get_reg_by_offset(addr);
    end else begin
      curr_reg = m_regmodel.get_reg_by_name($sformatf("%s", name.tolower()));
    end

    if (curr_reg != null) begin
      return 1;
    end else begin
      if (name == "") begin
        `uvm_error(get_name(), $sformatf("get_register(): Address '%h' does not exist!", addr))
      end else begin
        `uvm_error(get_name(), $sformatf("get_register(): Register '%s' does not exist!", name))
      end
      return 0;
    end
  endfunction

endclass
`endif
