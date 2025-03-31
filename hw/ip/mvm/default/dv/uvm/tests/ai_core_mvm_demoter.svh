/**
 *UVM Report Catcher to catch UVM_WARNING  [UVM/RSRC/NOREGEX] a resource with meta characters in the field name  has been created "regmodel.slave_blk"
 */
class ai_core_mvm_demoter extends uvm_report_catcher;

  function new(string name="ai_core_mvm_demoter");
   super.new(name);
  endfunction
  
  function bit string_search(string message, string pattern);
    int match_count;
    int len         = message.len();
    int pattern_len = pattern.len();
      for(int i =0; i < len;i++) begin
        if(message.substr(i,i+pattern_len-1) ==pattern) begin
          match_count +=1;
        end
      end
    return (match_count>0);
  endfunction

  function action_e catch();
    bit err;

    err = string_search(get_message(), "a resource with meta characters in the field name has been created");
    err = err | demote_x_in_obs_regs();

    if (err) begin
       set_severity(UVM_INFO);
    end
    return THROW;
  endfunction

  function bit demote_x_in_obs_regs();
    svt_axi_master_agent axi_mst;
    string err_msg, field_vld_name, field_lst_name;
    bit err;
    int x_or_z_q[$], last_field_q[$];
    uvm_reg regs[$];
    uvm_reg_field fields[$];
    int vld_indx, lst_indx;

    err = string_search(get_message(), "Monitor Check for X or Z on RDATA when RVALID is high");
    if (err) begin
      if (!uvm_config_db#(svt_axi_master_agent)::get(null, "", "CFG_AXI_MST_AGENT", axi_mst)) begin
        `uvm_fatal(get_name(), "Unable to get svt_axi_master_agent from config db!")
      end else begin
        for (int i=0; i < AXI_LT_DATA_WIDTH; i++) begin
          // Use clocking block so that sampling happens 1step before, otherwise, tb will sample the new data which already changed
          if (axi_mst.vif.axi_monitor_cb.rdata[i] !== 0 && axi_mst.vif.axi_monitor_cb.rdata[i] !== 1) begin
            x_or_z_q.push_back(i);
          end
        end
        if (x_or_z_q.size() > 0) begin
          axi_mst.axi_regmodel.get_registers(regs);
          foreach (regs[i]) begin
            if (regs[i].get_address() == axi_mst.vif.axi_monitor_cb.araddr) begin
              regs[i].get_fields(fields);
              foreach (fields[j]) begin
                field_vld_name = fields[j].get_name();
                if (string_search(field_vld_name, "_vld")) begin
                    // check if valid is 0
                    vld_indx = fields[j].get_lsb_pos();
                    if (axi_mst.vif.axi_monitor_cb.rdata[vld_indx] === 0) begin
                      // now check if it has corresponding last field
                      field_lst_name = {field_vld_name.substr(0, field_vld_name.len()-5), "_cmd"}; // minus _vld + _cmd
                      foreach (fields[k]) begin
                        if (string_search(fields[k].get_name(), field_lst_name)) begin
                          // get the index of lst field
                          lst_indx = fields[k].get_lsb_pos();
                          for( int len=0;len<fields[k].get_n_bits();len++) begin
                            if ($isunknown(axi_mst.vif.axi_monitor_cb.rdata[lst_indx+len])) begin
                               last_field_q.push_back(lst_indx+len);  // this means it has no valid and last is unknown
                              `uvm_info(get_name(), $sformatf("no valid with X or Z last for reg: %s field %s", regs[i].get_name(), fields[k].get_name()), UVM_LOW)
                            end
			  end
                        end
                      end
                    end
                end
              end
            end
          end
        end
      end
    end
    foreach (x_or_z_q[i]) begin
      if (!(x_or_z_q[i] inside {last_field_q})) begin
        return 0; // do not demote error, it is a valid X or Z erorr!
      end
    end
    return (err);
  endfunction
endclass
