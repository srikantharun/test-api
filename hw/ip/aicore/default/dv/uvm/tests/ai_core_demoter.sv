/**
 *UVM Report Catcher to catch UVM_WARNING  [UVM/RSRC/NOREGEX] a resource with meta characters in the field name  has been created "regmodel.slave_blk"
 */
class ai_core_demoter extends uvm_report_catcher;

  function new(string name="ai_core_demoter");
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
    err = err | demote_x_in_obs_regs()| certain_addr_demote();

    if (err) begin
       set_severity(UVM_INFO);
    end
    return THROW;
  endfunction

    function certain_addr_demote();
          bit err_new;
          svt_axi_master_agent axi_mst;
          uvm_reg regs[$];
          err_new = string_search(get_message(), "Monitor Check for X or Z on RDATA when RVALID is high");

           if (err_new) begin

            if (!uvm_config_db#(svt_axi_master_agent)::get(null, "", "CFG_AXI_MST_AGENT", axi_mst)) begin
             `uvm_fatal(get_name(), "Unable to get svt_axi_master_agent from config db!")
            end else begin
              axi_mst.axi_regmodel.get_registers(regs);

              foreach (regs[i]) begin
               if (axi_mst.vif.axi_monitor_cb.araddr == 32'h100c0038 | axi_mst.vif.axi_monitor_cb.araddr == 32'h100c0048 | axi_mst.vif.axi_monitor_cb.araddr == 32'h100b0038 | axi_mst.vif.axi_monitor_cb.araddr == 32'h100b0048| axi_mst.vif.axi_monitor_cb.araddr == 32'h100e0038 | axi_mst.vif.axi_monitor_cb.araddr == 32'h100e0048 | axi_mst.vif.axi_monitor_cb.araddr == 32'h100f0048 | axi_mst.vif.axi_monitor_cb.araddr == 32'h100f0038) begin
                 return(err_new);
               end
              end

            end
           end

    endfunction




  function bit demote_x_in_obs_regs();
    svt_axi_master_agent axi_mst;
    string err_msg, field_vld_name, field_lst_name, field_rdy_name;
    bit err;
    int x_or_z_q[$], last_field_q[$];
    uvm_reg regs[$];
    uvm_reg_field fields[$];
    int vld_indx, lst_indx, rdy_indx;

    err = string_search(get_message(), "Monitor Check for X or Z on RDATA when RVALID is high");
    if (err) begin
      if (!uvm_config_db#(svt_axi_master_agent)::get(null, "", "CFG_AXI_MST_AGENT", axi_mst)) begin
        `uvm_fatal(get_name(), "Unable to get svt_axi_master_agent from config db!")
      end else begin
        for (int i=0; i < `AXI_LP_DATA_WIDTH; i++) begin
          // Use clocking block so that sampling happens 1step before, otherwise, tb will sample the new data which already changed
         //if (axi_mst.vif.axi_monitor_cb.rdata[i] !== 0 && axi_mst.vif.axi_monitor_cb.rdata[i] !== 1 && axi_mst.vif.axi_monitor_cb.rvalid === 1) begin
          if (axi_mst.vif.axi_monitor_cb.rdata[i] !== 0 && axi_mst.vif.axi_monitor_cb.rdata[i] !== 1 && axi_mst.vif.axi_monitor_cb.rvalid === 1) begin
            x_or_z_q.push_back(i);
            `uvm_info(get_name(), $sformatf("x_or_z_q push back %0d x_or_z_q_slv0 equal to %p", i, x_or_z_q), UVM_LOW)
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
                      field_lst_name = {field_vld_name.substr(0, field_vld_name.len()-5), "_lst"}; // minus _vld + _lst
                      field_rdy_name = {field_vld_name.substr(0, field_vld_name.len()-5), "_rdy"}; // minus _rdy + _lst
                      foreach (fields[k]) begin
                        if (string_search(fields[k].get_name(), field_lst_name)) begin
                          // get the index of lst field
                          lst_indx = fields[k].get_lsb_pos();
                          if ($isunknown(axi_mst.vif.axi_monitor_cb.rdata[lst_indx])) begin
                            last_field_q.push_back(lst_indx);  // this means it has no valid and last is unknown
                            `uvm_info(get_name(), $sformatf("no valid with X or Z last for reg: %s field %s", regs[i].get_name(), fields[k].get_name()), UVM_LOW)
                          end
                          break; // foreach (fields[k])
                        end
                      end
                      foreach (fields[l]) begin
                        if (string_search(fields[l].get_name(), field_rdy_name)) begin
                          // get the index of rdy field
                          rdy_indx = fields[l].get_lsb_pos();
                          if ($isunknown(axi_mst.vif.axi_monitor_cb.rdata[rdy_indx])) begin
                            last_field_q.push_back(rdy_indx);  // this means it has no valid and rdy is unknown
                            `uvm_info(get_name(), $sformatf("no valid with X or Z last for reg: %s field %s", regs[i].get_name(), fields[l].get_name()), UVM_LOW)
                          end
                          break; // foreach (fields[l])
                        end
                      end
                    end
                end
              end
              break; // foreach (fields[j])
            end
          end
        end
      end
    end
    foreach (x_or_z_q[i]) begin
            //$display("x_or_z_q= %p", x_or_z_q);
            //$display("last_field_q = %p", last_field_q);
      if (!(x_or_z_q[i] inside {last_field_q})) begin
        return 0; // do not demote error, it is a valid X or Z erorr!
      end
    end
    return (err && x_or_z_q.size() > 0 );
  endfunction
endclass

//slave_demoter
class ai_core_demoter_slv#(string which_cfg_axi_slv = "CFG_AXI_SLV0_AGENT" ) extends uvm_report_catcher;
  `uvm_object_param_utils(ai_core_demoter_slv#(which_cfg_axi_slv))

  function new(string name="ai_core_demoter_slv");
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
    err = err | demote_x_in_obs_regs() ;

    if (err) begin
       set_severity(UVM_INFO);
    end
    return THROW;
  endfunction


  function bit demote_x_in_obs_regs();
    svt_axi_slave_agent axi_slv;
    svt_axi_master_agent axi_mst;
    virtual ai_core_top_if tb_cfg_if;

    string err_msg, field_vld_name, field_lst_name,field_rdy_name;
    bit err;
    int x_or_z_q_slv[$], last_field_q_slv[$];
    uvm_reg regs[$];
    uvm_reg_field fields[$];
    int vld_indx, lst_indx, rdy_indx;

    x_or_z_q_slv.delete();
    last_field_q_slv.delete();
    err = string_search(get_message(), "Monitor Check for X or Z on RDATA when RVALID is high");
    if (err) begin
      if (!uvm_config_db#(svt_axi_slave_agent)::get(null, "", which_cfg_axi_slv, axi_slv)) begin
        `uvm_fatal(get_name(), "Unable to get svt_axi_slave_agent from config db!")
      end else begin
        for (int i=0; i < `AXI_LP_DATA_WIDTH; i++) begin
          // Use clocking block so that sampling happens 1step before, otherwise, tb will sample the new data which already changed
          if (axi_slv.vif.axi_monitor_cb.rdata[i] !== 0 && axi_slv.vif.axi_monitor_cb.rdata[i] !== 1 && axi_slv.vif.axi_monitor_cb.rvalid === 1) begin
            x_or_z_q_slv.push_back(i);
            `uvm_info(get_name(), $sformatf("x_or_z_q_slv push back %0d x_or_z_q_slv equal to %p", i, x_or_z_q_slv), UVM_LOW)
          end
        end
        if (x_or_z_q_slv.size() > 0) begin
          if (!uvm_config_db#(svt_axi_master_agent)::get(null, "", "CFG_AXI_MST_AGENT", axi_mst)) begin
           `uvm_fatal(get_name(), "Unable to get svt_axi_master_agent from config db!")
          end 
          uvm_config_db#(virtual ai_core_top_if)::get(uvm_root::get(), "", "tb_cfg_if", tb_cfg_if);
          axi_mst.axi_regmodel.get_registers(regs);
          foreach (regs[i]) begin
            if (regs[i].get_address() == ({tb_cfg_if.cid[7:0],axi_slv.vif.axi_monitor_cb.araddr[27:0]})) begin
              regs[i].get_fields(fields);
              foreach (fields[j]) begin
                field_vld_name = fields[j].get_name();
                if (string_search(field_vld_name, "_vld")) begin
                    // check if valid is 0
                    vld_indx = fields[j].get_lsb_pos();
                    if (axi_slv.vif.axi_monitor_cb.rdata[vld_indx] === 0) begin
                      // now check if it has corresponding last field
                      field_lst_name = {field_vld_name.substr(0, field_vld_name.len()-5), "_lst"}; // minus _vld + _lst
                      field_rdy_name = {field_vld_name.substr(0, field_vld_name.len()-5), "_rdy"}; // minus _vld + _rdy
                      foreach (fields[k]) begin
                        if (string_search(fields[k].get_name(), field_lst_name)) begin
                          // get the index of lst field
                          lst_indx = fields[k].get_lsb_pos();
                          if ($isunknown(axi_slv.vif.axi_monitor_cb.rdata[lst_indx])) begin
                            last_field_q_slv.push_back(lst_indx);  // this means it has no valid and last is unknown
                            `uvm_info(get_name(), $sformatf("inside slave 1 no valid with X or Z last for reg: %s field %s", regs[i].get_name(), fields[k].get_name()), UVM_LOW)
                          end
                          break; // foreach (fields[k])
                        end
                      end

                      foreach (fields[l]) begin
                        if (string_search(fields[l].get_name(), field_rdy_name)) begin
                          // get the index of rdy field
                          rdy_indx = fields[l].get_lsb_pos();
                          if ($isunknown(axi_slv.vif.axi_monitor_cb.rdata[rdy_indx])) begin
                            last_field_q_slv.push_back(rdy_indx);  // this means it has no valid and rdy is unknown
                            `uvm_info(get_name(), $sformatf("inside slave 2 no valid with X or Z last for reg: %s field %s", regs[i].get_name(), fields[l].get_name()), UVM_LOW)
                          end
                          break; // foreach (fields[l])
                        end
                      end

                    end
                end
              end
              break; // foreach (fields[j])
            end
          end
        end
      end
    end
    foreach (x_or_z_q_slv[i]) begin
            //$display("x_or_z_q_slv= %p", x_or_z_q_slv);
            //$display("last_field_q_slv = %p", last_field_q_slv);
      if (!(x_or_z_q_slv[i] inside {last_field_q_slv})) begin
        return 0; // do not demote error, it is a valid X or Z erorr!
      end
    end
    return (err && x_or_z_q_slv.size() > 0 );
  endfunction
endclass

 
