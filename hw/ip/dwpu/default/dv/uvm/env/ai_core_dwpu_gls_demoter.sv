/**
 *UVM Demoter to catch UVM_ERROR /home/projects/dware/DESIGNWARE_HOME/vip/svt/common/S-2021.09/sverilog/src/vcs/svt_err_check_stats.svp(583) ...
  uvm_test_top.env.m_axi_system_env.slave[0].monitor [register_fail:AMBA:AXI4_STREAM:tvalid_low_when_reset_is_active_check] Description:
  Monitor Check that TVALID is low when reset is active
 */

class ai_core_dwpu_gls_demoter extends uvm_report_catcher;
  `uvm_object_utils(ai_core_dwpu_gls_demoter)

  ai_core_dwpu_env_cfg m_env_cfg_h;
  bit m_check_override = 0;
  static bit m_en_tvalid_during_rst_check=1;

  function new(string name="ai_core_dwpu_gls_demoter");
    super.new(name);
    if ($value$plusargs("CHK_OVERRIDE=%0d", m_check_override)) begin
      `uvm_info(get_type_name(), $sformatf("m_check_override is set to: %0d", m_check_override), UVM_LOW)
    end else begin
      `uvm_info(get_type_name(), $sformatf("m_check_override is set to default: %0d", m_check_override), UVM_LOW)
    end
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

    if (!uvm_config_db #(ai_core_dwpu_env_cfg)::get(null, "", "AI_CORE_DWPU_ENV_CFG", m_env_cfg_h)) begin
        `uvm_fatal(get_name(), "Unable to get ENV AI_CORE_DWPU_ENV_CFG")
    end
    `uvm_info(get_type_name(), $sformatf("GLS %0d en_tvalid_during_rst_check %0d", m_env_cfg_h.is_gls, m_env_cfg_h.en_tvalid_during_rst_check), UVM_HIGH)
    err = string_search(get_message(), "Monitor Check that TVALID is low when reset is active");
    if (err && m_env_cfg_h.is_gls && !m_env_cfg_h.en_tvalid_during_rst_check || m_check_override) begin
       set_severity(UVM_INFO);
    end
    return THROW;
  endfunction
endclass
