`ifndef SOC_MGMT_FUNC_COV_SV
`define SOC_MGMT_FUNC_COV_SV
`uvm_analysis_imp_decl(_axi4_lp_rcv_func_cov_pkt)
class soc_mgmt_func_cov extends uvm_component;
  `uvm_component_utils(soc_mgmt_func_cov)

  uvm_analysis_imp_axi4_lp_rcv_func_cov_pkt #(svt_axi_transaction,soc_mgmt_func_cov) axi4_lp_2_func_cov_export;
    
  // soc_mgmt RAL Modl
  soc_mgmt_reg_block soc_mgmt_regmodel;
  virtual soc_mgmt_if soc_mgmt_if;


  /***************************************************************************************
  					Covergroups
  ***************************************************************************************/
  covergroup soc_mgmt_axi4_lp_trans_cg;
    option.per_instance = 1'b1;
    option.name         = "soc_mgmt_axi4_lp_trans_cg";

  /**AXI transactions covergroups**/
  endgroup : soc_mgmt_axi4_lp_trans_cg

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
    axi4_lp_2_func_cov_export        = new("axi4_lp_2_func_cov_export", this);
    soc_mgmt_axi4_lp_trans_cg             = new();
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    uvm_config_db#(virtual soc_mgmt_if)::get(uvm_root::get(), "", "soc_mgmt_if", soc_mgmt_if);
  endfunction : build_phase

  virtual function void write_axi4_lp_rcv_func_cov_pkt(input svt_axi_transaction axi4_lp_pkt);
    uvm_report_info(get_type_name(), $psprintf("Func cov: received packet from AXI4 LP Report %s", axi4_lp_pkt.sprint()), UVM_LOW);
    soc_mgmt_axi4_lp_trans_cg.sample();

    uvm_report_info(get_type_name(), $psprintf("Func cov: received packet from AXI4 LP Report process_lp_packet function %s", axi4_lp_pkt.sprint()), UVM_DEBUG);
  endfunction : write_axi4_lp_rcv_func_cov_pkt

endclass
`endif
