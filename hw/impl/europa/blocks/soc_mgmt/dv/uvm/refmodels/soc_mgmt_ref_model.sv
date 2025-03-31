`ifndef SOC_MGMT_REF_MODEL_SV
`define SOC_MGMT_REF_MODEL_SV
`uvm_analysis_imp_decl(_axi4_lp_rcv_pkt)
`uvm_analysis_imp_decl(_axis_ifdw_rcv_pkt)
`uvm_analysis_imp_decl(_axis_ifd0_rcv_pkt)
//typedef soc_mgmt_subsys_reg_block soc_mgmt_RAL;
class soc_mgmt_ref_model extends uvm_component;
  `uvm_component_utils(soc_mgmt_ref_model)

  // soc_mgmt user Inteface Handle
  virtual soc_mgmt_if soc_mgmt_if;
    
  //soc_mgmt RAL Modl
  soc_mgmt_reg_block soc_mgmt_regmodel;
  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Recieve soc_mgmt user interface handle
    uvm_config_db#(virtual soc_mgmt_if)::get(uvm_root::get(), "uvm_test_top", "soc_mgmt_if", soc_mgmt_if);
  endfunction : build_phase

endclass
`endif
