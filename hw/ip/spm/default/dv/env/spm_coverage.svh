`ifndef SPM_COVERAGE_SV
`define SPM_COVERAGE_SV
//FIXME
class spm_coverage extends uvm_component;
  `uvm_component_utils(spm_coverage)

  uvm_analysis_imp#(svt_ahb_transaction,spm_coverage) item_collected_export;

  virtual spm_if spm_if;

  svt_ahb_transaction init_xact;

  covergroup cvg_spm_func;
    option.per_instance = 1'b1;
    option.name         = "cvg_spm_func";

    cp_spm_ecc_en : coverpoint spm_if.ecc_en {
      bins ecc_disable    = {0};
      bins ecc_enable     = {1};
    }

    cp_spm_error_disable : coverpoint spm_if.spm_error_disable {
      bins err_enb    = {0};
      bins err_dis    = {1};
    }

    cp_spm_error_status : coverpoint spm_if.scp_error_status[0] {
      bins err_absent   = {0};
      bins err_present  = {1};
    }

    cp_spm_error_type : coverpoint spm_if.scp_error_status[1] {
      bins corrupt_1bit = {0};
      bins corrupt_2bit = {1};
    }

    cp_spm_addr : coverpoint init_xact.addr {
      bins start_addr      ={[32'h0:2**5-1]};
      bins mid_addr        ={[2**5 : 2**10-1]};
      bins end_addr        ={[2**10:2**18-1]};
      ignore_bins inv_addr ={[2**18:2**32-1]};
    }

    cp_xact_type : coverpoint (init_xact.xact_type) {
      bins wr = {svt_ahb_transaction::WRITE};
      bins rd = {svt_ahb_transaction::READ};
      bins wr_rd = ({svt_ahb_transaction::WRITE} => {svt_ahb_transaction::READ});
      bins rd_wr = ({svt_ahb_transaction::READ} => {svt_ahb_transaction::WRITE});
    }

    cp_spm_inv_addr : coverpoint spm_if.inv_addr {
      bins in_range_addr    ={0};
      bins out_of_range_addr={1};
    }

    cp_spm_ecc_en_X_cp_spm_inv_addr         : cross cp_spm_ecc_en, cp_spm_inv_addr ;
    ccp_spm_error_type_X_cp_spm_error_status: cross cp_spm_error_type, cp_spm_error_status {
                         bins xy1 = binsof(cp_spm_error_status.err_present) && binsof(cp_spm_error_type.corrupt_1bit);
                         bins xy2 = binsof(cp_spm_error_status.err_present) && binsof(cp_spm_error_type.corrupt_2bit);
                         ignore_bins ap_addr = binsof(cp_spm_error_status.err_absent) ;
                       }


  endgroup

  function new(string name, uvm_component parent);
    super.new(name,parent);
    cvg_spm_func   = new();
    `uvm_info("constructor_coverage", "cover group created.", UVM_LOW)
  endfunction

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...",UVM_LOW)
    uvm_config_db#(virtual spm_if)::get(uvm_root::get(), "", "spm_intf", spm_if);
    item_collected_export = new("item_collected_export", this);
    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction:build_phase

  virtual function void write (input svt_ahb_transaction xact);
    init_xact = xact;
    `uvm_info("SUBS", $sformatf("New transaction received. Sampling coverage"), UVM_LOW)
    cvg_spm_func.sample();
  endfunction : write

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_full_name(), $sformatf("cvg_spm : %.2f%%", cvg_spm_func.get_coverage()), UVM_LOW)
  endfunction : report_phase


endclass

`endif
