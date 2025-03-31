
/**
 * Abstract:
 * This file defines a class that represents a customized AXI Master
 * transaction.  This class extends the AXI VIP's svt_axi_master_transaction
 * class.  It adds pre-defined distribution constraints for transaction
 * weighting, and adds constraints.
 */
`ifndef GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV
`define GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV

class cust_svt_axi_master_transaction extends svt_axi_master_transaction;

  static int burst_type_fixed_wt = 0;
  static int burst_type_incr_wt  = 80;
  static int burst_type_wrap_wt  = 20;
  bit add_l1_base_addr= 1;
  static int l1_bank_index = -1;
  aic_ls_env m_env_h;

  static bit m_write_before_read;
  static protected int m_mem[$];

  // Declare user-defined constraints
  constraint master_constraints {
    // addr,burst_length, burst_type, atomic_type, cache_type,
    // data_user,resp_user
    (l1_bank_index== -1) ->  soft addr dist {
      22'h0                 :/ 10,
      [22'h1 : 22'h3F_FFFE] :/ 80,
      22'h3F_FFFF           :/ 10,
      [22'h1 : 22'h00_00FE] :/ 80,
      22'h00_00FF           :/ 10
    };

    (l1_bank_index  != -1) ->  addr == l1_bank_index * AIC_LS_ENV_L1_BANK_SIZE;

    // AWLEN/ARLEN
    burst_length dist {
      6'd0           :/ 2,
      [6'd1 : 6'd62] :/ 10,
      6'd63          :/ 2
    };
    // AWSIZE/ARSIZE
    burst_size dist {
      3'h0          :/ 2,
      [3'h1 : 3'h5] :/ 10,
      3'h6          :/ 2
    };
    // AWBURST/ARBURST
    soft burst_type dist {
      svt_axi_transaction::FIXED := burst_type_fixed_wt,
      svt_axi_transaction::INCR  := burst_type_incr_wt,
      svt_axi_transaction::WRAP  := burst_type_wrap_wt
    };
    atomic_type dist {['h0 : 'h0] :/ 1};
    cache_type dist {
      'h0 :/ 1,
      'h1 :/ 0
    };
    //data_user    dist {['h0 : 'h0]  :/ 1
    //                     };
    resp_user dist {['h0 : 'h0] :/ 1};
    // AWPROT/ARPROT => 010
    //prot_type dist {['h2 : 'h2] :/ 1};
    //cache_type       dist {'h0 :/ 1,
    //                       'h1 :/ 0
    //                };
  }

  constraint write_before_read_c {
    (m_write_before_read && (!(addr inside {m_mem}))) ->  xact_type == svt_axi_transaction::WRITE;
  }

  function void post_randomize();
    super.post_randomize();
    if (add_l1_base_addr) begin
      if (!uvm_config_db #(aic_ls_env)::get(null, "", "AIC_LS_ENV", m_env_h)) begin
        `uvm_fatal(get_name(), "Unable to get ENV AIC_LS_ENV")
      end
      if (m_write_before_read) begin
        if (!(addr inside {m_mem})) begin
          m_mem.push_back(addr);
        end
      end
      addr += m_env_h.m_env_cfg.m_l1_full_start_addr;
    end
  endfunction

  /** UVM Object Utility macro */
  `uvm_object_utils_begin(cust_svt_axi_master_transaction)
    `uvm_field_int(burst_type_fixed_wt, UVM_ALL_ON)
    `uvm_field_int(burst_type_incr_wt, UVM_ALL_ON)
    `uvm_field_int(burst_type_wrap_wt, UVM_ALL_ON)
  `uvm_object_utils_end

  /** Class Constructor */
  function new(string name = "cust_svt_axi_master_transaction");
    super.new(name);
  endfunction : new

endclass : cust_svt_axi_master_transaction

`endif  // GUARD_CUST_SVT_AXI_MASTER_TRANSACTION_SV
