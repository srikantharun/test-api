`ifndef AI_CORE_INFRA_COVERAGE_SV
`define AI_CORE_INFRA_COVERAGE_SV

class ai_core_infra_coverage extends uvm_component;
  `uvm_component_utils(ai_core_infra_coverage)
  
  virtual ai_core_infra_config_if tb_cfg_if;

  covergroup cvg_ai_core_infra_func;
    option.per_instance = 1'b1;
    option.name         = "cvg_ai_core_infra_func";

    cp_ai_core_infra_cid : coverpoint tb_cfg_if.cid {
      bins cid_1     = {1};
      bins cid_2     = {2};
      bins cid_3     = {3};
      bins cid_4     = {4};
    }

    cp_ai_core_infra_reg_blk : coverpoint tb_cfg_if.reg_blk {
      bins mailbox_reg_blk = {1};
      bins pvt_reg_blk     = {2};
      bins dma_reg_blk     = {3};
      bins pmu_reg_blk     = {4};
      bins csr_reg_blk     = {5};
    }

    cp_ai_core_infra_master : coverpoint tb_cfg_if.mstr_initiator {
      bins mstr_noc    = {1};
      bins mstr_cntrlr = {2};
      bins mstr_ls_hp  = {3};
      bins mstr_dma_0  = {4};
      bins mstr_dma_1  = {5};
    }
    
    cp_ai_core_infra_atu_cfg : coverpoint tb_cfg_if.atu_cfg {
      bins bypass_cfg       = {1};
      bins valid_access_cfg = {2};
    }

    cp_ai_core_infra_dma_chnl : coverpoint tb_cfg_if.dma_chnl {
      bins dma_chnl[]    = {[0:3]};
    }

    cp_atu_cfg_X_dma_chnl_X_master : cross cp_ai_core_infra_atu_cfg, cp_ai_core_infra_master, cp_ai_core_infra_dma_chnl {
      ignore_bins inv_master = binsof(cp_ai_core_infra_master.mstr_noc) || binsof(cp_ai_core_infra_master.mstr_cntrlr)  ;
    }

    cp_cid_X_master_X_reg_blk   : cross cp_ai_core_infra_cid, cp_ai_core_infra_master, cp_ai_core_infra_reg_blk ;

    cp_ai_core_infra_slave : coverpoint tb_cfg_if.slv_receiver {
      bins noc_lp_slv = {1};
      bins noc_hp_slv = {2};
      bins ls_hp_slv  = {3};
      bins ls_lp_slv  = {4};
      bins mvm_slv    = {5};
      bins dwpu_slv   = {6};
      bins dpu_0_slv  = {7};
      bins dpu_1_slv  = {8};
    }
    
    cp_cid_X_master_X_slv   : cross cp_ai_core_infra_cid, cp_ai_core_infra_master, cp_ai_core_infra_slave ;

    cp_ai_core_infra_thrtl_mode : coverpoint tb_cfg_if.throttle_mode {
      bins disabled   = {1};
      bins max_limit  = {2};
      bins hard_thrtl = {3};
      bins soft_thrtl = {4};
    }
    
    cp_ai_core_infra_thrtl_src : coverpoint tb_cfg_if.throttle_src {
      bins csr_src  = {1};
      bins temp_src = {2};
      bins volt_src = {3};
      bins ext_src  = {4};
    }
    
    cp_thrtl_src_X_thrtl_mode   : cross cp_ai_core_infra_thrtl_src, cp_ai_core_infra_thrtl_mode;

    cp_ai_core_infra_rd_itrlv : coverpoint tb_cfg_if.rd_intrlv_src {
      bins rd_intrlv_noc    = {1};
      bins rd_intrlv_cntrlr = {2};
      bins rd_intrlv_ls_hp  = {3};  
      bins rd_intrlv_dma_0  = {4};  
      bins rd_intrlv_dma_1  = {5};  
    }

    cp_rd_intrlv_src_X_atu_cfg   : cross cp_ai_core_infra_rd_itrlv, cp_ai_core_infra_atu_cfg {
      ignore_bins inv_master = binsof(cp_ai_core_infra_rd_itrlv.rd_intrlv_noc) || binsof(cp_ai_core_infra_rd_itrlv.rd_intrlv_cntrlr)  ;
    }

  endgroup

  function new(string name, uvm_component parent);
    super.new(name,parent);
    cvg_ai_core_infra_func   = new();
    `uvm_info("constructor_coverage", "cover group created.", UVM_LOW)
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...",UVM_LOW) 
    //getting tb configuration interface in environment
    uvm_config_db#(virtual ai_core_infra_config_if)::get(uvm_root::get(), "", "tb_cfg_if", tb_cfg_if);
    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction:build_phase

virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    forever begin
      fork      

        begin
          @(posedge tb_cfg_if.mstr_initiator);
          cvg_ai_core_infra_func.sample();
        end

        begin
          @(posedge tb_cfg_if.slv_receiver);
          cvg_ai_core_infra_func.sample();
        end

         begin
          @(posedge tb_cfg_if.reg_blk);
          cvg_ai_core_infra_func.sample();
        end

      join_any
    end
    
  endtask : run_phase

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_full_name(), $sformatf("cvg_ai_core_infra : %.2f%%", cvg_ai_core_infra_func.get_coverage()), UVM_LOW)
  endfunction : report_phase

endclass

`endif
