`ifndef AIC_DMC_MONITOR_SV
`define AIC_DMC_MONITOR_SV

class aic_ls_monitor extends uvm_monitor;
  `uvm_component_utils(aic_ls_monitor)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual aic_ls_if vif;

  uvm_analysis_port#(aic_ls_seq_item) ap;

  aic_ls_seq_item prev_item;
  

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap  = new("ap", this);
    prev_item = aic_ls_seq_item::type_id::create("prev_item");
  endfunction

  virtual task run_phase(uvm_phase phase);
    aic_ls_seq_item item;
    uvm_comparer comparer;
    super.run_phase(phase);
    forever begin
      @(posedge vif.reset_an_i);
      `uvm_info(get_name(), "Reset negated!", UVM_HIGH)
      fork
        forever begin
          @(vif.mon);
          item = aic_ls_seq_item::type_id::create("item");

          item.reset_an_i                   = vif.mon.reset_an_i;
          item.cid                          = vif.mon.cid;
          item.l1_cg_enable                 = vif.mon.l1_cg_enable;
          item.dmc_cg_enable            = vif.mon.dmc_cg_enable;
          item.l1_sw_cfg_fabric_sel         = vif.mon.l1_sw_cfg_fabric_sel;
          item.l1_mem_ls                    = vif.mon.l1_mem_ls;
          item.l1_mem_ds                    = vif.mon.l1_mem_ds;
          item.l1_mem_sd                    = vif.mon.l1_mem_sd;
          item.l1_mem_rop                   = vif.mon.l1_mem_rop;
          item.l1_mem_daisy_chain_bypass_sd = vif.mon.l1_mem_daisy_chain_bypass_sd;
          item.l1_mem_daisy_chain_bypass_ds = vif.mon.l1_mem_daisy_chain_bypass_ds;
          item.aic_ls_obs               = vif.mon.aic_ls_obs;
          item.l1_lc_fabric_dlock           = vif.mon.l1_lc_fabric_dlock;
          item.sram_sw_test1                = vif.mon.sram_sw_test1;
          item.sram_sw_test_rnm             = vif.mon.sram_sw_test_rnm;
          item.sram_sw_rme                  = vif.mon.sram_sw_rme;
          item.sram_sw_rm                   = vif.mon.sram_sw_rm;
          item.sram_sw_wa                   = vif.mon.sram_sw_wa;
          item.sram_sw_wpulse               = vif.mon.sram_sw_wpulse;
          item.sram_sw_fiso                 = vif.mon.sram_sw_fiso;
          item.ls_cg_en                     = vif.mon.ls_cg_en;
          item.irq_out                      = vif.mon.irq_out;

          //only send the item due interface change 
          if (!prev_item.do_compare(item,comparer)) begin
            ap.write(item.do_clone);
          end
          prev_item.do_copy(item);
          `uvm_info(get_full_name(), "Got item!", UVM_HIGH)
        end
        @(negedge vif.reset_an_i);
      join_any
      disable fork;
      `uvm_info(get_name(), "Reset detected!", UVM_HIGH)
    end
  endtask
endclass

`endif


