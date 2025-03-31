`ifndef AIC_DMC_SEQ_ITEM
`define AIC_DMC_SEQ_ITEM

class aic_ls_seq_item extends uvm_sequence_item;
  `uvm_object_utils(aic_ls_seq_item)

  bit reset_an_i;
  bit [CID_WIDTH-1:0] cid;
  bit l1_cg_enable;
  bit dmc_cg_enable;
  bit [1:0] l1_sw_cfg_fabric_sel;
  bit l1_mem_ls;
  bit l1_mem_ds;
  bit l1_mem_sd;
  bit l1_mem_rop;
  bit l1_mem_daisy_chain_bypass_sd;
  bit l1_mem_daisy_chain_bypass_ds;
  bit[ OBS_DW-1:0] aic_ls_obs;
  bit[ 6:0] l1_lc_fabric_dlock;
  bit sram_sw_test1;
  bit sram_sw_test_rnm;
  bit sram_sw_rme;
  bit [3:0] sram_sw_rm;
  bit [2:0] sram_sw_wa;
  bit [2:0] sram_sw_wpulse;
  bit sram_sw_fiso;
  bit ls_cg_en;
  bit [IRQ_W-1:0] irq_out;


  function new (string name = "");
    super.new (name);
  endfunction

  virtual function aic_ls_seq_item do_clone();
    aic_ls_seq_item item;

    if(!$cast(item, this.clone()))
      `uvm_error(get_full_name(), "Clone failed")

    return item;
  endfunction

  virtual function void do_copy(uvm_object rhs);
    aic_ls_seq_item seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.reset_an_i                   = seq_rhs.reset_an_i;
    this.cid                          = seq_rhs.cid;
    this.l1_cg_enable                 = seq_rhs.l1_cg_enable;
    this.dmc_cg_enable            = seq_rhs.dmc_cg_enable;
    this.l1_sw_cfg_fabric_sel         = seq_rhs.l1_sw_cfg_fabric_sel;
    this.l1_mem_ls                    = seq_rhs.l1_mem_ls;
    this.l1_mem_ds                    = seq_rhs.l1_mem_ds;
    this.l1_mem_sd                    = seq_rhs.l1_mem_sd;
    this.l1_mem_rop                   = seq_rhs.l1_mem_rop;
    this.l1_mem_daisy_chain_bypass_sd = seq_rhs.l1_mem_daisy_chain_bypass_sd;
    this.l1_mem_daisy_chain_bypass_ds = seq_rhs.l1_mem_daisy_chain_bypass_ds;
    this.aic_ls_obs               = seq_rhs.aic_ls_obs;
    this.l1_lc_fabric_dlock           = seq_rhs.l1_lc_fabric_dlock;
    this.sram_sw_test1                = seq_rhs.sram_sw_test1;
    this.sram_sw_test_rnm             = seq_rhs.sram_sw_test_rnm;
    this.sram_sw_rme                  = seq_rhs.sram_sw_rme;
    this.sram_sw_rm                   = seq_rhs.sram_sw_rm;
    this.sram_sw_wa                   = seq_rhs.sram_sw_wa;
    this.sram_sw_wpulse               = seq_rhs.sram_sw_wpulse;
    this.sram_sw_fiso                 = seq_rhs.sram_sw_fiso;
    this.ls_cg_en                     = seq_rhs.ls_cg_en;
    this.irq_out                      = seq_rhs.irq_out;

  endfunction : do_copy

  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    aic_ls_seq_item seq_rhs;

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_compare cast failed");

    return ( super.do_compare(rhs, comparer) &&
             this.cid                          == seq_rhs.cid                          &&
             this.l1_cg_enable                 == seq_rhs.l1_cg_enable                 &&
             this.dmc_cg_enable            == seq_rhs.dmc_cg_enable            &&
             this.l1_sw_cfg_fabric_sel         == seq_rhs.l1_sw_cfg_fabric_sel         &&
             this.l1_mem_ls                    == seq_rhs.l1_mem_ls                    &&
             this.l1_mem_ds                    == seq_rhs.l1_mem_ds                    &&
             this.l1_mem_sd                    == seq_rhs.l1_mem_sd                    &&
             this.l1_mem_rop                   == seq_rhs.l1_mem_rop                   &&
             this.l1_mem_daisy_chain_bypass_sd == seq_rhs.l1_mem_daisy_chain_bypass_sd &&
             this.l1_mem_daisy_chain_bypass_ds == seq_rhs.l1_mem_daisy_chain_bypass_ds &&
             this.aic_ls_obs               == seq_rhs.aic_ls_obs               &&
             this.l1_lc_fabric_dlock           == seq_rhs.l1_lc_fabric_dlock           &&
             this.sram_sw_test1                == seq_rhs.sram_sw_test1                &&
             this.sram_sw_test_rnm             == seq_rhs.sram_sw_test_rnm             &&
             this.sram_sw_rme                  == seq_rhs.sram_sw_rme                  &&
             this.sram_sw_rm                   == seq_rhs.sram_sw_rm                   &&
             this.sram_sw_wa                   == seq_rhs.sram_sw_wa                   &&
             this.sram_sw_wpulse               == seq_rhs.sram_sw_wpulse               &&
             this.sram_sw_fiso                 == seq_rhs.sram_sw_fiso                 &&
             this.ls_cg_en                     == seq_rhs.ls_cg_en                     &&
             this.irq_out                      == seq_rhs.irq_out
    );
  endfunction : do_compare

  virtual function void reset();
    this.reset_an_i                   = 0;
    this.cid                          = 0;     
    this.l1_cg_enable                 = 0;
    this.dmc_cg_enable            = 0;    
    this.l1_sw_cfg_fabric_sel         = 0;
    this.l1_mem_ls                    = 0;
    this.l1_mem_ds                    = 0;
    this.l1_mem_sd                    = 0;
    this.l1_mem_rop                   = 0;
    this.l1_mem_daisy_chain_bypass_sd = 0;
    this.l1_mem_daisy_chain_bypass_ds = 0;
    this.aic_ls_obs               = 0;
    this.l1_lc_fabric_dlock           = 0;
    this.sram_sw_test1                = 0;
    this.sram_sw_test_rnm             = 0;
    this.sram_sw_rme                  = 0;
    this.sram_sw_rm                   = 0;
    this.sram_sw_wa                   = 0;
    this.sram_sw_wpulse               = 0;
    this.sram_sw_fiso                 = 0;
    this.ls_cg_en                     = 0;
    this.irq_out                      = 0;
  endfunction : reset
endclass

`endif

