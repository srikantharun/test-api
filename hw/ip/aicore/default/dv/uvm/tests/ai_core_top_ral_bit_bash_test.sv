class ai_core_top_ral_bit_bash_test extends ai_core_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_top_ral_bit_bash_test);
  uvm_status_e         status;
  uvm_reg_bit_bash_seq seq;
  uvm_reg reg_list[$];
  int i;
  string reg_name; //declare before the loop

  function new (string name="ai_core_top_ral_bit_bash_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("ai_core_top_ral_bit_bash_test", "is entered", UVM_LOW)
    //set_type_override_by_type(ai_core_uvm_pkg::svt_axi_reg_adapter::get_type(), ai_core_uvm_pkg::ai_core_axi_slverr_adapter::get_type());
    seq = uvm_reg_bit_bash_seq::type_id::create("seq");
    uvm_top.set_timeout(1500us, 1);
    `uvm_info("ai_core_top_ral_bit_bash_test", "build - is exited", UVM_LOW)
  endfunction : build_phase

   function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);
       env.cfg.bus_inactivity_timeout = 1500000;
  endfunction: start_of_simulation_phase


  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    phase.raise_objection(this);
    //This test was reading from WO registers, so suppressing it.
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd0_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd1_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd2_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifdw_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd0_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd1_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_odr_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_odr_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 

    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd0_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd1_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd2_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifdw_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd0_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd1_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_odr_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_odr_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 

    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd0_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd1_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd2_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifdw_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd0_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd1_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_odr_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_odr_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 

    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd0_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd1_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd2_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifdw_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd0_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd1_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_odr_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_odr_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 

    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd0_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd1_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd2_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifdw_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd0_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd1_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_odr_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_odr_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 

    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd0_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd1_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifd2_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_ifdw_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd0_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_ifd1_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_odr_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_odr_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 

    //MVM REGISTERS
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmexe_regmod.perf_stall_in.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmexe_regmod.perf_stall_out.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmexe_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmexe_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);      //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmexe_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmexe_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmexe_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmexe_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmprg_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);      //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmprg_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmprg_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmprg_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmprg_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_mvmprg_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register

    //IAU REGISTERS
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_iau_regmod.perf_stall_in.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_iau_regmod.perf_stall_out.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_iau_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_iau_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);      //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_iau_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_iau_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_iau_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_iau_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 

    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_iau_regmod.perf_stall_in.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_iau_regmod.perf_stall_out.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_iau_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_iau_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);      //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_iau_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_iau_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_iau_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_iau_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register

    //DPU REGISTERS
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_dpu_regmod.perf_stall_in.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_dpu_regmod.perf_stall_out.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_dpu_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_dpu_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);      //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_dpu_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_dpu_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_dpu_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.m_dpu_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 

    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dpu_regmod.perf_stall_in.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dpu_regmod.perf_stall_out.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dpu_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dpu_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);      //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dpu_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dpu_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dpu_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dpu_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register

    //DWPU Registers
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dwpu_regmod.perf_stall_in.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dwpu_regmod.perf_stall_out.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this); //RC register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dwpu_regmod.cmdblk_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dwpu_regmod.dp_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);      //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dwpu_regmod.dbg_observe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dwpu_regmod.cmdgen_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dwpu_regmod.dbg_id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register 
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.d_dwpu_regmod.hw_capability.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register

    //AXI4 MAILBOX
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.axi4_mbox_regmod.error.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RC register
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.axi4_mbox_regmod.irqp.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.axi4_mbox_regmod.status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
   
    //TOKEN MANAGER //TODO: https://git.axelera.ai/prod/europa/-/issues/1371
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_hp_dma_1_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_hp_dma_1_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_hp_dma_0_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_hp_dma_0_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.swep_cons_2.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);          //RC register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_ifd_0_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_ifd_0_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_ifd_1_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_ifd_1_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_ifd_2_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_ifd_2_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_ifd_w_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_ifd_w_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_mvmprg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_mvmexe.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_odr_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_m_odr_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_d_odr_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_d_odr_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_d_ifd_0_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_d_ifd_0_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_d_ifd_1_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.prod_cnt_d_ifd_1_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_cons_cnt_aic0_dma_c0_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_cons_cnt_aic0_dma_c0_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_cons_cnt_aic0_dma_c0_2.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_cons_cnt_aic0_dma_c1_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_cons_cnt_aic0_dma_c1_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_cons_cnt_aic0_dma_c1_2.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_cons_cnt_aic0_cd.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_prod_cnt_aic0_cd.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_prod_cnt_aic0_dma_c0_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_prod_cnt_aic0_dma_c0_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_prod_cnt_aic0_dma_c1_0.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.tkn_manager_regmod.top_prod_cnt_aic0_dma_c1_1.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);   //RO register


   //TIMESTAMP LOGGER
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.timestamp_logger_regmod.entry_count.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register

   //LP DMA
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_lp_dma_regmod.ch1_axi_qosreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);     //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_lp_dma_regmod.dmac_idreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_lp_dma_regmod.dmac_compverreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_lp_dma_regmod.dmac_intstatusreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_lp_dma_regmod.ch1_ctl.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);            //RO register //TODO
   //HP DMA
   //uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_hp_dma_regmod.ch1_ctl.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);            //RO register //TODO
   //uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_hp_dma_regmod.ch2_ctl.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);            //RO register //TODO
   //uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_hp_dma_regmod.ch1_axi_qosreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);     //RO register
   //uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_hp_dma_regmod.ch2_axi_qosreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);     //RO register
   //uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_hp_dma_regmod.dmac_idreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register
   //uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_hp_dma_regmod.dmac_compverreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register
   //uvm_resource_db#(bit)::set({"REG::", env.regmodel.aic_hp_dma_regmod.dmac_intstatusreg.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register

   //INFRA PERIPH CSR
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.infra_periph_regmod.lt_dma_debug.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);    //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.infra_periph_regmod.obs_sig.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);         //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.infra_periph_regmod.ai_core_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.infra_periph_regmod.id.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);              //RO register

   //MID PERIPH CSR
   for (i = 0; i < 6; i++) begin
     reg_name = { "REG::", env.regmodel.mid_periph_regmod.c2c_counters[i].get_full_name(), "*" };
     uvm_resource_db#(bit)::set(reg_name, "NO_REG_BIT_BASH_TEST", 1, this);  // RO register
   end
   for (i = 0; i < 30; i++) begin
     reg_name = { "REG::", env.regmodel.mid_periph_regmod.svs_imc_counters[i].get_full_name(), "*" };
     uvm_resource_db#(bit)::set(reg_name, "NO_REG_BIT_BASH_TEST", 1, this);  // RO register
   end
   for (i = 0; i < 30; i++) begin
     reg_name = { "REG::", env.regmodel.mid_periph_regmod.svs_core_counters[i].get_full_name(), "*" };
     uvm_resource_db#(bit)::set(reg_name, "NO_REG_BIT_BASH_TEST", 1, this);  // RO register
   end
   for (i = 0; i < 43; i++) begin
      reg_name = { "REG::", env.regmodel.mid_periph_regmod.p2_counters[i].get_full_name(), "*" };
     uvm_resource_db#(bit)::set(reg_name, "NO_REG_BIT_BASH_TEST", 1, this);  // RO register
   end
   for (i = 0; i < 14; i++) begin
     reg_name = { "REG::", env.regmodel.mid_periph_regmod.p1_counters[i].get_full_name(), "*" };
     uvm_resource_db#(bit)::set(reg_name, "NO_REG_BIT_BASH_TEST", 1, this);  // RO register
   end
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.mid_periph_regmod.monitor_min_max_value.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);  //RO register
   uvm_resource_db#(bit)::set({"REG::", env.regmodel.mid_periph_regmod.imc_bist_status.get_full_name(), "*"}, "NO_REG_BIT_BASH_TEST", 1, this);        //RO register

   //INFRA PERIPH CSR
   seq.model = env.regmodel;
   #300ns;
   `uvm_info("ai_core_top_ral_bit_bash_test", "Before sequence start", UVM_LOW)
   seq.start(null);
   `uvm_info("ai_core_top_ral_bit_bash_test", "After sequence start", UVM_LOW)
   env.regmodel.print();
   `uvm_info("ai_core_top_ral_bit_bash_test", "Main phase exited", UVM_LOW)
    phase.drop_objection(this);
  endtask : main_phase

endclass:ai_core_top_ral_bit_bash_test
