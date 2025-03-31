`ifndef AI_CORE_CD_INSTR_PRG_SMOKE_TEST_SV
`define AI_CORE_CD_INSTR_PRG_SMOKE_TEST_SV


class ai_core_cd_mem_manager__prg_smoke_test#(int CMD_L_MAX=64, INSTR_L_MAX=256) extends ai_core_cd_mem_manager#(.CMD_L_MAX(CMD_L_MAX), .INSTR_L_MAX(INSTR_L_MAX));
    `uvm_component_utils(ai_core_cd_mem_manager__prg_smoke_test)

  constraint c_t_mem_size {
    mem_size == 120; 
  }          
  constraint c_t_mem_partition_num {
    mem_partition_num == 3;
  }
  //constraint c_t_spm_partition_idx {
  //  spm_partition_idx == 3;  
  //}


  constraint c_t_offset_tsk2base {
    offset_tsk2base == 0;
  }
  constraint c_t_offset_tsk2base8 {
    //offset_tsk2base == 8;
  }
  constraint c_t_offset_cmd2tsk {
    offset_cmd2tsk  == 8;
  }
  constraint c_t_offset_prg2cmd {
    offset_prg2cmd  == 8;
  }

  constraint c_t_command_list_min_size {
    command_list_size == 2;
  }
  constraint c_t_task_list_size {
    task_list_size    == 5;
  }
  constraint c_t_cmd_mem_size {
    cmd_mem_size      == 10;
  }
  constraint c_t_prg_mem_size {
    prg_mem_size      == 20;
  }

  // --- INHERITED METHODS - UVM_COMPONENT --- //
    function new(string name = "ai_core_cd_mem_manager", uvm_component parent = null);
        super.new(name, parent);

         `uvm_info("new", "Exiting...", UVM_LOW)
    endfunction : new

    
    //!!!!ToDO!!!!ToDO!!!!ToDO!!!!: remove patch after issue is closed/discussed 
    virtual function void compare_ref_to_svt();
        //ToDO: implement this method to compare reference memory addr_range data to SVT address range data
        //`uvm_error("REF_MODEL","METHOD IS NOT IMPLEMENTED: compare_ref_to_svt()")
    endfunction : compare_ref_to_svt


    function void override_cmd_list();
        foreach (command_list[i])
        begin
            command_list[i].control_offset = 0;
            command_list[i].length = 2;        //inside {[0:task_list_size-command_list[i].task_list_ptr]};
            command_list[i].task_list_ptr = 0; //inside {[0:task_list_size-1]}
        end
    endfunction : override_cmd_list


    function void override_instr_list(); 
        //override_instr_list_timestamp();
        //override_instr_list_token_with_errors();
        //override_instr_list_token();
        override_instr_list_prg();
        //override_instr_list_prg_unaligned_addr();
        //override_instr_list_cmd();
    endfunction : override_instr_list


endclass : ai_core_cd_mem_manager__prg_smoke_test

// AI CORE CD base test class
class ai_core_cd_instr_prg_smoke_test extends ai_core_cd_base_test;
  `uvm_component_utils(ai_core_cd_instr_prg_smoke_test)

  // --- INHERITED METHODS - UVM_COMPONENT --- //
    /** Class Constructor */
    function new(string name = "ai_core_cd_instr_prg_smoke_test", uvm_component parent=null);
      super.new(name,parent);
      uvm_top.set_timeout(3ms,1);
      `ifdef TARGET_GLS
        gls_demoter = ai_core_dwpu_gls_demoter::type_id::create("gls_demoter");
      `endif // TARGET_GLS
    endfunction: new

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
      `uvm_info("Build phase", "Entered...", UVM_LOW)
      super.build_phase(phase);

      /** Factory override of the ai core mem_manager object */
      set_type_override_by_type(ai_core_cd_mem_manager#(64, 256)::get_type(),  ai_core_cd_mem_manager__prg_smoke_test#(64, 256)::get_type(), 1'b1);
    endfunction: build_phase


endclass:ai_core_cd_instr_prg_smoke_test

`endif // AI_CORE_CD_INSTR_PRG_SMOKE_TEST_SV
