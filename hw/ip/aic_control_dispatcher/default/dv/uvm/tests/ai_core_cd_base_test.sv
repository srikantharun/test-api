`ifndef AI_CORE_CD_BASE_TEST_SV
`define AI_CORE_CD_BASE_TEST_SV


//import ai_core_cd_common_pkg::mem_access_st;

//class mem_access_st extends uvm_object;
//    bit[64-1:0] addr;  
//    bit[64-1:0] range_base;
//    bit[64-1:0] range_top;
//    int command_idx;
//    int instr_idx;
//
//    function new (string name);
//        super.new(name);
//    endfunction : new
//endclass : mem_access_st


//!!!!ToDO!!!!ToDO!!!!ToDO!!!!: remove patch after issue is closed/discussed 
class token_agent_seq_item__acd_patch extends token_agent_seq_item;
  `uvm_object_utils(token_agent_seq_item__acd_patch)

  //sanity constraint for m_bv_delay to make sure the delay is not to high
  constraint ct_delay_sanity {
    m_bv_delay == 0;  //ACD will not toggle any bus lanes untill all expected lanes have been asserted on the other end
  }

  function new (string name = "");
    super.new (name);
  endfunction : new
endclass : token_agent_seq_item__acd_patch


//!!!!ToDO!!!!ToDO!!!!ToDO!!!!: remove patch after issue is closed/discussed 
class ai_core_cd_ref_model__acd_patch extends ai_core_cd_ref_model;
  `uvm_component_utils(ai_core_cd_ref_model__acd_patch)

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual task halt_acd_execution();
    //irq_active.get(1);
    `uvm_info(get_name(), "PATCHED: halt_acd_execution", UVM_LOW)
  endtask : halt_acd_execution

  virtual task resume_acd_execution();
    //irq_active.put(1);
    `uvm_info(get_name(), "PATCHED: resume_acd_execution", UVM_LOW)
  endtask : resume_acd_execution
  
endclass : ai_core_cd_ref_model__acd_patch

//!!!!ToDO!!!!ToDO!!!!ToDO!!!!:constraints should be removed or refined with "soft" after debug / bringup is ready 
class ai_core_cd_mem_manager__base_test#(int CMD_L_MAX=64, INSTR_L_MAX=256) extends ai_core_cd_mem_manager#(.CMD_L_MAX(CMD_L_MAX), .INSTR_L_MAX(INSTR_L_MAX));
    `uvm_component_utils(ai_core_cd_mem_manager__base_test)

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

endclass : ai_core_cd_mem_manager__base_test


class ai_core_cd_axe_uvm_memory_allocator extends axe_uvm_memory_allocator;
    
    `uvm_component_utils(ai_core_cd_axe_uvm_memory_allocator)
    
    function new (string name, uvm_component parent);
        super.new(name, parent);
        policy = ALLOCATE_RANDOM;
    endfunction : new

    /* Function:start_of_simulation_phase
       UVM Start of Simulation phase

       Parameters:
        phase - UVM built-in
    */
    virtual function void start_of_simulation_phase(uvm_phase phase);
        //initialize();
    endfunction : start_of_simulation_phase
endclass : ai_core_cd_axe_uvm_memory_allocator


// AI CORE CD base test class
class ai_core_cd_base_test extends uvm_test;
  //FIELDS
    bit RAL_TEST;
    /** UVM Component Utility macro */
    `uvm_component_utils(ai_core_cd_base_test)
    uvm_phase crt_phase;
    /** Variable that allows testcase to determine if the test pass/fail if there are uvm_warnings during the execution of it.
    * By default the value is 1, which means that if there is any uvm_warning during the test, then the test will fail */
    bit use_uvm_warn_on_pass_fail=1;
     // Declare p sequencer
    // `uvm_declare_p_sequencer(axi_virtual_sequencer)
    // AI Core CD RAL Model
    aic_cd_csr_reg_block regmodel;
    /** Construct the report catcher extended class*/
    warning_catcher catcher = new();
    `ifdef TARGET_GLS
      ai_core_dwpu_gls_demoter gls_demoter;
    `endif // TARGET_GLS
    /** Instance of the environment */
    ai_core_cd_env env;

    /** Instance of the environment configuration */
    ai_core_cd_env_cfg m_env_cfg;

    /** Customized configuration */
    ai_core_cd_cust_svt_axi_system_configuration axi_cfg;

    uvm_status_e  status;

    bit [`ACD_M_AXI_DATA_WIDTH-1:0] ral_write_data;
    bit [`ACD_M_AXI_DATA_WIDTH-1:0] ral_read_data;
    bit [`ACD_M_AXI_ADDR_WIDTH-1:0] ral_read_prg_status;
    bit [`ACD_M_AXI_ADDR_WIDTH-1:0] ral_read_exe_status;
    bit [`ACD_M_AXI_ADDR_WIDTH-1:0] axi_write_addr;
    bit [`ACD_M_AXI_DATA_WIDTH-1:0] axi_write_data;
    bit [`ACD_M_AXI_ADDR_WIDTH-1:0] axi_read_addr;
    bit [`ACD_M_AXI_DATA_WIDTH-1:0] axi_read_data;

    //Axi reset sequece
    ai_core_cd_axi_simple_reset_sequence           axi_reset_seq;

    //-//axi_master_write_sequence axi_wr_seq;
    //-//axi_master_read_sequence axi_rd_seq;
    axi_master_write_random_sequence    axi_wr_rand_seq;
    axi_master_read_random_sequence     axi_rd_rand_seq;

    token_agent_cons_sequence           tok_cons_seq;
    token_agent_prod_sequence           tok_prod_seq;


  //REF MODEL FIELDS
    typedef logic [64-1:0] mem_addr_t;
    typedef logic [64-1:0] mem_data_t;
    ai_core_cd_command acd_cmd_q[$];

      int dst_id_max = 17;
      int patch_mode_max = 8;
      int patch_id_max = 16;
      int token_global_max = PROD_GLOB; 
      int token_local_max = PROD_LOC;
    //ai_core_cd_common_pkg::mem_access_st expected_instr_read_addr[$];
    //mem_access_st expected_instr_read_addr[$];
    //int expected_instr_read_addr[$];

  // --- INHERITED METHODS - UVM_COMPONENT --- //
    /** Class Constructor */
    function new(string name = "ai_core_cd_base_test", uvm_component parent=null);
      super.new(name,parent);
      uvm_top.set_timeout(3ms,1);
      `ifdef TARGET_GLS
        gls_demoter = ai_core_dwpu_gls_demoter::type_id::create("gls_demoter");
      `endif // TARGET_GLS
    endfunction: new

    virtual function void apply_test_specific_overrides();
      /** Factory override of the ai core mem_manager object */
      set_type_override_by_type(ai_core_cd_mem_manager#(64, 256)::get_type(),  ai_core_cd_mem_manager__base_test#(64, 256)::get_type(), 1'b1);
      set_type_override_by_type(ai_core_cd_ref_model::get_type(),  ai_core_cd_ref_model__acd_patch::get_type(), 1'b1);
      set_type_override_by_type(token_agent_seq_item::get_type(),  token_agent_seq_item__acd_patch::get_type(), 1'b1);
    endfunction : apply_test_specific_overrides

    // Build Phase
    virtual function void build_phase(uvm_phase phase);
      `uvm_info("Build phase", "Entered...", UVM_LOW)
      super.build_phase(phase);
      if ($test$plusargs("RAL_TEST")) RAL_TEST = 1;
      /** Add uvm_report_cb callback */
      uvm_report_cb::add(null, catcher);

      /** Factory override of the master transaction object */
      //-//set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());
      set_type_override_by_type(axe_uvm_memory_allocator::get_type(),  ai_core_cd_axe_uvm_memory_allocator::get_type(), 1'b1);     
      apply_test_specific_overrides();

      `uvm_info("build_phase", "Loaded ai_core_cd_cust_svt_axi_system_configuration ", UVM_LOW)

      /** Create the configuration object */
      axi_cfg = ai_core_cd_cust_svt_axi_system_configuration::type_id::create("axi_cfg");
      /** Call change_axi_cfg if necessary */
      change_axi_cfg();
      /** Set configuration in environment */
      uvm_config_db#(ai_core_cd_cust_svt_axi_system_configuration)::set(this, "env", "axi_cfg", this.axi_cfg);

      /** Create the configuration object for AI Core CD environment */
      m_env_cfg = ai_core_cd_env_cfg::type_id::create("m_env_cfg");
      configure_env();
      /** Set configuration for AI Core CD environment */
      uvm_config_db#(ai_core_cd_env_cfg)::set(this, "env", "m_env_cfg", this.m_env_cfg);

      /** Create the environment */
      env = ai_core_cd_env::type_id::create("env", this);
      /** Apply the default reset sequence */
      //uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());
      uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", ai_core_cd_axi_simple_reset_sequence::type_id::get());
      axi_reset_seq       = ai_core_cd_axi_simple_reset_sequence::type_id::create("rst_seq", this);

      /** Apply the Slave default response sequence to every Slave sequencer
       * Slaves will use the memory response sequence by default.  To override this behavior
       * extended tests can apply a different sequence to the Slave Sequencers.
       *
       * This sequence is configured for the run phase since the slave should always
       * respond to recognized requests.
       */
      //uvm_config_db#(uvm_object_wrapper)::set(this, "env.m_axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());
      uvm_config_db#(uvm_object_wrapper)::set(this, "env.m_axi_system_env.slave*.sequencer.run_phase", "default_sequence", ai_core_cd_axi_slave_mem_response_sequence::type_id::get());
      axi_wr_rand_seq       = axi_master_write_random_sequence::type_id::create("axi_wr_rand_seq");
      axi_rd_rand_seq       = axi_master_read_random_sequence::type_id::create("axi_rd_rand_seq");

      tok_cons_seq  = token_agent_cons_sequence::type_id::create("tok_cons_seq", this);
      tok_prod_seq  = token_agent_prod_sequence::type_id::create("tok_prod_seq", this);
      `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction: build_phase

    function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      `uvm_info("end_of_elaboration_phase", "Entered...", UVM_LOW)
      //uvm_top.print_topology(); //if needed please uncomment this line
      `uvm_info("end_of_elaboration_phase", "Exiting...", UVM_LOW)
    endfunction: end_of_elaboration_phase

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info("connect_phase", "Entered...", UVM_LOW)
      regmodel = env.m_aicd_regmodel;
      `uvm_info("connect_phase", "Exiting...", UVM_LOW)
    endfunction : connect_phase
    /**
     * Calculate the pass or fail status for the test in the final phase method of the
     * test. If a UVM_FATAL, UVM_ERROR, or a UVM_WARNING message has been generated the
     * test will fail.
     */
    function void final_phase(uvm_phase phase);
      uvm_report_server svr;
      `uvm_info("final_phase", "Entered...",UVM_LOW)

      super.final_phase(phase);

      svr = uvm_report_server::get_server();

      if (svr.get_severity_count(UVM_FATAL)
        + svr.get_severity_count(UVM_ERROR)
        //+ (svr.get_severity_count(UVM_WARNING) && use_uvm_warn_on_pass_fail) //TODO - remove this line when all warnings are fixed
          > 0)
        `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
      else
        `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

      `uvm_info("final_phase", "Exiting...", UVM_LOW)
    endfunction: final_phase

    virtual function void phase_started(uvm_phase phase);
      super.phase_started(phase);
      crt_phase = phase;
    endfunction : phase_started

    function void start_of_simulation_phase (uvm_phase phase);
      super.start_of_simulation_phase(phase);
      // set env in config db to be retrieved by non uvm components like report catcher and sequences
      uvm_config_db#(ai_core_cd_env_cfg)::set(null,"*", "AI_CORE_CD_ENV_CFG", env.env_cfg);
      `ifdef TARGET_GLS
        uvm_report_cb::add(null, gls_demoter); // only add after setting env cfg, else, it will FATAL error not getting the cfg at time 0
      `endif // TARGET_GLS
      `uvm_info("start_of_simulation_phase", "done", UVM_LOW)
    endfunction: start_of_simulation_phase

  // --- TEST METHODS --- //
    virtual function void change_axi_cfg();
      //this should be overwritten on the extended testcases
    endfunction : change_axi_cfg


    virtual function void configure_env();
      m_env_cfg.ral_test = RAL_TEST;
      m_env_cfg.aicd_ref_model_cfg.tkn_consume_produce_parity_en = 0; //CHECK #PROD == #CONS

      m_env_cfg.aicd_ref_model_cfg.local_token_line_num = 17;
      m_env_cfg.aicd_ref_model_cfg.global_token_line_num = 7;
      m_env_cfg.aicd_ref_model_cfg.fill_counter_num = 17;
    endfunction : configure_env

    virtual task reset_cd_env();
      //-//-> env.dwpu_scb.m_rst_evt;
      //-//@(posedge env.m_axi_system_env.vif.common_aclk);
      //-//-> env.dwpu_scb.m_rst_done_evt;
      //-//env.dwpu_mdl.reset();
    endtask


    task check_exec_done(int num_cycles=50);
      bit [63:0] read_data;
      uvm_status_e read_status;
      read_data = ~0;
      //wait program done by checking IDLE bit
      //repeat(num_cycles) @(posedge env.m_axi_system_env.vif.common_aclk);
      //repeat(num_cycles) @(env.aic_cd_agt.vif.mon);
      repeat(num_cycles) @(posedge env.aic_cd_agt.vif.clk);
      //-////wait for idle = 1 : program is done
      //-//while (|read_data[1:0]) begin // IDLE state == 0
      //-//  regmodel.cmdblk_status.read(read_status, read_data);
      //-//  repeat(100) @(posedge env.m_axi_system_env.vif.common_aclk);
      //-//end
      `uvm_info ("check_exec_done", $sformatf("Program finished, AIC CD in IDLE"), UVM_HIGH)
    endtask // check_exec_done


    virtual function void cfg_token_scb_comp_min();
      for (int i=0; i<m_env_cfg.aicd_ref_model_cfg.local_token_line_num; i++)
      begin
        env.aicd_local_tkn_scb[i].comp_min = 0;
      end

      for (int i=0; i<m_env_cfg.aicd_ref_model_cfg.global_token_line_num; i++)
      begin
        env.aicd_global_tkn_scb[i].comp_min = 0;
      end
    endfunction : cfg_token_scb_comp_min


    virtual task run_phase(uvm_phase phase);
      uvm_objection m_uvm_objection;
      
      super.run_phase(phase);
  
      phase.get_objection().set_drain_time(this, 150);
      phase.raise_objection(this);

      //remove token scbd comp min for non token tests 
      cfg_token_scb_comp_min();

      // -- REF MODEL METHODS --
      fork begin
        fork begin 
          execute_command_from_fifo();
        end join_none
      end join

      //----

      // Call start method to start built-in sequences.
      `uvm_info(get_name(), "Before sequence start", UVM_LOW)

      // Start reset sequence on the sequencer
      if(!axi_reset_seq.randomize()) `uvm_error(get_name, "axi_reset_seq randomization error!");
      axi_reset_seq.start(env.sequencer);

      `uvm_info(get_name(), "After sequence start", UVM_LOW)

      //Status CSR access 
      //read_reg();

      //Reg check: HW_RST, BIT_BASH, ACCESS
      //check_regs();

      //Initialize ACD registers
      init_acd_regs();
      //send_acd_command();

      `uvm_info(get_name(), "START sending commands to ACD", UVM_LOW)
      send_acd_commands();
      `uvm_info(get_name(), "END   sending commands to ACD", UVM_LOW)


      //`uvm_info(get_name(), "Printing RegModel", UVM_LOW)
      //regmodel.print();
  
      check_exec_done(500);

      phase.drop_objection(this);

      #10us;

      m_uvm_objection = phase.get_objection();
      `uvm_info(get_name(), $sformatf("Objection that gates run_phase is %0p",m_uvm_objection), UVM_LOW)


      m_uvm_objection.display_objections();

      `uvm_info(get_name(), "Run phase exited", UVM_LOW)
    endtask : run_phase 


   // --- REG METHODS --- //
    task read_reg();
      bit [63:0] read_data;
      uvm_status_e read_status;
      read_data = ~0;
      regmodel.status_busy.read(read_status, read_data);

      `uvm_info ("read_reg_done", $sformatf("Read register finished | Status: %p | Data: %0h",read_status,read_data), UVM_LOW)
    endtask // read_reg

    task check_regs();
      uvm_reg_mem_built_in_seq m_ral_seq;
      m_ral_seq = uvm_reg_mem_built_in_seq::type_id::create("m_ral_seq",,get_full_name());
      // =======================================================================================================================
      // CD RAL model
      // =======================================================================================================================
      m_ral_seq.model = regmodel;

      m_ral_seq.tests = (UVM_DO_REG_HW_RESET | UVM_DO_REG_BIT_BASH | UVM_DO_REG_ACCESS);
      m_ral_seq.start(null);
    endtask : check_regs

    task init_acd_regs();
      uvm_status_e status;
      int num_fifo_lines;
      int bytes_per_line;

      //ToDO: Memory manager has to be generated/initialized before the registers are configured (dst addr cmd / prg) 

      //ctrl_data_base_addr;
      `uvm_info(get_name(), "Configuring CTRL DATA Base Addr", UVM_LOW)
      regmodel.ctrl_data_base_addr.ctrl_data_base_addr.write(status, 0);

      //command_status; (RO)
      //status_busy; (RO)
      //hw_capability_params;
      //hw_capability_fifos;
      //patch_mode[8];
      //patch_table[16];
      //dst_addr_command[17];
      //dst_addr_program[17];
      
      `uvm_info(get_name(), "Configuring DST Cmd Block params", UVM_LOW)
      foreach (regmodel.dst_cmdblock_params[i]) begin //ToDO: randomize values 
        num_fifo_lines = 15; //+i;
        bytes_per_line = 8;  //+i*3;
        regmodel.dst_cmdblock_params[i].num_fifo_lines.write(status, num_fifo_lines);
        regmodel.dst_cmdblock_params[i].bytes_per_line.write(status, bytes_per_line);
        env.aicd_refmodel.fill_counter[i].put(num_fifo_lines*bytes_per_line);
        `uvm_info(get_name(), $sformatf("Init max capacity for fill_counter[%0d]: %0d",i,num_fifo_lines*bytes_per_line), UVM_LOW)
      end
      
      //status_fill_counter[17]; (RO)
      //irq_en;
      env.aicd_refmodel.mirror_irq_en();
      //irq_status; (RO)
      env.aicd_refmodel.mirror_irq_status();
      //error_cause; (RO)

      //command_control;
      `uvm_info(get_name(), "Configuring CMD Control", UVM_LOW)
      //regmodel.command_control.exec_en.write(status, 1);
      regmodel.command_control.write(status, 1);
    endtask : init_acd_regs

  // --- ENV METHODS --- //
    virtual task send_acd_commands();
      ai_core_cd_command crt_cmd;

      //foreach commands in command list 
      foreach (env.m_mem_manager.command_list[cmd_idx])
      begin 
        crt_cmd = env.m_mem_manager.command_list[cmd_idx];

        //push command to FIFO  //ToDO: when burst commands are implemented we have to accurated increment the space in FIFO model and also review the CMD drop logic (i.e. if FIFO has room for 5 commands but 6 are sent, does it drop all or just the last?)
        add_command_to_fifo(crt_cmd, cmd_idx);

        //start send_command_on_bus 
        //fork begin
        //  fork begin
            send_command_on_bus(crt_cmd);  //ToDO: this sends the commands 1 by 1 on the bus | should implement a task which is able to group multiple commands in a single AXI trans
        //  end join_none
        //end join


        //execute_command
        //execute_command(crt_cmd, cmd_idx);

        //wait delay

      end 
    endtask : send_acd_commands



    virtual function bit command_is_valid(ai_core_cd_command acd_cmd, int cmd_idx);
      bit cmd_valid = 1;
      //ToDO: implement this method 
      //if command is not valid we should set and start the appropriate IRQ status fields  and start checking and service routines

      if (acd_cmd.length == 0) begin 
        env.aicd_refmodel.set_irq_status("COMMAND_EMPTY_TASK_LIST");  //handle_irq_status();
        cmd_valid = 0;
      end 


      if (cmd_valid == 0) begin 
        env.aicd_refmodel.set_irq_status("COMMAND_DROPPED");  //handle_irq_status();
      end 

      return cmd_valid;
    endfunction : command_is_valid


    virtual function bit instruction_is_valid(ai_core_cd_instruction instr, int cmd_idx);
      bit instr_is_valid;
      //ToDO: implement this method 
      case (instr.instr_type) 
        CMD : instr_is_valid = instr_cmd_is_valid(instr, cmd_idx); 
        PRG : instr_is_valid = instr_prg_is_valid(instr, cmd_idx);
        TKN : instr_is_valid = instr_tkn_is_valid(instr, cmd_idx);
        TMS : instr_is_valid = instr_tms_is_valid(instr, cmd_idx); 
        default : `uvm_fatal("REF_MODEL","The type of this instruction is unknown")
      endcase

      //if instruction is not valid we should set and start the appropriate IRQ status fields  and start checking and service routines
      return instr_is_valid;
    endfunction : instruction_is_valid

    
    virtual function bit instr_cmd_is_valid(ai_core_cd_instruction instr, int cmd_idx);
      bit instr_is_valid = 1;
      ai_core_cd_cmd_instr cmd_instr;

      `uvm_info(get_name(), $sformatf("Entered instr_cmd_is_valid"), UVM_LOW)
      
      if (!$cast(cmd_instr, instr))
        `uvm_fatal("REF_MODEL",$sformatf("Cast was not succesfull for ai_core_cd_cmd_instr \ instr_type: %0p",instr.instr_type))

      //check for the different irq conditions

      if (cmd_instr.dst_id >= dst_id_max) begin
        //irq_status["INSTR_DST_ID_MAPPING"]          = data_from_reg[5];
        env.aicd_refmodel.set_irq_status("INSTR_DST_ID_MAPPING");  //handle_irq_status();
        instr_is_valid = 0;
      end 
      if (cmd_instr.patch_mode > patch_mode_max) begin
        //irq_status["INSTR_PATCH_MODE_MAPPING"]      = data_from_reg[6]; 
        env.aicd_refmodel.set_irq_status("INSTR_PATCH_MODE_MAPPING");  //handle_irq_status();
        instr_is_valid = 0;
      end 
      if (cmd_instr.patch_id0 > patch_id_max) begin
        //irq_status["INSTR_PATCH_ID_0_MAPPING"]      = data_from_reg[7]; 
        env.aicd_refmodel.set_irq_status("INSTR_PATCH_ID_0_MAPPING");  //handle_irq_status();
        instr_is_valid = 0;
      end 
      if (cmd_instr.patch_id1 > patch_id_max) begin
        //irq_status["INSTR_PATCH_ID_1_MAPPING"]      = data_from_reg[8]; 
        env.aicd_refmodel.set_irq_status("INSTR_PATCH_ID_1_MAPPING");  //handle_irq_status();
        instr_is_valid = 0;
      end 
      if (cmd_instr.cmd_ptr[2:0] != 0) begin
        //irq_status["COPY_DATA_MISALIGNED"]          = data_from_reg[14]
        //"A copy command has the data not byte aligned. The Copy operation was dropped!" //ToDO: cmd/prg or both?? Byte aligned or word aligned? PRG can copy data from a non word aligend address.
        env.aicd_refmodel.set_irq_status("COPY_DATA_MISALIGNED");  //handle_irq_status();
        instr_is_valid = 0;
      end 

      return instr_is_valid;
    endfunction : instr_cmd_is_valid


    virtual function bit instr_prg_is_valid(ai_core_cd_instruction instr, int cmd_idx);
      bit instr_is_valid = 1;
      ai_core_cd_prg_instr prg_instr;

      `uvm_info(get_name(), $sformatf("Entered instr_prg_is_valid"), UVM_LOW)
      
      if (!$cast(prg_instr, instr))
        `uvm_fatal("REF_MODEL",$sformatf("Cast was not succesfull for ai_core_cd_prg_instr \ instr_type: %0p",instr.instr_type))

      //check for the different irq conditions

      if (prg_instr.dst_id >= dst_id_max) begin
        //irq_status["INSTR_DST_ID_MAPPING"]          = data_from_reg[5]
        env.aicd_refmodel.set_irq_status("INSTR_DST_ID_MAPPING");  //handle_irq_status();
        instr_is_valid = 0;
      end 
      if (prg_instr.prg_ptr[2:0] != prg_instr.dst_addr[2:0]) begin
        //irq_status["COPY_DATA_MISALIGNED"]          = data_from_reg[14]
        //"A copy command has the data not byte aligned. The Copy operation was dropped!" //ToDO: cmd/prg or both?? Byte aligned or word aligned? PRG can copy data from a non word aligend address.
        env.aicd_refmodel.set_irq_status("COPY_DATA_MISALIGNED");  //handle_irq_status();
        instr_is_valid = 0;
      end 

      return instr_is_valid;
    endfunction : instr_prg_is_valid


    virtual function bit instr_tkn_is_valid(ai_core_cd_instruction instr, int cmd_idx);
      bit instr_is_valid = 1;
      ai_core_cd_token_instr tkn_instr;
      int mapped_local_tokens;
      int unmapped_local_tokens;
      int mapped_global_tokens;
      int unmapped_global_tokens;

      `uvm_info(get_name(), $sformatf("Entered instr_tkn_is_valid"), UVM_LOW)
      `uvm_info("MEM_MANAGER",$sformatf("TKN Instr : %0p",instr.sprint()),UVM_LOW)

      if (!$cast(tkn_instr, instr))
        `uvm_fatal("REF_MODEL",$sformatf("Cast was not succesfull for ai_core_cd_token_instr \ instr_type: %0p",instr.instr_type))

      //check for the different irq conditions

      if (tkn_instr.token_type > token_global_max) begin
        //irq_status["INSTR_TOKEN_ILLEGAL_OPCODE"]    = data_from_reg[9]; 
        env.aicd_refmodel.set_irq_status("INSTR_TOKEN_ILLEGAL_OPCODE");  //handle_irq_status();
        instr_is_valid = 0;
      end 
      mapped_local_tokens = tkn_instr.token_num[17-1:0];
      mapped_global_tokens = tkn_instr.token_num[7-1:0];
      unmapped_local_tokens = tkn_instr.token_num>>17;
      unmapped_global_tokens = tkn_instr.token_num>>7;
      
      if (tkn_instr.token_type <= token_local_max) begin
        if (mapped_local_tokens == 0) begin
          //irq_status["INSTR_TOKEN_LOCAL_MAP_EMPTY"]   = data_from_reg[10];
          env.aicd_refmodel.set_irq_status("INSTR_TOKEN_LOCAL_MAP_EMPTY");  //handle_irq_status();
          instr_is_valid = 0;
        end 
        if (unmapped_local_tokens > 0) begin
          //irq_status["INSTR_TOKEN_LOCAL_MAPPING"]     = data_from_reg[12];
          env.aicd_refmodel.set_irq_status("INSTR_TOKEN_LOCAL_MAPPING");  //handle_irq_status();
          instr_is_valid = 0;
        end 
      end 
      else begin 
        if (mapped_global_tokens == 0) begin
          //irq_status["INSTR_TOKEN_GLOBAL_MAP_EMPTY"]  = data_from_reg[11];
          env.aicd_refmodel.set_irq_status("INSTR_TOKEN_GLOBAL_MAP_EMPTY");  //handle_irq_status();
          instr_is_valid = 0;
        end 
        if (unmapped_global_tokens > 0) begin
          //irq_status["INSTR_TOKEN_GLOBAL_MAPPING"]    = data_from_reg[13];
          env.aicd_refmodel.set_irq_status("INSTR_TOKEN_GLOBAL_MAPPING");  //handle_irq_status();
          instr_is_valid = 0;
        end 
      end

      
      //OBSOLETE CODE - CAN DELETE
      //if (mapped_tokens == 0) begin
      //  if (tkn_instr.token_type <= token_local_max) begin
      //    //irq_status["INSTR_TOKEN_LOCAL_MAP_EMPTY"]   = data_from_reg[10];
      //    env.aicd_refmodel.set_irq_status("INSTR_TOKEN_LOCAL_MAP_EMPTY");  //handle_irq_status();
      //  end 
      //  else begin 
      //    //irq_status["INSTR_TOKEN_GLOBAL_MAP_EMPTY"]  = data_from_reg[11];
      //    env.aicd_refmodel.set_irq_status("INSTR_TOKEN_GLOBAL_MAP_EMPTY");  //handle_irq_status();
      //  end
      //  instr_is_valid = 0;
      //end 
      //unmapped_local_tokens = tkn_instr.token_num>>17;
      //unmapped_global_tokens = tkn_instr.token_num>>7;
      //if (unmapped_tokens >= 0) begin
      //  if (tkn_instr.token_type <= token_local_max) begin
      //    //irq_status["INSTR_TOKEN_LOCAL_MAPPING"]     = data_from_reg[12];
      //    env.aicd_refmodel.set_irq_status("INSTR_TOKEN_LOCAL_MAPPING");  //handle_irq_status();
      //  end
      //  else begin 
      //    //irq_status["INSTR_TOKEN_GLOBAL_MAPPING"]    = data_from_reg[13];
      //    env.aicd_refmodel.set_irq_status("INSTR_TOKEN_GLOBAL_MAPPING");  //handle_irq_status();
      //  end
      //  instr_is_valid = 0;
      //end 
      

      //ToDO: make sure this code is added in TB/REF MODEL
      //if (tkn_instr.dst_id >= dst_id_max) begin
      //  irq_status["DBG_SW_INTERRUPT"]              = data_from_reg[32];
      //  env.aicd_refmodel.set_irq_status("DBG_SW_INTERRUPT");  //handle_irq_status();
      //  instr_is_valid = 0;
      //end 

      return instr_is_valid;
    endfunction : instr_tkn_is_valid


    virtual function bit instr_tms_is_valid(ai_core_cd_instruction instr, int cmd_idx);
      bit instr_is_valid = 1;
      ai_core_cd_timestamp_instr tms_instr;

      `uvm_info(get_name(), $sformatf("Entered instr_tms_is_valid"), UVM_LOW)
      
      if (!$cast(tms_instr, instr))
        `uvm_fatal("REF_MODEL",$sformatf("Cast was not succesfull for ai_core_cd_timestamp_instr \ instr_type: %0p",instr.instr_type))

      //ToDO: check for the different irq conditions

      
      //handle_irq_status(); //this has to be started whether instr are valid or not because of IRQ functionality

      return instr_is_valid;
    endfunction : instr_tms_is_valid


    //starts IRQ checking and service routines
    virtual task handle_irq_status();
      //ToDO: implement this method 

      //class aic_cd_csr_reg_irq_en extends dv_base_reg;
        //// fields
        //rand dv_base_reg_field task_list_done;
        //rand dv_base_reg_field command_dropped;
        //rand dv_base_reg_field command_empty_task_list;
        //rand dv_base_reg_field instr_axi_resp_slverr;
        //rand dv_base_reg_field instr_axi_resp_decerr;
        //rand dv_base_reg_field instr_dst_id_mapping;
        //rand dv_base_reg_field instr_patch_mode_mapping;
        //rand dv_base_reg_field instr_patch_id_0_mapping;
        //rand dv_base_reg_field instr_patch_id_1_mapping;
        //rand dv_base_reg_field instr_token_illegal_opcode;
        //rand dv_base_reg_field instr_token_local_map_empty;
        //rand dv_base_reg_field instr_token_global_map_empty;
        //rand dv_base_reg_field instr_token_local_mapping;
        //rand dv_base_reg_field instr_token_global_mapping;
        //rand dv_base_reg_field copy_data_misaligned;
        //rand dv_base_reg_field copy_fill_counter_done_pop;
        //rand dv_base_reg_field copy_fill_counter_overflow;
        //rand dv_base_reg_field copy_axi_read_resp_slverr;
        //rand dv_base_reg_field copy_axi_read_resp_decerr;
        //rand dv_base_reg_field copy_axi_write_resp_slverr;
        //rand dv_base_reg_field copy_axi_write_resp_decerr;
        //rand dv_base_reg_field dbg_sw_interrupt;

    endtask : handle_irq_status


    virtual task execute_command(ai_core_cd_command acd_cmd, int cmd_idx);
      mem_access_st mem_access;
      mem_addr_t start_word_addr;
      mem_addr_t end_word_addr;
      bit instr_is_valid;
      int exp_addr_range_q[$];
      string pstr;
      
      `uvm_info("REF_MODEL", $sformatf("START   Execute command for cmd idx:%0d", cmd_idx), UVM_LOW)

      if (acd_cmd.length == 0)
      begin
        `uvm_info(get_name(), $sformatf("Not executing command due to length 0 ",), UVM_LOW)
        return;
      end

      if (command_is_valid(acd_cmd, cmd_idx) == 0)
      begin
        `uvm_info(get_name(), $sformatf("Not executing command because of properties displayed above ",), UVM_LOW)
        return;
      end

      //add to the expected x_ID read addr range to Memory 
      start_word_addr = acd_cmd.task_list_ptr;
      end_word_addr = start_word_addr + 8 * (acd_cmd.length-1);

      for (int addr=start_word_addr; addr<=end_word_addr; addr=addr+8)
      begin 
        //mem_access = new("mem_access");
        mem_access.addr = addr;
        mem_access.range_base  = start_word_addr;
        mem_access.range_top   = end_word_addr;
        mem_access.command_idx = cmd_idx;
        mem_access.instr_idx   = -1; //signals this mem access was not triggered by instruction

        env.m_mem_manager.exp_instr_rd_addr_q.push_back(mem_access);
        exp_addr_range_q.push_back(mem_access.addr);

      end 
      
      
      $swriteh(pstr,"%0p", exp_addr_range_q);
      `uvm_info(get_name(), $sformatf("expected_instr_read_addr_q added expected_addr_range: %s \n expected_instr_read_addr_q : %p", pstr, env.m_mem_manager.exp_instr_rd_addr_q), UVM_LOW)
      foreach (env.m_mem_manager.exp_instr_rd_addr_q[i])
        `uvm_info(get_name(), $sformatf("expected_instr_read_addr_q[%0d]: %h", i, env.m_mem_manager.exp_instr_rd_addr_q[i]), UVM_LOW)
      
      //push command in the queue and/or increment counter 
      env.m_mem_manager.command_q_count++;

      //ToDO: this should probably be a different task which goes through the instructions 1 by 1 since another CMD can start the instr fetch process at the same time
      //    : push the instructions in a FIFO and execute them from there
      //foreach instr_idx inside command 
      foreach (acd_cmd.instr_idxs[idx]) begin
        ai_core_cd_instruction aicd_instr;
        //execute_instruction(get_instruction_idx(acd_cmd.instr_idxs[idx], acd_cmd.command_id, acd_cmd.command_idx));
        `uvm_info("REF_MODEL", $sformatf("START Execute instr idx:%0d for cmd idx:%0d", acd_cmd.instr_idxs[idx], cmd_idx), UVM_LOW)
        
        aicd_instr = get_instruction_idx(acd_cmd.instr_idxs[idx]);
        //`uvm_info("MEM_MANAGER",$sformatf("Instr before clone : %0p",aicd_instr.sprint()),UVM_LOW)
        $cast(aicd_instr, get_instruction_idx(acd_cmd.instr_idxs[idx]).clone());
        `uvm_info("MEM_MANAGER",$sformatf("Instr after  clone : %0p",aicd_instr.sprint()),UVM_LOW)
        aicd_instr.command_ids  = {acd_cmd.command_id};
        aicd_instr.command_idxs = {cmd_idx};

        //ToDO: add last instruction from current command indication to instr field -> will help with irq logic
        //aicd_instr.last_in_set = (idx == last_idx);

        instr_is_valid = instruction_is_valid(aicd_instr, cmd_idx);

        //execute instruction  //
        if (instr_is_valid) begin
          execute_instruction(aicd_instr, cmd_idx);
        end
        `uvm_info("REF_MODEL", $sformatf("END   Execute instr idx:%0d for cmd idx:%0d", acd_cmd.instr_idxs[idx], cmd_idx), UVM_LOW)
      end

      //when all of the instructions from the crt command have been completed we can assert the TASK LIST DONE IRQ
       env.aicd_refmodel.set_irq_status("TASK_LIST_DONE");  //handle_irq_status(); 
    
      
      `uvm_info("REF_MODEL", $sformatf("END   Execute command for cmd idx:%0d", cmd_idx), UVM_LOW)
    
    endtask : execute_command


    function ai_core_cd_instruction get_instruction_idx(int instr_idx);
        return env.m_mem_manager.task_list.instr_list[instr_idx];
    endfunction : get_instruction_idx

    //function ai_core_cd_instruction get_instruction_idx(int instr_idx, cmd_id, cmd_idx);
    //    ai_core_cd_instruction instr;
    //    instr = env.m_mem_manager.task_list.instr_list[instr_idx].deep_copy();
    //    instr.command_ids.delete(); instr.command_ids.push_back();
    //    instr.command_idxs.delete();
    //    return instr;
    //endfunction : get_instruction_idx


    virtual task send_command_on_bus(ai_core_cd_command acd_cmd);
      axi_master_write_random_sequence      axi_seq;

      bit                                   cmd_bits[];
      bit [63:0]                            packed_cmd; 
      int                                   cmds_num = 1;       

      axi_seq  = axi_master_write_random_sequence::type_id::create("axi_seq");

      acd_cmd.pack(cmd_bits);
      packed_cmd = {>>{cmd_bits}};
      `uvm_info(get_name(), $sformatf("SCB - Command to be sent is :\n %p",acd_cmd.sprint()), UVM_LOW)
      //`uvm_info(get_name(), $sformatf("Gen command bits:\n %p",cmd_bits), UVM_LOW)
      //`uvm_info(get_name(), $sformatf("Gen command bytes:\n %h",packed_cmd), UVM_LOW)



      assert(axi_seq.randomize() with {
                                          //sequence_length      == (req.length);
                                          sequence_length      == cmds_num; //1 command  (toDO: create command list to send burst of commands )
                                          burst_length         == 1; //toDO: randomize between burst and seqlen to decide the number of commands
                                          max_bw               == 8;
                                          //cfg_addr             == (req.task_list_ptr);
                                          cfg_addr             == ACD_CMD_ST_ADDR;
                                          burst_size           == svt_axi_transaction::BURST_SIZE_64BIT;
                                          burst_type           inside {svt_axi_transaction::FIXED, svt_axi_transaction::INCR};       //ToDO: this should be randomized -- ACD could support other burst types as well 
                                          atomic_type          inside {svt_axi_transaction::NORMAL}; // svt_axi_transaction::EXCLUSIVE --- not suppoerted in ACD
                                          //burst_type           == svt_axi_transaction::INCR; //ToDO leave it at incremental ar randomize it within the modes
                                          min_addr_valid_delay == 0;
                                          max_addr_valid_delay == 16;
                                          min_bready_delay     == 0;
                                          max_bready_delay     == 16;
                                          //foreach(cfg_data[j]) { cfg_data[j] == {cmd_bits}; }
                                          cfg_data.size()      == cmds_num;
                                          foreach(cfg_data[j]) { cfg_data[j] == packed_cmd; }
      });
      axi_seq.print();
      crt_phase.raise_objection(this);
      axi_seq.start(env.m_axi_system_env.master[0].sequencer);
      crt_phase.drop_objection(this);

      //print 

      //wait delay ToDO: add random delay 

      //force hdl_top.dut.u_cmdblock_cmd_fifo.snd_wrd_incr
    endtask : send_command_on_bus


    virtual task send_acd_command();
      axi_master_write_random_sequence      axi_seq;
      ai_core_cd_command                    acd_cmd;
      bit                                   cmd_bits[];
      bit [63:0]                            packed_cmd; 
      int                                   cmds_num = 2;       

      axi_seq  = axi_master_write_random_sequence::type_id::create("axi_seq");
      acd_cmd  = ai_core_cd_command::type_id::create("acd_cmd");

      //acd_cmd.c_reserved_default.constraint_mode(0);
      if (!acd_cmd.randomize() with {
        task_list_ptr == 0;
        length == 2;
        control_offset == 'h0;
      }) `uvm_warning("RANDOMIZE FAIL","Was not able to randomize command with given constraints")

      acd_cmd.pack(cmd_bits);
      packed_cmd = {>>{cmd_bits}};
      `uvm_info(get_name(), $sformatf("Gen command is:\n %p",acd_cmd), UVM_LOW)
      `uvm_info(get_name(), $sformatf("Gen command bits:\n %p",cmd_bits), UVM_LOW)
      `uvm_info(get_name(), $sformatf("Gen command bytes:\n %h",packed_cmd), UVM_LOW)



      assert(axi_seq.randomize() with {
                                          //sequence_length      == (req.length);
                                          sequence_length      == cmds_num; //1 command  (toDO: create command list to send burst of commands )
                                          burst_length         == 1; //toDO: randomize between burst and seqlen to decide the number of commands
                                          max_bw               == 8;
                                          //cfg_addr             == (req.task_list_ptr);
                                          cfg_addr             == ACD_CMD_ST_ADDR;
                                          burst_size           == svt_axi_transaction::BURST_SIZE_64BIT;
                                          burst_type           == svt_axi_transaction::FIXED;
                                          //burst_type           == svt_axi_transaction::INCR; //ToDO leave it at incremental ar randomize it within the modes
                                          min_addr_valid_delay == 0;
                                          max_addr_valid_delay == 16;
                                          min_bready_delay     == 0;
                                          max_bready_delay     == 16;
                                          //foreach(cfg_data[j]) { cfg_data[j] == {cmd_bits}; }
                                          cfg_data.size()      == cmds_num;
                                          foreach(cfg_data[j]) { cfg_data[j] == packed_cmd; }
      });
      axi_seq.print();
      axi_seq.start(env.m_axi_system_env.master[0].sequencer);

      //print 

      //wait 

      //force hdl_top.dut.u_cmdblock_cmd_fifo.snd_wrd_incr
    endtask : send_acd_command

  // --- REF MODEL METHODS --- //
    //ToDO: to be added later on when we would like to loosely model the instruction FIFO 
    virtual task add_command_to_fifo(ai_core_cd_command acd_cmd, int cmd_idx);
      ai_core_cd_command crt_cmd;
      int cmd_fifo_depth = 16;
      
      //wait until fifo has enough space - NOT NEEDED - ACD discards incomming command as to not block the AXI bus
      

      //if there is not enough room inside ACD then discard the command 
      //TODO: this can lead to cycle accuracy issues -> find a way to sync with the RTL whether it discard the incoming command or not or mark the incomming as POSSIBLY_DROPPED (gray area mechanism)
      
      //if (acd_cmd_q.size() > cmd_fifo_depth) begin
      if (env.m_mem_manager.command_q_count > cmd_fifo_depth) begin  //command_q_count has a better cycle accuracy then acd_cmd_q.size() because it is decreased on SVT callback 
        `uvm_info(get_name(), $sformatf("CMD FIFO FULL: Command queue has %0d items stored and command_q_count=", acd_cmd_q.size(), env.m_mem_manager.command_q_count), UVM_LOW)
        env.aicd_refmodel.set_irq_status("COMMAND_DROPPED"); //handle_irq_status();
      end 
      else begin
        //push instruction to the FIFO 
        `uvm_info(get_name(), $sformatf("PUSHING CMD to FIFO: Command queue has %0d items stored and command_q_count=", acd_cmd_q.size(), env.m_mem_manager.command_q_count), UVM_LOW)
        crt_cmd = acd_cmd;
        crt_cmd.command_idx = cmd_idx;
        acd_cmd_q.push_back(crt_cmd);
      end 
    endtask : add_command_to_fifo


    //ToDO: to be added later on when we would like to loosely model the instruction FIFO 
    virtual task execute_command_from_fifo();
      ai_core_cd_command crt_cmd;
      
      forever begin
        //wait fifo not empty 
        wait (acd_cmd_q.size() != 0);
        
        if (env.aicd_refmodel.irq_active.try_get(1)==0) begin
          `uvm_info(get_name(), $sformatf("Command queue has %0d items stored - STALLING execution until IRQ cleared", acd_cmd_q.size()), UVM_LOW)
          //stall command execution if IRQ active 
          env.aicd_refmodel.irq_active.get(1);
          env.aicd_refmodel.irq_active.put(1);
        end 
        else begin 
          `uvm_info(get_name(), $sformatf("Command queue has %0d items stored", acd_cmd_q.size()), UVM_LOW)
          env.aicd_refmodel.irq_active.put(1);
        end

        //pop command from fifo
        crt_cmd = acd_cmd_q.pop_front();

        //execute command
        execute_command(crt_cmd, crt_cmd.command_idx);
      end
    endtask : execute_command_from_fifo

    //ToDO: to be added later on when we would like to loosely model the instruction FIFO 
    virtual task add_instr_to_fifo();//instr);
      //wait until fifo has enough space 

      //push instruction to the FIFO 
    endtask : add_instr_to_fifo

    //ToDO: to be added later on when we would like to loosely model the instruction FIFO 
    virtual task execute_instr_from_fifo();
      forever begin
        #1ms;

        //wait fifo not empty 
        //pop isntr from fifo
        //execute instruction
      end
    endtask : execute_instr_from_fifo


    virtual task execute_instruction(ai_core_cd_instruction instr, int cmd_idx);
      //`uvm_info(get_name(), $sformatf("Instruction that will be executed is :\n %s",instr.sprint()), UVM_LOW)
      case (instr.instr_type) 
        CMD : execute_cmd_instruction(instr, cmd_idx); 
        PRG : execute_prg_instruction(instr, cmd_idx);
        TKN : execute_tkn_instruction(instr, cmd_idx);
        TMS : execute_tms_instruction(instr, cmd_idx); 
        default : `uvm_fatal("REF_MODEL","The type of this instruction is unknown")
      endcase
    endtask : execute_instruction


    //returns configured addr map from RAL for the specified target
    virtual function bit[64-1:0] get_target_addr_for_dst_id();
      //ToDO: implement this method
      return 0;
    endfunction 


    virtual function void add_exp_mem_access_to_queue(mem_addr_t start_addr, mem_addr_t end_addr,ref mem_access_st exp_q[$], input string q_name, int cmd_idx, int instr_idx=-1, int increment=8);
      mem_access_st mem_access;
      int aligned_st_addr;
      int aligned_en_addr;
      int computed_en_addr;
      int access_num;
      int exp_addr_range_q[$];
      string pstr;

      //this logic does not account for the extra transaction that is occuring with unaligned addressing
      //for (int addr=start_addr; addr<=end_addr; addr=addr+increment)
      //begin 
      //  //mem_access = new("mem_access");
      //  mem_access.addr = addr;
      //  mem_access.range_base  = start_addr;
      //  mem_access.range_top   = end_addr;
      //  mem_access.command_idx = cmd_idx;
      //  mem_access.instr_idx   = instr_idx;   // instr_idx==-1 signals that this mem access was not triggered by instruction
      //
      //  exp_q.push_back(mem_access);
      //  exp_addr_range_q.push_back(mem_access.addr);
      //end 

      //this logic applies for unaligned addressing but only for increments of 8 (or more generally increment with power of 2s)
      aligned_st_addr = start_addr >> 3;
      aligned_st_addr = aligned_st_addr << 3; //this is added to account for the unaligned addressing -> which can produce 1 extra access
      aligned_en_addr = end_addr >> 3;
      aligned_en_addr = aligned_en_addr << 3; //this is added to account for the unaligned addressing -> which can produce 1 extra access
      aligned_en_addr+= increment;  //this is added because length is expressed in bytes and initial end_addr == start_addr + length -1. Adresses reflect words on the other hand
      access_num = (aligned_en_addr-aligned_st_addr)/increment;

      computed_en_addr = start_addr+(access_num-1)*increment;
      
      `uvm_info(get_name(), $sformatf("aligned_st_addr_h: %0h | aligned_en_addr: %0h | computed_en_addr: %0h | access_num: %0d | ",aligned_st_addr, aligned_en_addr, computed_en_addr, access_num), UVM_LOW)
      `uvm_info(get_name(), $sformatf("aligned_st_addr_d: %0d | aligned_en_addr: %0d | computed_en_addr: %0d | access_num: %0d | ",aligned_st_addr, aligned_en_addr, computed_en_addr, access_num), UVM_LOW)


      for (int access=0; access<access_num; access+=1)
      begin 
        //mem_access = new("mem_access");
        mem_access.addr = start_addr+access*increment;
        mem_access.range_base  = start_addr;
        mem_access.range_top   = computed_en_addr;
        mem_access.command_idx = cmd_idx;
        mem_access.instr_idx   = instr_idx;   // instr_idx==-1 signals that this mem access was not triggered by instruction
      
        exp_q.push_back(mem_access);
        exp_addr_range_q.push_back(mem_access.addr);
      end 

      
      $swriteh(pstr,"%0p", exp_addr_range_q);
      `uvm_info(get_name(), $sformatf("%s added expected_addr_range: %s \n %0s : %p", q_name, pstr, q_name, exp_q), UVM_LOW)
      foreach (exp_q[i])
        `uvm_info(get_name(), $sformatf("%0s[%0d]: %p", q_name, i, exp_q[i]), UVM_LOW)
    endfunction : add_exp_mem_access_to_queue


    virtual function int get_endp_fill_level(int dst_id);
      int fill_level = 0;
      foreach(env.aicd_refmodel.endpoint_stored_cmd_len_daq[dst_id][i]) begin
        fill_level += env.aicd_refmodel.endpoint_stored_cmd_len_daq[dst_id][i];
      end
      return fill_level;
    endfunction : get_endp_fill_level


    virtual task wait_for_done(int dst_id);
      forever begin
        #1ms;
        //@posedge(done_if[dst_id]) 
        //decrement_fill_counter(int dst_id);
      end
    endtask : wait_for_done


    //task will be called by the cmd instruction before execution (starting the copy forward operations)
    virtual task increment_fill_counter(int dst_id, int cmd_length);
      `uvm_info(get_name(), $sformatf("Current fill level for endpoint[%0d] : %0d", dst_id, get_endp_fill_level(dst_id)), UVM_LOW)
      
      if (env.aicd_refmodel.fill_counter[dst_id].try_get(cmd_length)) begin
        `uvm_info(get_name(), $sformatf("There is space in fill_counter[%0d] for cmd_len: %0d", dst_id, cmd_length), UVM_LOW)
      end
      else begin 
        `uvm_info(get_name(), $sformatf("CMD Instr will stall: There is No space in fill_counter[%0d] for cmd_len: %0d", dst_id, cmd_length), UVM_LOW)
        //irq_status["COPY_FILL_COUNTER_OVERFLOW"]    = data_from_reg[16];  //ToDO: How does it overflow if we track not to send cmds when they are full? Also: What is the underflow condition/Scenario??
        env.aicd_refmodel.set_irq_status("COPY_FILL_COUNTER_OVERFLOW");  //handle_irq_status();
      end
      
      //ToDO: add fill level monitoring in additon to the semaphore
      env.aicd_refmodel.fill_counter[dst_id].get(cmd_length);
      env.aicd_refmodel.endpoint_stored_cmd_len_daq[dst_id].push_back(cmd_length);
    endtask : increment_fill_counter


    //task will be called when AIC CD receives Done indication from the different endpoints
    virtual task decrement_fill_counter(int dst_id);
      int done_cmd_length;
      if (env.aicd_refmodel.endpoint_stored_cmd_len_daq[dst_id].size() == 0) begin
        //irq_status["COPY_FILL_COUNTER_DONE_POP"]    = data_from_reg[15];
        env.aicd_refmodel.set_irq_status("COPY_FILL_COUNTER_DONE_POP");  //handle_irq_status();

        //irq_status["COPY_FILL_COUNTER_OVERFLOW"]    = data_from_reg[16];  //ToDO: Also: Is this the underflow condition/Scenario??
        env.aicd_refmodel.set_irq_status("COPY_FILL_COUNTER_OVERFLOW");  //handle_irq_status();

        `uvm_fatal(get_name(),$sformatf("Received Done signal but endpoint_stored_cmd_len_daq[%d] does not currently store any commands in its queues", dst_id))
      end

      done_cmd_length = env.aicd_refmodel.endpoint_stored_cmd_len_daq[dst_id].pop_front();

      `uvm_info(get_name(), $sformatf("Decrementing fill_counter[%d] for cmd_len: %0d", dst_id, done_cmd_length), UVM_LOW)
      env.aicd_refmodel.fill_counter[dst_id].put(done_cmd_length);
    endtask : decrement_fill_counter


    virtual task execute_cmd_instruction(ai_core_cd_instruction instr, int cmd_idx);
      ai_core_cd_cmd_instr cmd_instr;
      mem_addr_t src_start_byte_addr;
      mem_addr_t dst_start_byte_addr;
      mem_addr_t src_end_byte_addr;
      mem_addr_t dst_end_byte_addr;

      bit patch_id0_en;
      bit patch_id1_en;
      int word_index_0;
      int addr_width_0;
      int word_index_1;
      int addr_width_1;
      int addr_patch;


      `uvm_info(get_name(), $sformatf("Entered execute_cmd_instruction"), UVM_LOW)
      
      if (!$cast(cmd_instr, instr))
        `uvm_fatal("REF_MODEL",$sformatf("Cast was not succesfull for ai_core_cd_cmd_instr \ instr_type: %0p",instr.instr_type))


      if (cmd_instr.length == 0)
      begin
        `uvm_info(get_name(), $sformatf("Not executing instruction due to length 0 "), UVM_LOW)
        return;
      end

      //increment fill counters, perform check on them  ->> these act as a semaphore/resource sharing and will block the execution until enough are received 
      increment_fill_counter(cmd_instr.dst_id, cmd_instr.length);
      //on the other side we have to start DONE transactions fromt he appropriate port and when they are detected decrement fill counters and do check on them 

      //add to the expected x_ID read addr range to Memory    
    
      //add to the expected x_ID write addr range to Memory     (addr, range_base, range_top, cmd_idx, instr_idx)
      
      //ADD expected accesses for SPM CMD read
      //start_byte_addr = aic_base_addr + ctr_base_addr + control_offset + cmd_instr.cmd_ptr;  //ToDO update the start byte address below
      src_start_byte_addr =  env.m_mem_manager.command_list[cmd_instr.command_ids[0]].control_offset + cmd_instr.cmd_ptr;
      src_end_byte_addr = src_start_byte_addr + cmd_instr.length-1;  //length expresses number of bytes / adresses target words (8bytes)
      add_exp_mem_access_to_queue(src_start_byte_addr, src_end_byte_addr, env.m_mem_manager.exp_copy_rd_addr_q, "exp_copy_rd_addr_q", cmd_idx, cmd_instr.instr_idx);

      //ADD expected accesses for Block CMD write
      //start_byte_addr = aic_base_addr + get_target_addr_for_dst_id();  //ToDO update the start byte address below
      dst_start_byte_addr =  get_target_addr_for_dst_id();
      dst_end_byte_addr = dst_start_byte_addr + cmd_instr.length-1; //length expresses number of bytes / adresses target words (8bytes)
      add_exp_mem_access_to_queue(dst_start_byte_addr, dst_end_byte_addr, env.m_mem_manager.exp_copy_wr_addr_q, "exp_copy_wr_addr_q", cmd_idx, cmd_instr.instr_idx);
      
      
      //add expected to the instr_order_scoreboard //ToDO


      ////push instruction in the queue and/or increment counter 
      env.m_mem_manager.instr_q_count++;
  

      //copy data from src_addr to dst_addr for byte_length  ( or address range to address range  ) 
      env.m_mem_manager.execute_copy(src_start_byte_addr, dst_start_byte_addr, cmd_instr.length);

      //ToDO: get patch information from cmd_instr and registers
      word_index_0 = 0;
      addr_width_0 = 0;
      word_index_1 = 0;
      addr_width_1 = 0;

      patch_id0_en = (word_index_0 != 0) && (addr_width_0 != 0);
      patch_id1_en = (word_index_1 != 0) && (addr_width_1 != 0);

      //apply address patching patch_id0
      if (patch_id0_en) begin
        //ToDO: read addr_patch from register
        addr_patch = 0;
        env.m_mem_manager.execute_addr_patch(dst_start_byte_addr, word_index_0, addr_width_0, addr_patch);
      end

      //apply address patching patch_id1
      if (patch_id0_en) begin
        //ToDO: read addr_patch from register
        addr_patch = 0;
        env.m_mem_manager.execute_addr_patch(dst_start_byte_addr, word_index_1, addr_width_1, addr_patch);
      end
      
      //print memory for copy and patch debug
      env.m_mem_manager.ref_mem.print_memory_part(src_start_byte_addr, src_end_byte_addr, "SPM");
      env.m_mem_manager.ref_mem.print_memory_part(dst_start_byte_addr, dst_end_byte_addr, $sformatf("BLOCK_%0d", cmd_instr.dst_id));

      //wait until the SVT Mon callback on last read -> because instructions have to be executed in order

      //start  to do partial compare with watchdog with the SVT Memory for this range -> partial comparison will know which cmd/instr combo executed it  
      //start instead of wait because reads of next instr can be executed at same time with the write of this instruction
      //comparison actual comparison is triggered by the SVT Mon callback on last write, it will also add the 

      //!!!we make sure that the order between tkn, tms, and cpy instructions via the instr_order_scoreboard 
    endtask : execute_cmd_instruction


    virtual task execute_prg_instruction(ai_core_cd_instruction instr, int cmd_idx);
      ai_core_cd_prg_instr prg_instr;
      mem_addr_t src_start_byte_addr;
      mem_addr_t dst_start_byte_addr;
      mem_addr_t src_end_byte_addr;
      mem_addr_t dst_end_byte_addr;
      
      `uvm_info(get_name(), $sformatf("Entered execute_prg_instruction"), UVM_LOW)

      if (!$cast(prg_instr, instr))
        `uvm_fatal("REF_MODEL",$sformatf("Cast was not succesfull for ai_core_cd_prg_instr \ instr_type: %0p",instr.instr_type))


      if (prg_instr.length == 0)
      begin
        `uvm_info(get_name(), $sformatf("Not executing instruction due to length 0 ",), UVM_LOW)
        return;
      end

      //add to the expected x_ID read addr range to Memory 

      //sanity check - make sure that the instruction has been updated just with the current cmd index
      if (prg_instr.command_ids.size() != 1) begin
        `uvm_fatal("REF_MODEL","Instruction to be executed has more than 1 cmd references")
      end

      //ADD expected accesses for SPM PRG read
      //start_byte_addr = aic_base_addr + ctr_base_addr + control_offset + prg_instr.prg_ptr;  //ToDO update the start byte address below
      src_start_byte_addr =  env.m_mem_manager.command_list[prg_instr.command_ids[0]].control_offset + prg_instr.prg_ptr;
      src_end_byte_addr = src_start_byte_addr + prg_instr.length-1;  //length expresses number of bytes / adresses target words (8bytes)
      add_exp_mem_access_to_queue(src_start_byte_addr, src_end_byte_addr, env.m_mem_manager.exp_copy_rd_addr_q, "exp_copy_rd_addr_q", cmd_idx, prg_instr.instr_idx);

      //ADD expected accesses for Block PRG write
      //start_byte_addr = aic_base_addr + get_target_addr_for_dst_id() + prg_instr.dst_addr;  //ToDO update the start byte address below
      dst_start_byte_addr =  get_target_addr_for_dst_id() + prg_instr.dst_addr;
      dst_end_byte_addr = dst_start_byte_addr + prg_instr.length-1;  //length expresses number of bytes / adresses target words (8bytes)
      add_exp_mem_access_to_queue(dst_start_byte_addr, dst_end_byte_addr, env.m_mem_manager.exp_copy_wr_addr_q, "exp_copy_wr_addr_q", cmd_idx, prg_instr.instr_idx);


      //`uvm_info(get_name(), $sformatf("added expected_instr_read_addr :\n %p",env.m_mem_manager.exp_instr_rd_addr_q), UVM_LOW)
      //foreach (env.m_mem_manager.exp_instr_rd_addr_q[i])
      //  `uvm_info(get_name(), $sformatf("expected_instr_read_addr[%0d]: %p", i, env.m_mem_manager.exp_instr_rd_addr_q[i]), UVM_LOW)
      //

      ////push instruction in the queue and/or increment counter 
      env.m_mem_manager.instr_q_count++;


      //add to the expected x_ID read addr range to Memory    
      //add to the expected x_ID write addr range to Memory     (addr, range_base, range_top, cmd_idx, instr_idx)
      //add expected to the instr_order_scoreboard

      //check pointers and address for consistency (i.e. if they are not aligned they should be unaligned with the same value)

      //copy data from src_addr to dst_addr for byte_length  ( or address range to address range  ) 
      //env.m_mem_manager.ref_mem.copy_mem_range_src2dst(src_start_byte_addr, dst_start_byte_addr, prg_instr.length);
      env.m_mem_manager.execute_copy(src_start_byte_addr, dst_start_byte_addr, prg_instr.length);

      //print memory for copy debug
      env.m_mem_manager.ref_mem.print_memory_part(src_start_byte_addr, src_end_byte_addr, "SPM");
      env.m_mem_manager.ref_mem.print_memory_part(dst_start_byte_addr, dst_end_byte_addr, $sformatf("BLOCK_%0d", prg_instr.dst_id));


      //wait until the SVT Mon callback on last read -> because instructions have to be executed in order //not really necessary since we have the instr_order_scoreboard
      //start  to do partial compare with watchdog with the SVT Memory for this range -> partial comparison will know which cmd/instr combo executed it  
      //start instead of wait because reads of next instr can be executed at same time with the write of this instruction
      //comparison actual comparison is triggered by the SVT Mon callback on last write, it will also add the 

      //!!!we make sure that the order between tkn, tms, and cpy instructions via the instr_order_scoreboard 

    endtask : execute_prg_instruction


    //convert token trans to expected actual type 
    virtual function token_agent_seq_item convert_tkn_exp2act(ai_core_cd_instruction instr);
      token_agent_seq_item tkn_item;

      tkn_item = token_agent_seq_item::type_id::create("tkn_item");
      if (instr.token_type inside {CONS_LOC, CONS_GLOB} )
        tkn_item.m_type_enm = TOK_CONS_MON;
      if (instr.token_type inside {PROD_LOC, PROD_GLOB} )
        tkn_item.m_type_enm = TOK_PROD_MON;

      return tkn_item;
    endfunction : convert_tkn_exp2act


    virtual function void incr_decr_token_cnt(token_type_enum token_type, ref int tkn_count);
      case (token_type)
        CONS_LOC  : tkn_count--;
        PROD_LOC  : tkn_count++;
        CONS_GLOB : tkn_count--;
        PROD_GLOB : tkn_count++;
      endcase
      //`uvm_info(get_name(), $sformatf("Updated %p token count: %0d", token_type, tkn_count), UVM_LOW)
    endfunction


    //ToDO: be aware that token agent driver does not appear to allow back to back transactions () -- need to understand how to enable these
    //ToDO: also it might be usefull to start the sequences before the instruction is executed by DUT so that rdy or drv signal is already asserted
    virtual task start_token_sequence(token_type_enum token_type, int tkn_line);
      case (token_type)
        CONS_LOC  : begin
          `uvm_info("TOK_DBG", $sformatf("Starting %p token sequence on line %0d", token_type, tkn_line), UVM_LOW)
          tok_cons_seq.randomize();
          tok_cons_seq.start(env.local_tok_agt[tkn_line].m_tok_seqr);
        end
        PROD_LOC  : begin
          `uvm_info("TOK_DBG", $sformatf("Starting %p token sequence on line %0d", token_type, tkn_line), UVM_LOW)
          tok_prod_seq.randomize();
          tok_prod_seq.start(env.local_tok_agt[tkn_line].m_tok_seqr);
        end
        CONS_GLOB : begin
          `uvm_info("TOK_DBG", $sformatf("Starting %p token sequence on line %0d", token_type, tkn_line), UVM_LOW)
          tok_cons_seq.randomize();
          tok_cons_seq.start(env.global_tok_agt[tkn_line].m_tok_seqr);
        end
        PROD_GLOB : begin
          `uvm_info("TOK_DBG", $sformatf("Starting %p token sequence on line %0d", token_type, tkn_line), UVM_LOW)
          tok_prod_seq.randomize();
          tok_prod_seq.start(env.global_tok_agt[tkn_line].m_tok_seqr);
        end
        default : `uvm_fatal("TOK_SEQ", $sformatf("Should not reach this case branch"))
      endcase
    endtask : start_token_sequence


    virtual task execute_tkn_instruction(ai_core_cd_instruction instr, int cmd_idx);
      ai_core_cd_token_instr tkn_instr;
      token_agent_seq_item tkn_item;

      `uvm_info(get_name(), $sformatf("Entered execute_tkn_instruction"), UVM_LOW)

      if (!$cast(tkn_instr, instr))
        `uvm_fatal("REF_MODEL",$sformatf("Cast was not succesfull for ai_core_cd_token_instr \ instr_type: %0p",instr.instr_type))
      //`uvm_info(get_name(), $sformatf("Instruction being executed is :\n %s",tkn_instr.sprint()), UVM_LOW)

      //send expected token transaction to token scbd and instr_order_scbd
      if (tkn_instr.token_type inside {CONS_LOC, PROD_LOC}) begin
        for (int tkn_line=0; tkn_line<m_env_cfg.aicd_ref_model_cfg.local_token_line_num; tkn_line++) begin
          
          if (tkn_instr.token_num[tkn_line] == 1) begin
            tkn_item = convert_tkn_exp2act(tkn_instr);
            env.aicd_refmodel.local_token_exp_ap[tkn_line].write(tkn_item);
            `uvm_info(get_full_name(), $sformatf("Sending to SB on EXP %p",tkn_instr.token_type), UVM_LOW)

            incr_decr_token_cnt(tkn_instr.token_type, env.aicd_refmodel.local_tokens[tkn_line]);
            start_token_sequence(tkn_instr.token_type, tkn_line);
          end
        end
      end
      else if (tkn_instr.token_type inside {CONS_GLOB, PROD_GLOB}) begin 
        for (int tkn_line=0; tkn_line<m_env_cfg.aicd_ref_model_cfg.global_token_line_num; tkn_line++) begin
          `uvm_info(get_name(), $sformatf("GLOBAL tkn_instr.token_num[%0d]=%0d",tkn_line, tkn_instr.token_num[tkn_line]), UVM_LOW)
          
          if (tkn_instr.token_num[tkn_line] == 1) begin
            tkn_item = convert_tkn_exp2act(tkn_instr);
            env.aicd_refmodel.global_token_exp_ap[tkn_line].write(tkn_item);
            `uvm_info(get_full_name(), $sformatf("Sending to SB on EXP %p",tkn_instr.token_type), UVM_LOW)

            incr_decr_token_cnt(tkn_instr.token_type, env.aicd_refmodel.global_tokens[tkn_line]);
            start_token_sequence(tkn_instr.token_type, tkn_line);
          end
        end
      end 
      else begin
        `uvm_fatal("REF_MODEL","Not able to recognize token type")
      end

      //increase counters if needed and semaphore logic || design tells us that tokens are not blocking ACD. ACD is agnostic of the token flow 
      //counters just used for analysis/debug and coverage for the meantime 

      
      //ToDO: add instruction to queue or increment counter
      //env.m_mem_manager.instr_q_count++; ??
    endtask : execute_tkn_instruction


    virtual task execute_tms_instruction(ai_core_cd_instruction instr, int cmd_idx);
      ai_core_cd_timestamp_instr tms_instr;
      timestamp_t exp_tms;

      `uvm_info(get_name(), $sformatf("Entered execute_tms_instruction"), UVM_LOW)

      if (!$cast(tms_instr, instr))
        `uvm_fatal("REF_MODEL",$sformatf("Cast was not succesfull for ai_core_cd_timestamp_instr \ instr_type: %0p",instr.instr_type))
      
      //add expected timestamp   
      exp_tms.tms_id = tms_instr.tms_id;
      exp_tms.command_idx = cmd_idx;
      exp_tms.instr_idx = instr.instr_idx;
      env.m_mem_manager.exp_timestamp_q.push_back(exp_tms);

      //add instruction to queue or increment counter
      env.m_mem_manager.instr_q_count++;
    endtask : execute_tms_instruction

endclass:ai_core_cd_base_test

`endif // AI_CORE_CD_BASE_TEST_SV
