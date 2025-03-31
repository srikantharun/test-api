`ifndef GUARD_DPU_BASE_TEST_SV
`define GUARD_DPU_BASE_TEST_SV
class dpu_base_test extends uvm_test;

  `uvm_component_utils(dpu_base_test)

  dpu_env env;

  /** Instance of the environment configuration */
  dpu_env_cfg m_env_cfg = new();
  
  /** Customized configuration */
  cust_svt_axi_system_configuration cfg;

  axi_simple_reset_sequence   axi_reset_seq;
  dpu_csr_config_sequence     dpu_csr_config_seq;
  dpu_cmd_descriptor_sequence dpu_cmd_descriptor_seq;
  dpu_program_sequence        dpu_program_seq;
  dpu_stream_sequence         dpu_ifd0_stream_seq;
  dpu_stream_sequence         dpu_ifd1_stream_seq;


  function new(string name = "dpu_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new


  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    set_type_override_by_type(svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
    uvm_config_db#(cust_svt_axi_system_configuration)::set(this, "env", "cfg", this.cfg);

    m_env_cfg = dpu_env_cfg::type_id::create("m_env_cfg");
    uvm_config_db#(dpu_env_cfg)::set(this, "env*", "m_env_cfg", this.m_env_cfg);

    env = dpu_env::type_id::create("env", this);
   

    uvm_config_db#(uvm_object_wrapper)::set(this, "env.sequencer.reset_phase", "default_sequence", axi_simple_reset_sequence::type_id::get());
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    axi_reset_seq          = axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    dpu_csr_config_seq     = dpu_csr_config_sequence::type_id::create("dpu_csr_config_seq");
    dpu_cmd_descriptor_seq = dpu_cmd_descriptor_sequence::type_id::create("dpu_cmd_descriptor_seq");
    dpu_program_seq        = dpu_program_sequence::type_id::create("dpu_program_seq");
    dpu_ifd0_stream_seq    = dpu_stream_sequence::type_id::create("dpu_ifd0_stream_seq");
    dpu_ifd1_stream_seq    = dpu_stream_sequence::type_id::create("dpu_ifd1_stream_seq");

    uvm_top.set_timeout(500us, 1);
  endfunction : build_phase


  function void final_phase(uvm_phase phase);
    uvm_report_server svr;
    super.final_phase(phase);

    svr = uvm_report_server::get_server();

    if (svr.get_severity_count(UVM_FATAL) + svr.get_severity_count(UVM_ERROR) > 0)
      `uvm_info("final_phase", "\nSvtTestEpilog: Failed\n", UVM_NONE)
    else `uvm_info("final_phase", "\nSvtTestEpilog: Passed\n", UVM_NONE)

    svr.set_max_quit_count(100);
  endfunction : final_phase


  //create the command but don´t write it, because program needs to be written first
  //or when the cmd is executed it will get a unknown (X) instruction from program memory
  virtual task cfg_cmd_desc(int i_min = 1, i_max = 5, l_min = 1, l_max = 5); 
    dpu_cmd_descriptor_seq.randomize() with {
      cmd_desc.cmd.main_0.iteration    inside {[i_min : i_max]};
      cmd_desc.cmd.main_1.iteration    inside {[i_min : i_max]};
      cmd_desc.cmd.main_2.iteration    inside {[i_min : i_max]};
      cmd_desc.cmd.nested_0.iteration  inside {[i_min : i_max]};
      cmd_desc.cmd.nested_1.iteration  inside {[i_min : i_max]};

      cmd_desc.cmd.main_0.length    inside {[l_min : l_max]};
      cmd_desc.cmd.main_1.length    inside {[l_min : l_max]};
      cmd_desc.cmd.main_2.length    inside {[l_min : l_max]};
      cmd_desc.cmd.nested_0.length  inside {[l_min : l_max]};
      cmd_desc.cmd.nested_1.length  inside {[l_min : l_max]};
    };
  endtask


  //write the instructions into program mem and start cmd execution 
  virtual task cfg_program_and_start(bit config_only = 0, set_rfs = 0);
    //generates the program memory
    dpu_program_seq.cmd_desc = dpu_cmd_descriptor_seq.cmd_desc;
    dpu_program_seq.set_rfs = set_rfs;
    dpu_program_seq.randomize();
    if (!config_only) begin
      dpu_program_seq.start(env.axi_system_env.master[0].sequencer);
      dpu_cmd_descriptor_seq.start(env.axi_system_env.master[0].sequencer);
    end
  endtask


  virtual task cfg_streams(bit config_only = 0, int n_cycles = 0);
    //Sending stream data ifd0
    //no need to randomize, it is done internally when start is called
    dpu_ifd0_stream_seq.dp_ctrl_reg = dpu_csr_config_seq.dp_ctrl_reg;
    dpu_ifd0_stream_seq.ifd_config = dpu_ifd0_stream_seq.IFD0;
    dpu_ifd0_stream_seq.cmd_desc   = dpu_cmd_descriptor_seq.cmd_desc;
    dpu_ifd0_stream_seq.prog_mem   = dpu_program_seq.prog_mem;

    dpu_ifd1_stream_seq.dp_ctrl_reg = dpu_csr_config_seq.dp_ctrl_reg;
    dpu_ifd1_stream_seq.ifd_config = dpu_ifd1_stream_seq.IFD1;
    dpu_ifd1_stream_seq.cmd_desc   = dpu_cmd_descriptor_seq.cmd_desc;
    dpu_ifd1_stream_seq.prog_mem   = dpu_program_seq.prog_mem;

    if (!config_only) begin
      fork : data_stream_fork
        dpu_ifd0_stream_seq.start(env.axi_system_env.master[1].sequencer);
        dpu_ifd1_stream_seq.start(env.axi_system_env.master[2].sequencer);
      join_none

      wait_for_end_of_program();
      disable data_stream_fork;
    end
    wait_cycles(n_cycles);
  endtask

  
  virtual task wait_for_end_of_program();
    bit [63:0] data;
    uvm_status_e status;
    fork check_irq(); join_none
    do begin
      wait_cycles(50);
      env.regmodel.cmdblk_status.read(status, data);
    end while (data[1:0] != 0); // IDLE state == 0
    env.regmodel.irq_status.read(status,data);
    `uvm_info (get_name, $sformatf("Program finished, DPU in IDLE"), UVM_HIGH)
    disable fork;
  endtask


  virtual task wait_cycles(int cycles = 1);
    repeat (cycles) 
      @(posedge env.axi_system_env.vif.common_aclk);
  endtask


  task check_irq();
    dpu_irq_reg_t  irq_reg;
    uvm_status_e status;
    while (irq_reg == 0) begin
      env.regmodel.irq_status.read(status, irq_reg);
      wait_cycles(50);
    end
    `uvm_info(get_name, $sformatf("Got interruption: %p", irq_reg), UVM_LOW)
  endtask

endclass

`endif  // GUARD_DPU_BASE_TEST_SV
