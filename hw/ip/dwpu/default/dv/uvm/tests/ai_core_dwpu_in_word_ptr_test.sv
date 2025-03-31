/**
* The aim of this testcase is to verify the correct behavior of in_word_ptr field under CMDBLK_STATUS register
* The sequence of events will be the following:
* - randomize a command that has at least two words
* - split the sending of the command in a way that last word is not sent. For exammple: if the cmd_format=4 the number of words is equal to 3, which means that the testcase will only send 2 words.
* - read the CMDBLK_STATUS and verify that the field in_word_ptr has the correct value (cmd format number of words minus 1. Following the example above, the expected value at this stage shall be equal to 2)
* - reset the in_word_ptr by writing to PTR_RST field on CMDBLK_CTRL register
* - read the CMDBLK_STATUS and verify that the field in_word_ptr has the correct value (0 in this case)
* - do the previous steps 10 times
*/
class ai_core_dwpu_in_word_ptr_test extends ai_core_dwpu_base_test;

  // Registration with the factory
  `uvm_component_utils(ai_core_dwpu_in_word_ptr_test)

  ai_core_dwpu_cmd_sequence                             cmd_seq;
  ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb   cmd_info_seq;
  axi_master_write_split_sequence                       write_split_seq;

  // Class Constructor
  function new(string name = "ai_core_dwpu_in_word_ptr_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    cmd_seq       = ai_core_dwpu_cmd_sequence::type_id::create("cmd_seq", this);
    cmd_info_seq  = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb::type_id::create("cmd_info_seq", this);
    /** create sequence from type axi_master_write_split_sequence */
    write_split_seq = axi_master_write_split_sequence::type_id::create($sformatf("write_split_seq"));

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase
  // Run phase
  virtual task run_phase(uvm_phase phase);
    bit [AXI_LT_DATA_WIDTH-1:0] l_cmd_data_da[];
    bit [63:0] data;

    phase.raise_objection(this);
    repeat (10) begin
      //randomize command sequence
      randomize_cmd_seq();

      //send command to command fifo
      //(do not send the full data because the counter is reset when the total number of words for that command type is achieved)
      send_command(l_cmd_data_da);

      //read the status register
      regmodel.cmdblk_status.read(status, data);
      //check bits [15:8] to see if the value of the counter is equal to the number of words that were sent
      if(data[15:8] != l_cmd_data_da.size()) begin
        `uvm_error(get_name, $sformatf("The value of IN_WORD_PTR is incorrect after sending some words of the command. Expected : %0d and Observed : %0d", l_cmd_data_da.size(), data[15:8]));
      end
      else begin
        `uvm_info(get_type_name(), $sformatf("The value of IN_WORD_PTR is correct after sending some words of the command. Expected : %0d", l_cmd_data_da.size()), UVM_LOW)
      end

      //reset the counter
      regmodel.cmdblk_ctrl.write(status, 32'b10); //setting the PTR_RST to 1 (bit 1)
      regmodel.cmdblk_ctrl.write(status, 32'b00); //setting the PTR_RST to 0 (bit 1)
      
      //read the status
      regmodel.cmdblk_status.read(status, data);
      
      //check bits [15:8] to see if the value of the counter was reset
      if(data[15:8] != 0) begin
        `uvm_error(get_name, $sformatf("The value of IN_WORD_PTR is incorrect after doing the reset. Expected : %0d and Observed : %0d", 0, data[15:8]));
      end
      else begin
        `uvm_info(get_type_name(), $sformatf("The value of IN_WORD_PTR is correct after doing the reset. Expected : %0d", 0), UVM_LOW)
      end
      //delete the array to be able to re-start the sequence
      l_cmd_data_da.delete();
    end

    phase.drop_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase finished, dropping objection"), UVM_LOW)
  endtask
  
  function void randomize_cmd_seq();
    //program generation
    if(!cmd_seq.randomize() with {
      header.format != aic_dp_cmd_gen_pkg::Bypass;
    }) `uvm_error(get_name, "cmd_seq randomization error!");
    
    //set the base and top addresses for cmd_info_seq randomization
    cmd_info_seq.base=0;
    cmd_info_seq.top=INSTR_MEM_DEPTH-1;
    //randomize command
    if(!cmd_info_seq.randomize() with {
      //set the command to be valid
      valid == 1;
      format == cmd_seq.header.format;
    }) `uvm_error(get_name, "cmd_info_seq randomization error!");

    //set the pointer to command info
    cmd_seq.cmd_info = cmd_info_seq;

  endfunction : randomize_cmd_seq
  
  task send_command(ref bit [AXI_LT_DATA_WIDTH-1:0] p_cmd_data_da []);
    //get data from commad sequence into an array
    cmd_seq.get_packed_data_from_cmd(p_cmd_data_da);
    // remove the last word. This is necessary because the counter is reset to 0 if the command is fully sent.
    p_cmd_data_da = new[p_cmd_data_da.size-1] (p_cmd_data_da);
  
    //randomize transaction
    if(!write_split_seq.randomize() with {
      incr_addr_between_bursts == 0; //into the command fifo we don't want to increment the address between bursts. Always write to the base address of CMD fifo
      cfg_addr        == DWPU_CMD_ST_ADDR;
      cfg_data.size == p_cmd_data_da.size;
      foreach(cfg_data[i]) {
        cfg_data[i] == p_cmd_data_da[i];
      }
    }) `uvm_fatal(get_name, "write_tran randomization error!");
    //start sequence
    write_split_seq.start(env.m_axi_system_env.master[0].sequencer);
  endtask : send_command

endclass : ai_core_dwpu_in_word_ptr_test
