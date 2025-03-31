/**
 * Sequence that is responsible to randomize and write the program into DWPU
 */
class ai_core_dwpu_prg_sequence extends svt_axi_master_base_sequence;
  svt_axi_master_transaction write_tran;
  int prog_mem_size;

  dwpu_dp_command_t prog_mem[int];
  rand dwpu_dp_command_t rnd_prog_mem_q[$];

  /** pointer to cmd information */
  ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb   cmd_info;

  // AI Core DWPU RAL Modl
  dwpu_csr_reg_block regmodel;
  
  int main_start[   3];
  int main_end[     3];
  int main_length[  3];
  int main_iter[    3];
  int nested_start[ 2];
  int nested_end[   2];
  int nested_length[2];
  int nested_iter[  2];

  constraint c_prog {
    rnd_prog_mem_q.size == prog_mem_size;
    foreach (rnd_prog_mem_q[i]) {
      rnd_prog_mem_q[i].op_desc.opcode dist {
        SOP    := 70,
        MAX,MIN,SUM :/ 30
      };

      rnd_prog_mem_q[i].op_desc.shift_wb dist {
        1 := 70,
        0 := 30
      };
      rnd_prog_mem_q[i].op_desc.shift_sp dist {
        1 := 70,
        0 := 30
      };

      rnd_prog_mem_q[i].op_desc.last_push dist {
        1 := 20,
        0 := 80
      };

      rnd_prog_mem_q[i].op_desc.op_exe dist {
        1 := 70,
        0 := 30
      };

      foreach (rnd_prog_mem_q[i].w_sel[j]) {
        rnd_prog_mem_q[i].w_sel[j] dist {
          0 := 40,
          [1:62] :/ 20,
          63 := 40
        };
      }
      foreach (rnd_prog_mem_q[i].i_sel[j]) {
        rnd_prog_mem_q[i].i_sel[j] dist {
          0       := 25,  //absorbing element
          1       := 40,  //data input
          [2:126] :/ 25,  //sp regs
          127     := 10   //last sp reg
        };
      }
    }
  }

  /** UVM Object Utility macro */
  `uvm_object_utils(ai_core_dwpu_prg_sequence)

  /** Class Constructor */
  function new(string name="ai_core_dwpu_prog_sequence");
    super.new(name);
  endfunction

  extern function void pre_randomize();
  extern function void post_randomize();
  extern task send_write(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[], bit a_incr_addr);
  extern virtual task body();
  /** return the number of input data needed by each loop
   * the condition for determine if will consume data from input is "ai_core_dwpu_utils::get_read_input(prog_mem[mem_pos])"
   * the increment is equal to "1"
   */
  `GET_INPUT_STREAM_INFO(ai_core_dwpu_utils::get_read_input(prog_mem[mem_pos]), 1)

endclass: ai_core_dwpu_prg_sequence

function void ai_core_dwpu_prg_sequence::pre_randomize();
  
  /** delete the previous information */
  for (int i=0; i<3; i++) begin
    main_start[i]   = 0;
    main_end[i]     = 0;
    main_length[i]  = 0;
    main_iter[i]    = 0;
  end
  for (int i=0; i<2; i++) begin
    nested_start[i]   = 0;
    nested_end[i]     = 0;
    nested_length[i]  = 0;
    nested_iter[i]    = 0;
  end

  `uvm_info("pre_rand", $sformatf("format: %0d",cmd_info.format), UVM_LOW)
  /** Initialize main variables (used from program size) */
  for (int i=0; i<3; i++) begin
    if(cmd_info.main_valid(i) && (cmd_info.format!=aic_dp_cmd_gen_pkg::Bypass)) begin
      main_start[i]   = cmd_info.get_start(     1, i);
      main_end[i]     = cmd_info.get_end(       1, i);
      main_length[i]  = cmd_info.get_length(    1, i);
      main_iter[i]    = cmd_info.get_iteration( 1, i);
      `uvm_info("pre_rand", $sformatf("main[%0d] -> start: %0d | end: %0d | iteration: %0d", i, main_start[i], main_end[i], main_iter[i]), UVM_LOW)
    end
  end
  /** Initialize nested variables */
  for (int i=0; i<2; i++) begin
    if(cmd_info.nested_valid(i) && (cmd_info.format!=aic_dp_cmd_gen_pkg::Bypass)) begin
      nested_start[i]   = cmd_info.get_start(     0, i);
      nested_end[i]     = cmd_info.get_end(       0, i);
      nested_length[i]  = cmd_info.get_length(    0, i);
      nested_iter[i]    = cmd_info.get_iteration( 0, i);
      `uvm_info("pre_rand", $sformatf("nested[%0d] -> start: %0d | end: %0d | iteration: %0d", i, nested_start[i], nested_end[i], nested_iter[i]), UVM_LOW)
    end
  end
  /** Build prog_mem array variable */
  prog_mem.delete();
  if(cmd_info.format!=aic_dp_cmd_gen_pkg::Bypass) begin
    for (int main_idx=0; main_idx<3; main_idx++) begin
      if( (main_iter[main_idx] != 0) && (main_length[main_idx]!=0)) begin
        for (int mem_pos = main_start[main_idx]; mem_pos <= main_end[main_idx]; mem_pos++) begin
          prog_mem[mem_pos] = 0;
        end
      end
    end
  end
  foreach (prog_mem[i])
    `uvm_info("pre_rand", $sformatf("created prog_mem[%0d]",i), UVM_FULL)

  /** set prog_mem_size to be used in the randomization */
  prog_mem_size = prog_mem.size();
endfunction : pre_randomize


function void ai_core_dwpu_prg_sequence::post_randomize();
  bit found_last_push = 0;
  int first_valid_addr_push_last;
  foreach (prog_mem[i]) begin
    prog_mem[i] = rnd_prog_mem_q.pop_front();
  end

  /** check if last push was set in any of the operations, if not, set it in the last instruction */
  if(cmd_info.format!=aic_dp_cmd_gen_pkg::Bypass) begin
    for (int main_idx=0; main_idx<3; main_idx++) begin
      if(cmd_info.main_valid(main_idx)) begin
        found_last_push = 0;
        for(int mem_pos=main_end[main_idx]; mem_pos>=main_start[main_idx]; mem_pos--) begin
          if(found_last_push == 0) begin
            if(prog_mem[mem_pos].op_desc.last_push == 1) begin
              //if it is the highest position with last_push, then this will be the real last push of the stream
              prog_mem[mem_pos].op_desc.op_exe = 1;
              found_last_push = 1;
              `uvm_info("post_randomize", $sformatf("last push will be inserted at prog_mem[%0d]", mem_pos), UVM_FULL)
            end
            else begin
              //if the highest last_push was not found, then the op_exe needs to be reset, otherwise the output stream will be active at the end of the program
              prog_mem[mem_pos].op_desc.op_exe = 0;
            end
          end
        end
        //if at the end of loop, no last_push was found, then insert the last_push at the last instruction by default
        if (found_last_push ==0) begin
          prog_mem[main_end[main_idx]].op_desc.last_push = 1;
          prog_mem[main_end[main_idx]].op_desc.op_exe    = 1;
          `uvm_info("post_randomize", $sformatf("last push will be inserted at prog_mem[%0d]", main_end[main_idx]), UVM_FULL)
        end
      end
    end
  end
  `uvm_info("post_randomize", $sformatf("Finsh post_randomize"), UVM_FULL)

endfunction

task ai_core_dwpu_prg_sequence::send_write(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[], bit a_incr_addr);
  axi_master_write_split_sequence write_seq;

  foreach (a_data_da[i])`uvm_info("send_write", $sformatf("Sending data[%0d] = 0x%0x", i, a_data_da[i]), UVM_HIGH)
  /** create sequence from type axi_master_write_sequence */
  `uvm_create(write_seq)
  //randomize transaction
  if(!write_seq.randomize() with {
    incr_addr_between_bursts == a_incr_addr;
    cfg_addr        == a_addr;
    cfg_data.size == a_data_da.size;
    foreach(cfg_data[i]) {
      cfg_data[i] == a_data_da[i];
    }
  }) `uvm_fatal(get_name, "write_tran randomization error!");

  //start sequence
  write_seq.start(m_sequencer);
  `uvm_info("send_write", $sformatf("Finish the sending of write sequence"), UVM_HIGH)

endtask : send_write

task ai_core_dwpu_prg_sequence::body();
  svt_configuration get_cfg;
  //each DWPU_INSTR_NUM_ROWS addrs in the memory represents a single instruction
  int mem_to_instr_addr = 8*DWPU_INSTR_NUM_ROWS;
  axi_lp_data_t l_data_packed[];
  bit status;
  int init_prog_pos, next_prog_pos, prog_mem_status;
  bit l_incr_addr;
  `uvm_info("body", "Entered ...", UVM_LOW)

  super.body();

  /** Obtain a handle to the port configuration */
  p_sequencer.get_cfg(get_cfg);
  if (!$cast(cfg, get_cfg)) begin
    `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
  end

  //set the increment address variable when we are in the normal program execution
  l_incr_addr = 1;
  //delete data in the beggining of the loop to enable the packing of all program into one big burst
  l_data_packed.delete();
  //get the first position in prog_mem
  prog_mem.first(next_prog_pos);
  init_prog_pos = next_prog_pos;
  foreach (prog_mem[i]) begin
    `uvm_info ("body", $sformatf("sending instr into several transactions @ 0x%h: prog_mem[%0d]=%p",DWPU_IMEM_ST_ADDR + i * mem_to_instr_addr, i, prog_mem[i]), UVM_HIGH)
    /** pack instruction into data array */
    ai_core_dwpu_utils::pack_instr2data(prog_mem[i], l_data_packed);
    /** get the next address of prog_mem*/
    prog_mem_status = prog_mem.next(next_prog_pos);
    /** if it is the last position of prog_mem (prog_mem_status equal to 0) or the next position is not a sequential (next_prog_pos not equal to current position + 1)
      * we are a the end of a section and it neccessary to send this transaction
      */
    if((prog_mem_status==0) || (next_prog_pos != (i+1))) begin
      `uvm_info ("body", $sformatf("finish section with initial address = %0d and final addr = %0d", init_prog_pos, i), UVM_HIGH)
      send_write(DWPU_IMEM_ST_ADDR + init_prog_pos * mem_to_instr_addr, l_data_packed, l_incr_addr);
      /** flush the packed data array to be used for the next section */
      l_data_packed.delete();
      /** set new init_prog_pos */
      init_prog_pos = next_prog_pos;
    end
  end
  
  `uvm_info("body", "AXI PROG WRITE transaction completed", UVM_HIGH);

  `uvm_info("body", "Exiting...", UVM_HIGH)
 endtask: body
