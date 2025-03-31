// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: gbratu

`ifndef GUARD_AI_CORE_CD_MEM_MODEL_SVH
`define GUARD_AI_CORE_CD_MEM_MODEL_SVH


`define gfn get_full_name()

`ifndef uvm_object_new
`define uvm_object_new \
    function new (string name=""); \
      super.new(name); \
    endfunction : new
`endif

`ifndef dv_info
// verilog_lint: waive macro-name-style
`define dv_info(MSG_, VERBOSITY_ = uvm_pkg::UVM_LOW, ID_ = $sformatf("%m")) \
    if (uvm_pkg::uvm_report_enabled(VERBOSITY_, uvm_pkg::UVM_INFO, ID_)) begin \
        uvm_pkg::uvm_report_info(ID_, MSG_, VERBOSITY_, `uvm_file, `uvm_line, "", 1); \
    end
`endif

`ifndef dv_warning
// verilog_lint: waive macro-name-style
`define dv_warning(MSG_, ID_ = $sformatf("%m")) \
    if (uvm_pkg::uvm_report_enabled(uvm_pkg::UVM_NONE, uvm_pkg::UVM_WARNING, ID_)) begin \
        uvm_pkg::uvm_report_warning(ID_, MSG_, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
    end
`endif

`ifndef dv_error
// verilog_lint: waive macro-name-style
`define dv_error(MSG_, ID_ = $sformatf("%m")) \
    if (uvm_pkg::uvm_report_enabled(uvm_pkg::UVM_NONE, uvm_pkg::UVM_ERROR, ID_)) begin \
        uvm_pkg::uvm_report_error(ID_, MSG_, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
    end
`endif

`ifndef dv_fatal
// verilog_lint: waive macro-name-style
`define dv_fatal(MSG_, ID_ = $sformatf("%m")) \
    if (uvm_pkg::uvm_report_enabled(uvm_pkg::UVM_NONE, uvm_pkg::UVM_FATAL, ID_)) begin \
        uvm_pkg::uvm_report_fatal(ID_, MSG_, uvm_pkg::UVM_NONE, `uvm_file, `uvm_line, "", 1); \
    end
`endif

`ifndef DV_CHECK
`define DV_CHECK(T_, MSG_ = "", SEV_ = error, ID_ = `gfn) \
    begin \
      if (T_) ; else begin \
        `dv_``SEV_($sformatf("Check failed (%s) %s ", `"T_`", MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_CASE_EQ
`define DV_CHECK_CASE_EQ(ACT_, EXP_, MSG_ = "", SEV_ = error, ID_ = `gfn) \
    begin \
      if ((ACT_) === (EXP_)) ; else begin \
        `dv_``SEV_($sformatf("Check failed %s === %s (0x%0h [%0b] vs 0x%0h [%0b]) %s", \
                             `"ACT_`", `"EXP_`", ACT_, ACT_, EXP_, EXP_, MSG_), ID_) \
      end \
    end
`endif

`ifndef DV_CHECK_FATAL
`define DV_CHECK_FATAL(T_, MSG_ = "", ID_ = `gfn) \
    `DV_CHECK(T_, MSG_, fatal, ID_)
`endif

// Shorthand for common std::randomize(foo) + fatal check
`ifndef DV_CHECK_STD_RANDOMIZE_FATAL
`define DV_CHECK_STD_RANDOMIZE_FATAL(VAR_, MSG_ = "Randomization failed!", ID_ = `gfn) \
        `DV_CHECK_FATAL(std::randomize(VAR_), MSG_, ID_)
`endif



class mem_model #(
    int AddrWidth = 64,
    int DataWidth = 64
) extends uvm_object;

  localparam int MaskWidth = DataWidth / 8;

  typedef logic [AddrWidth-1:0] mem_addr_t;
  typedef logic [DataWidth-1:0] mem_data_t;
  typedef logic [MaskWidth-1:0] mem_mask_t;

  logic [7:0] system_memory[mem_addr_t];

  `uvm_object_param_utils(mem_model#(AddrWidth, DataWidth))

  `uvm_object_new

  function void init();
    system_memory.delete();
  endfunction

  function int get_written_bytes();
    return system_memory.size();
  endfunction


  function void write_byte(mem_addr_t addr, logic [7:0] data);
    //`uvm_info("MEM_MODEL", $sformatf("system_memory[0x%0h]: %0h ",addr,data), UVM_LOW)
    system_memory[addr] = data;
  endfunction


  function void write(input mem_addr_t addr, mem_data_t data, mem_mask_t mask = '1);
    bit [7:0] byte_data;
    for (int i = 0; i < DataWidth / 8; i++) begin
      if (mask[0]) begin
        byte_data = data[7:0];
        write_byte(addr + i, byte_data);
      end
      data = data >> 8;
      mask = mask >> 1;
    end
  endfunction


  function byte_arr_t get_bytes_from_mem(mem_addr_t base, int length);
    byte_arr_t byte_arr;
    byte_arr = new[length];
    for (int i = 0; i<length; i++) begin
      byte_arr[i] = system_memory[base+i];
    end
    return byte_arr;
  endfunction : get_bytes_from_mem


  function void push_bytes_in_mem(mem_addr_t base, byte_arr_t byte_arr);
    foreach(byte_arr[i]) begin
      system_memory[base+i] = byte_arr[i];
    end
  endfunction : push_bytes_in_mem


  function bit [7:0] read_byte(mem_addr_t addr);
    bit [7:0] data;
    if (addr_exists(addr)) begin
      data = system_memory[addr];
      `uvm_info(`gfn, $sformatf("Read Mem  : Addr[0x%0h], Data[0x%0h]", addr, data), UVM_HIGH)
    end else begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `uvm_error(`gfn, $sformatf("read from uninitialized addr 0x%0h", addr))
    end
    return data;
  endfunction


  function mem_data_t read(mem_addr_t addr, mem_mask_t mask = '1);
    mem_data_t data;
    for (int i = DataWidth / 8 - 1; i >= 0; i--) begin
      data = data << 8;
      if (mask[MaskWidth-1]) data[7:0] = read_byte(addr + i);
      else data[7:0] = 0;
      mask = mask << 1;
    end
    return data;
  endfunction : read


  function void compare_byte(mem_addr_t addr, logic [7:0] act_data);
    `uvm_info(`gfn, $sformatf(
              "Compare Mem : Addr[0x%0h], Act Data[0x%0h], Exp Data[0x%0h]",
              addr,
              act_data,
              system_memory[addr]
              ), UVM_HIGH)
    `DV_CHECK_CASE_EQ(act_data, system_memory[addr], $sformatf("addr 0x%0h read out mismatch", addr
                      ))
  endfunction


  function void compare(mem_addr_t addr, mem_data_t act_data, mem_mask_t mask = '1,
                        bit compare_exist_addr_only = 1);
    bit [7:0] byte_data;
    for (int i = 0; i < DataWidth / 8; i++) begin
      mem_addr_t byte_addr = addr + i;
      byte_data = act_data[7:0];
      if (mask[0]) begin
        if (addr_exists(byte_addr)) begin
          compare_byte(byte_addr, byte_data);
        end else if (!compare_exist_addr_only) begin
          `uvm_error(`gfn, $sformatf("address 0x%0x not exists", byte_addr))
        end
      end else begin
        // Nothing to do here: since this byte wasn't selected by the mask, there are no
        // requirements about what data came back.
      end
      act_data = act_data >> 8;
      mask = mask >> 1;
    end
  endfunction : compare


  //ToDO: implement
  function void copy_mem_range_src2dst(mem_addr_t src_base, mem_addr_t dst_base, int length, bit compare_addr_exists=1);
    mem_addr_t src_addr;
    mem_addr_t dst_addr;

    for (int incr = 0; incr<length; incr++) begin
      src_addr = src_base+incr;
      dst_addr = dst_base+incr;

      if (!addr_exists(src_addr)) begin
        if (compare_addr_exists) begin
          `uvm_error(`gfn, $sformatf("address 0x%0x does not exist", src_addr))
          system_memory[src_addr] = $random();
        end
        else begin
          `uvm_warning(`gfn, $sformatf("address 0x%0x does not exist", src_addr))
          system_memory[src_addr] = 0;
        end
      end

      system_memory[dst_addr] = system_memory[src_addr];
      //system_memory[dst_addr] = src_addr;
    end
  endfunction : copy_mem_range_src2dst


  function void patch_memory(mem_addr_t src_base, int start_word_num, int num_bytes, byte_arr_t patch_bytes);
    for (int i = 0; i<num_bytes; i++ ) begin
      system_memory[src_base + start_word_num*8 + i] = system_memory[src_base + start_word_num*8 + i] + patch_bytes[i];
    end
  endfunction : patch_memory

  
  function void patch_address_in_mem(mem_addr_t src_base, int start_word_num, int num_bytes, int addr_patch);
    int patched_addr;
    
    //get current address stored in memory 
    //for (int i = 0; i<num_bytes; i++ ) begin
    //  patched_addr[(i+1)*8-1:i*8-1] = system_memory[src_base + start_word_num*8 + i];
    //end
    for (int i = num_bytes-1; i>=0; i-- ) begin
      patched_addr[8:0] = system_memory[src_base + start_word_num*8 + i];
      patched_addr = patched_addr<<8;
    end

    //apply address patch
    patched_addr += addr_patch;

    //update memory with the patched address
    //for (int i = 0; i<num_bytes; i++ ) begin
    //  system_memory[src_base + start_word_num*8 + i] = patched_addr[(i+1)*8-1:i*8-1];
    //end
    for (int i = 0; i<num_bytes; i++ ) begin
      system_memory[src_base + start_word_num*8 + i] = patched_addr[8:0];
      patched_addr = patched_addr>>8;
    end
  endfunction : patch_address_in_mem


  function bit addr_exists(mem_addr_t addr);
    return system_memory.exists(addr);
  endfunction

  //print the touched memory 
  function void print_memory();
    `uvm_info("MEMORY_MODEL",$sformatf("system_memory--------------------------"),UVM_LOW)
    foreach (system_memory[addr])
    begin
      `uvm_info("MEMORY_MODEL",$sformatf("system_memory[%0h]: %0h",addr,system_memory[addr]),UVM_LOW)
    end 
  endfunction : print_memory


  function void print_memory_part_bytes(mem_addr_t base, mem_addr_t top, string part_name);
    //print each byte address
    foreach(system_memory[addr])
    begin 
      if (addr inside {[base:top]})
        `uvm_info("MEMORY_MODEL",$sformatf("%0s[0x%0h] = %0h", part_name, addr, system_memory[addr]),UVM_LOW)
    end 
  endfunction : print_memory_part_bytes


  function void print_memory_part_words(mem_addr_t base, mem_addr_t top, string part_name);
    //mem_addr_t tmp_addr;
    mem_addr_t prev_worda_base = 0;
    mem_addr_t crt_worda_base  = 0;
    mem_data_t word_data;
    bit [7:0] byte_arr[8];
    bit byte_added_to_word;
    
    //print only words 
    foreach(system_memory[addr])
    if (addr inside {[base:top]})
    begin 
      //get word range for this address
      crt_worda_base = addr;
      crt_worda_base[2:0] = 0;  //word align
      //`uvm_info("MEMORY_MODEL",$sformatf("Addr: 0x%0h  Crt_word: 0x%0h  Prv_word: 0x%0h", addr, crt_worda_base, prev_worda_base),UVM_LOW)

      byte_arr[addr[2:0]] = system_memory[addr];
      if (addr[2:0]==7) begin //last byte from word
        //print word
        word_data = {<<8{byte_arr}};
        `uvm_info("MEMORY_MODEL",$sformatf("%0s[0x%0h] = 0x%16h", part_name, crt_worda_base, word_data),UVM_LOW)
        
        //initialize byte array
        prev_worda_base = crt_worda_base;
        byte_arr = '{0,0,0,0, 0,0,0,0};
      end
    end

    //print last word
    if (crt_worda_base!=prev_worda_base) begin
      word_data = {<<8{byte_arr}};
      `uvm_info("MEMORY_MODEL",$sformatf("%0s[0x%0h] = 0x%16h", part_name, crt_worda_base, word_data),UVM_LOW)
    end
  endfunction : print_memory_part_words


  function void print_memory_part(mem_addr_t base, mem_addr_t top, string part_name, bit print_bytes=0);
    `uvm_info("MEMORY_MODEL",$sformatf("system_memory partition %0s [0x%0h : 0x%0h]", part_name, base, top),UVM_LOW)

    if (print_bytes) begin
      print_memory_part_bytes(base, top, part_name);
    end 
    else begin
      print_memory_part_words(base, top, part_name);
    end
  endfunction : print_memory_part


endclass



`endif  // GUARD_AI_CORE_CD_MEM_MODEL_SVH



