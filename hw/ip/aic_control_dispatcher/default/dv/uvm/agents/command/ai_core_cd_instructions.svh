// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: gbratu

`ifndef GUARD_AI_CORE_CD_INSTRUCTIONS_SVH
`define GUARD_AI_CORE_CD_INSTRUCTIONS_SVH

`define TMS_ID_SIZE 2 

typedef enum bit[1:0] {
  CMD = 0, //command copy
  PRG = 2, //program copy
  TKN = 1, //token
  TMS = 3 //timestamp
} instr_type_enum;

typedef enum logic[5:0] {
  CONS_LOC  = 0, //cosume  local
  PROD_LOC  = 1, //produce local
  CONS_GLOB = 2, //cosume  global
  PROD_GLOB = 3, //produce global
  ERR_MAP_BIT2 = 6'b??_?1??, //Error on MAPPED bit 2
  ERR_MAP_BIT3 = 6'b??_1???, //Error on MAPPED bit 3
  ERR_MAP_BIT4 = 6'b?1_????, //Error on MAPPED bit 4
  ERR_MAP_BIT5 = 6'b1?_????  //Error on MAPPED bit 5
} token_type_enum;


class ai_core_cd_instruction extends uvm_sequence_item;

  static int  gen_instr_num;
  int         instr_id;    //unique instr_id
  rand int    instr_idx;   //can be used to show/track order (within instr list, queue or otherwise) 
  int         command_ids[$];   //references the commands which target this instruction  | unique ID
  int         command_idxs[$];  //references the commands which target this instruction  | command_list[idx]

  rand bit    error;
  rand instr_type_enum instr_type;
  rand token_type_enum token_type;

  constraint c_no_error {
    soft error == 0;
  }


  `uvm_object_utils_begin(ai_core_cd_instruction)
    //`uvm_field_enum(instr_type_enum, instr_type, UVM_DEFAULT)
    `uvm_field_int(  error,            UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(  instr_id,         UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(  instr_idx,        UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_queue_int(command_ids,  UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_queue_int(command_idxs, UVM_NOCOMPARE | UVM_NOPACK)
  `uvm_object_utils_end


  function new(string name = "");
    super.new(name);
    instr_id = gen_instr_num;
    gen_instr_num++;
  endfunction : new


  function string description_str();
  endfunction : description_str

  virtual function void do_print(uvm_printer printer);
  endfunction : do_print
  

  virtual function void do_pack(uvm_packer packer);
    super.do_pack(packer);
  endfunction : do_pack
  
  
  virtual function void do_unpack(uvm_packer packer);
    super.do_unpack(packer);
  endfunction : do_unpack
  
  
  function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    bit result;
    ai_core_cd_instruction rhs_;
    if (!$cast(rhs_, rhs))
      `uvm_fatal(get_type_name(), "Cast of rhs object failed")
    result = super.do_compare(rhs, comparer);
    return result;
  endfunction : do_compare

endclass : ai_core_cd_instruction


class ai_core_cd_cmd_instr extends ai_core_cd_instruction;
  //rand instr_type_enum instr_type;
  rand bit [5:0] dst_id;
  rand bit [3*8-1:0] cmd_ptr;
  rand bit [1*8-1:0] patch_id0;
  rand bit [1*8-1:0] patch_id1;
  rand bit [1*8-1:0] length;
  rand bit [1*8-1:0] patch_mode;

  constraint c_instr_type {
    instr_type == CMD;
  }

  `uvm_object_utils_begin(ai_core_cd_cmd_instr)
    //`uvm_field_int(  error,            UVM_DEFAULT ^ UVM_NOCOMPARE ^ UVM_NOPACK)
    `uvm_field_int(  patch_mode,            UVM_DEFAULT)
    `uvm_field_int(  length,            UVM_DEFAULT)
    `uvm_field_int(  patch_id1,            UVM_DEFAULT)
    `uvm_field_int(  patch_id0,            UVM_DEFAULT)
    `uvm_field_int(  cmd_ptr,            UVM_DEFAULT)
    `uvm_field_int(  dst_id,            UVM_DEFAULT)
    `uvm_field_enum( instr_type_enum, instr_type,            UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction : new


  function string description_str();
  endfunction : description_str

  //extern virtual function void do_pack(uvm_packer packer);
  //extern virtual function void do_unpack(uvm_packer packer);
  virtual function bit  do_compare(uvm_object rhs, uvm_comparer comparer);
  endfunction : do_compare

  virtual function void do_print(uvm_printer printer);
  endfunction : do_print

endclass : ai_core_cd_cmd_instr


class ai_core_cd_prg_instr extends ai_core_cd_instruction;
  //rand instr_type_enum instr_type;
  rand bit [5:0] dst_id;
  rand bit [3*8-1:0] prg_ptr;
  rand bit [2*8-1:0] dst_addr;
  rand bit [2*8-1:0] length;

  constraint c_instr_type {
    instr_type == PRG;
  }

  `uvm_object_utils_begin(ai_core_cd_prg_instr)
    //`uvm_field_int(  error,            UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(  length,            UVM_DEFAULT)
    `uvm_field_int(  dst_addr,            UVM_DEFAULT)
    `uvm_field_int(  prg_ptr,            UVM_DEFAULT)
    `uvm_field_int(  dst_id,            UVM_DEFAULT)
    `uvm_field_enum( instr_type_enum, instr_type,            UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction : new


  function string description_str();
  endfunction : description_str

  //extern virtual function void do_pack(uvm_packer packer);
  //extern virtual function void do_unpack(uvm_packer packer);
  virtual function bit  do_compare(uvm_object rhs, uvm_comparer comparer);
  endfunction : do_compare

  virtual function void do_print(uvm_printer printer);
  endfunction : do_print

endclass : ai_core_cd_prg_instr


class ai_core_cd_timestamp_instr extends ai_core_cd_instruction;

  //rand instr_type_enum instr_type;
  rand bit [5:0] reserved_0;
  rand bit [`TMS_ID_SIZE-1:0] tms_id;
  rand bit [7*8-1-`TMS_ID_SIZE:0] reserved_1;

  constraint c_instr_type {
    instr_type == TMS;
  }
  constraint c_reserved_0 {
    reserved_0 == 0;
  }
  constraint c_reserved_1 {
    reserved_1 == 0;
  }

  `uvm_object_utils_begin(ai_core_cd_timestamp_instr)
    //`uvm_field_int(  error,            UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(  reserved_1,            UVM_DEFAULT)
    `uvm_field_int(  tms_id,            UVM_DEFAULT)
    `uvm_field_int(  reserved_0,            UVM_DEFAULT)
    `uvm_field_enum( instr_type_enum, instr_type,            UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction : new


  function string description_str();
  endfunction : description_str

  //extern virtual function void do_pack(uvm_packer packer);
  //extern virtual function void do_unpack(uvm_packer packer);
  extern virtual function bit  do_compare(uvm_object rhs, uvm_comparer comparer);

  virtual function void do_print(uvm_printer printer);
  endfunction : do_print


endclass : ai_core_cd_timestamp_instr


//function void ai_core_cd_timestamp_instr::do_pack(uvm_packer packer);
//  super.do_pack(packer);
//  `uvm_pack_enum(instr_type)
//  `uvm_pack_int(reserved_0)
//  `uvm_pack_int(tms_id)
//  `uvm_pack_int(reserved_1)
//endfunction : do_pack
//
//
//function void ai_core_cd_timestamp_instr::do_unpack(uvm_packer packer);
//  super.do_unpack(packer);
//  `uvm_pack_enum(instr_type)
//  `uvm_unpack_int(reserved_0)
//  `uvm_unpack_int(tms_id)
//  `uvm_unpack_int(reserved_1)
//endfunction : do_unpack


function bit ai_core_cd_timestamp_instr::do_compare(uvm_object rhs, uvm_comparer comparer);
  bit result;
  ai_core_cd_timestamp_instr rhs_;
  if (!$cast(rhs_, rhs))
    `uvm_fatal(get_type_name(), "Cast of rhs object failed")
  result = super.do_compare(rhs, comparer);
  result &= comparer.compare_field("instr_type", instr_type,   rhs_.instr_type,  $bits(instr_type));
  result &= comparer.compare_field("reserved_0", reserved_0, rhs_.reserved_0, $bits(reserved_0));
  result &= comparer.compare_field("tms_id", tms_id, rhs_.tms_id, $bits(tms_id));
  result &= comparer.compare_field("reserved_1", reserved_1, rhs_.reserved_1, $bits(reserved_1));
  return result;
endfunction : do_compare





class ai_core_cd_token_instr extends ai_core_cd_instruction;

  //rand instr_type_enum instr_type;
  //rand token_type_enum token_type;
  rand bit [3*8-1:0] token_num;
  rand bit [4*8-1:0] reserved_0;

  constraint c_instr_type {
    instr_type == TKN;
  }
  constraint c_reserved_0 {
    reserved_0 == 0;
  }

  `uvm_object_utils_begin(ai_core_cd_token_instr)
    //`uvm_field_int(  error,            UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(  reserved_0,                  UVM_DEFAULT)
    `uvm_field_int(  token_num,                   UVM_DEFAULT)
    `uvm_field_enum( token_type_enum, token_type, UVM_DEFAULT)
    `uvm_field_enum( instr_type_enum, instr_type, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction : new


  function string description_str();
  endfunction : description_str

  //extern virtual function void do_pack(uvm_packer packer);
  //extern virtual function void do_unpack(uvm_packer packer);
  extern virtual function bit  do_compare(uvm_object rhs, uvm_comparer comparer);

  virtual function void do_print(uvm_printer printer);
  endfunction : do_print

endclass : ai_core_cd_token_instr


//function void ai_core_cd_token_instr::do_pack(uvm_packer packer);
//  super.do_pack(packer);
//  `uvm_pack_enum(instr_type)
//  `uvm_pack_enum(token_type)
//  `uvm_pack_int(token_num)
//  `uvm_pack_int(reserved_0)
//endfunction : do_pack
//
//
//function void ai_core_cd_token_instr::do_unpack(uvm_packer packer);
//  super.do_unpack(packer);
//  `uvm_pack_enum(instr_type)
//  `uvm_pack_enum(token_type)
//  `uvm_unpack_int(token_num)
//  `uvm_unpack_int(reserved_0)
//endfunction : do_unpack


function bit ai_core_cd_token_instr::do_compare(uvm_object rhs, uvm_comparer comparer);
  bit result;
  ai_core_cd_token_instr rhs_;
  if (!$cast(rhs_, rhs))
    `uvm_fatal(get_type_name(), "Cast of rhs object failed")
  result = super.do_compare(rhs, comparer);
  result &= comparer.compare_field("instr_type", instr_type,   rhs_.instr_type,  $bits(instr_type));
  result &= comparer.compare_field("token_type", token_type, rhs_.token_type, $bits(token_type));
  result &= comparer.compare_field("token_num", token_num, rhs_.token_num, $bits(token_num));
  result &= comparer.compare_field("reserved_0", reserved_0, rhs_.reserved_0, $bits(reserved_0));
  return result;
endfunction : do_compare






class ai_core_cd_instruction_list#(int INSTR_L_MAX=256) extends uvm_object;

  static int  instr_list_id;

  rand int length;
  rand ai_core_cd_instruction instr_list[];


  constraint c_instr_indexes {
    foreach (instr_list[i])
      instr_list[i].instr_idx == i;
  }

  constraint c_length_one {
    soft length == 1;
  }

  constraint c_debug {
    foreach (instr_list[i])
      soft instr_list[i].instr_type == TMS;
  }

  constraint c_instr_list_size {
    instr_list.size() == length;
  }


  `uvm_object_utils_begin(ai_core_cd_instruction_list)
    `uvm_field_int(  length,            UVM_DEFAULT | UVM_NOCOMPARE)
  `uvm_object_utils_end


  function new(string name = "");
    super.new(name);    
    instr_list_id++;
  endfunction : new

  function void pre_randomize();
    instr_list = new[INSTR_L_MAX];
    foreach(instr_list[i])
      instr_list[i] = ai_core_cd_instruction::type_id::create($sformatf("instr_list[%0d]",i));
  endfunction 
  
  function void post_randomize();
    ai_core_cd_timestamp_instr tmp_timestamp;
    ai_core_cd_token_instr tmp_token;
    foreach (instr_list[i]) begin
  
      case (instr_list[i].instr_type)
        TMS : begin tmp_timestamp = new(); tmp_timestamp.randomize(); instr_list[i] = tmp_timestamp; end
        TKN : begin tmp_token     = new(); tmp_token.randomize() with { tmp_token.token_type == instr_list[i].token_type; };     instr_list[i] = tmp_token; end 
      endcase
    end 
  endfunction: post_randomize


  function string description_str();
  endfunction : description_str

  virtual function void do_print(uvm_printer printer);
  endfunction : do_print
  

  function void do_pack(uvm_packer packer);
    super.do_pack(packer);
  endfunction : do_pack

  
  function void do_unpack(uvm_packer packer);
    super.do_unpack(packer);
  endfunction : do_unpack
  
  
  function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    bit result;
    ai_core_cd_timestamp_instr rhs_;
    if (!$cast(rhs_, rhs))
      `uvm_fatal(get_type_name(), "Cast of rhs object failed")
    result = super.do_compare(rhs, comparer);
    return result;
  endfunction : do_compare

endclass : ai_core_cd_instruction_list








`endif // GUARD_AI_CORE_CD_INSTRUCTIONS_SVH

