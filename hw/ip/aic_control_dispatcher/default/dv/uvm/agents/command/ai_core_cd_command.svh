// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: gbratu

`ifndef GUARD_AI_CORE_CD_COMMAND_SVH
`define GUARD_AI_CORE_CD_COMMAND_SVH

class ai_core_cd_command extends uvm_sequence_item;

    static int  gen_cmd_num;
    int         command_id;     //unique commands_id
    rand int    command_idx;    //can be used to show/track order (within command list, queue or otherwise) 
    int         instr_ids[$];   //references the instructions which are targetted by this command   |  unique ID
    int         instr_idxs[$];  //references the instructions which are targetted by this command   |  instr_list[idx]
    
    //rand bit                                    valid;
    rand logic [1*8-1:0] reserved ;
    rand logic [3*8-1:0] control_offset ;
    rand logic [2*8-1:0] length ;
    rand logic [2*8-1:0] task_list_ptr ;

    rand int                                    delay;

    constraint c_no_delay {
        delay == -1;
    }

    constraint c_reserved_default {
        //reserved == 0;
        reserved == command_id;
    }

    constraint c_length_tl_ptr_order {
        solve task_list_ptr before length;
    }

`uvm_object_utils_begin(ai_core_cd_command)
    `uvm_field_int(  command_id,            UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(  command_idx,           UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_queue_int(instr_ids,         UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_queue_int(instr_idxs,        UVM_NOCOMPARE | UVM_NOPACK)
    `uvm_field_int(  reserved,              UVM_DEFAULT)
    `uvm_field_int(  control_offset,        UVM_DEFAULT)
    `uvm_field_int(  length,                UVM_DEFAULT)
    `uvm_field_int(  task_list_ptr,         UVM_DEFAULT)
`uvm_object_utils_end

function new(string name = "");
    super.new(name);
    command_id = gen_cmd_num;
    gen_cmd_num++;
endfunction : new


function string description_str();
endfunction : description_str


virtual function void do_print(uvm_printer printer);    
endfunction : do_print

endclass : ai_core_cd_command

`endif // GUARD_AI_CORE_CD_COMMAND_SVH



