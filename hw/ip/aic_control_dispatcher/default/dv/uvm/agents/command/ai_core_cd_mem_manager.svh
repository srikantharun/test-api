// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: gbratu

`ifndef GUARD_AI_CORE_CD_MEM_MANAGER_SVH
`define GUARD_AI_CORE_CD_MEM_MANAGER_SVH

`define INSTR_ID 0

struct {
    bit[63:0] start_addr;  
    rand bit[63:0] end_addr;
} mem_partition;

class ai_core_cd_mem_manager#(int CMD_L_MAX=64, INSTR_L_MAX=256) extends uvm_component;

  // --- MEM MANAGER FIELDS --- //
    rand int mem_size;           //words  //ToDO; redefine with base and top if we want to use just a subsection of the memory -> helps with address space randomization
    rand int mem_partition_num;
    rand int spm_partition_idx;  //defines where in the memory space the SPM sits Bl1 ... SPM ...  BlN
    

    //define seperation between task list, cmd and prg spaces inside the SPM partition
    rand int offset_tsk2base;    //bytes
    rand int offset_cmd2tsk;     //bytes
    rand int offset_prg2cmd;     //bytes
    
    rand int command_list_size;  //number of commands to be sent to ACD
    rand int task_list_size;     // total number of instructions in SPM //this has to fit within the SPM partition - space for the cmd and prg mem
    rand int cmd_mem_size;       //words
    rand int prg_mem_size;       //words
    //keep task_list_size + cmd_mem_size + prg_mem_size + offset_tsk2base + offset_cmd2tsk + offset_prg2cmd <=  (mem_size/mem_partition_num)

    rand ai_core_cd_command     command_list[];
    rand ai_core_cd_instruction_list task_list;

    ////ai_core_cd_instruction task_list[];
    //bit[63:0] ai_core_mem_top;
    //// bit[63:0] ref_mem[];

    axe_uvm_memory_allocator          m_mem_allocator;
    ////rand mem_partition mem_part[];  //SPM is always defined at the last array idx
    //
    axe_uvm_memory_range mem_part[];  //SPM is always defined at the last array idx
    axe_uvm_memory_range spm_part[];  
    mem_model ref_mem;
  
      
  // --- REF MODEL FIELDS --- //
    virtual ai_core_cd_tms_if  tms_vif;
    virtual ai_core_cd_done_if done_vif;
    mem_access_st exp_instr_rd_addr_q[$]; //used to track instr rd operations from SPM
    mem_access_st exp_copy_rd_addr_q[$];  //used to track PRG and CMD rd operations from SPM
    mem_access_st exp_copy_wr_addr_q[$];  //used to track PRG and CMD wr operations to Endpoints
    timestamp_t   exp_timestamp_q[$];     //used to track timestamps
    int command_q_count;
    int instr_q_count;
  
  // --- CONSTRAINTS --- //
    constraint c_mem_size {
        mem_size > 0;
    }
    constraint c_mem_partition_num {
        mem_partition_num > 0;
    }

    constraint c_spm_partition_idx {
        solve mem_partition_num before spm_partition_idx;
        soft spm_partition_idx == mem_partition_num-1; //SPM is always defined at the last array idx
        spm_partition_idx >= 0;
        spm_partition_idx <= mem_partition_num-1;
    }

    constraint c_dbg_constraints {
        soft mem_size <= 100;
        soft mem_partition_num <= 2;
    }



    //constraint c_ref_mem {
    //    ref_mem.size() == mem_size;
    //}

    constraint c_command_list_size {
        soft command_list_size <= 16;
    }

    constraint c_command_list {
        command_list.size() == command_list_size;
        //solve command_list_size before command_list;
        foreach (command_list[i])
        {
            command_list[i].command_idx == i;
            command_list[i].task_list_ptr inside {[0:task_list_size-1]};
            command_list[i].length inside {[0:task_list_size-command_list[i].task_list_ptr]};
        }
    }

    constraint c_instr_list_size {
        //task_list_size <= 10;
        task_list.length == task_list_size;
        solve task_list_size before task_list.length;
    }


    `uvm_component_utils_begin(ai_core_cd_mem_manager)
    `uvm_object_utils_end
  
  
  // --- INHERITED METHODS - UVM_COMPONENT --- //
    function new(string name = "ai_core_cd_mem_manager", uvm_component parent = null);
        super.new(name, parent);

         `uvm_info("new", "Exiting...", UVM_LOW)
    endfunction : new

    
    function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW)
        super.build_phase(phase);   

         // Memory Allocator
        `uvm_info("ACD_MEM_MANAGER",$sformatf("Mmeory alocator b4 create: \n%0p",m_mem_allocator),UVM_LOW) 
        m_mem_allocator = axe_uvm_memory_allocator::type_id::create("m_mem_allocator", this);
        ref_mem = mem_model#(64,64)::type_id::create("ref_mem", this);
        `uvm_info("ACD_MEM_MANAGER",$sformatf("Mmeory alocator after create: \n%0p",m_mem_allocator),UVM_LOW) 

        `uvm_info("build_phase", "Exiting...", UVM_LOW)
    endfunction : build_phase


    
    function void connect_phase(uvm_phase phase);
        `uvm_info("connect_phase", "Entered...", UVM_LOW)
        super.connect_phase(phase);

        if(!uvm_config_db#(virtual ai_core_cd_tms_if)::get(this, "", "tms_vif", tms_vif))
            `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
            
        if(!uvm_config_db#(virtual ai_core_cd_done_if)::get(this, "", "done_vif", done_vif))
            `uvm_fatal(get_full_name(), "Failed to get vif handle from config_db")
        
        `uvm_info("connect_phase", "Exiting...", UVM_LOW)
    endfunction : connect_phase


    function string description_str();
    endfunction : description_str


    virtual function void do_print(uvm_printer printer);    
    endfunction : do_print


    function void pre_randomize();
        //command_list = new[command_list_size];CMD_L_MAX
        command_list = new[CMD_L_MAX];
        foreach (command_list[i])
            command_list[i] = ai_core_cd_command::type_id::create($sformatf("command_list[%0d]",i));

        task_list = ai_core_cd_instruction_list#(INSTR_L_MAX)::type_id::create($sformatf("task_list"));

        `uvm_info("pre_randomize", "Exiting...", UVM_LOW)
    endfunction

    function void post_randomize();
        axe_uvm_memory_range mem_range;
        bit [63:0] addr;

        `uvm_info("ACD_MEM_MANAGER",$sformatf("task_list length: %0d",task_list.length),UVM_LOW)
        `uvm_info("ACD_MEM_MANAGER",$sformatf("task_list: %0p",task_list),UVM_LOW)
        foreach(task_list.instr_list[i])
            `uvm_info("ACD_MEM_MANAGER",$sformatf("Instr_%2d: \n%0p",i,task_list.instr_list[i]),UVM_LOW) 
        foreach(command_list[i])
            `uvm_info("ACD_MEM_MANAGER",$sformatf("Command_%2d: \n%0p",i,command_list[i]),UVM_LOW) 


        `uvm_info("ACD_MEM_MANAGER",$sformatf("Mem partitions_numm: %0d",mem_partition_num),UVM_LOW) 
        mem_part = new[mem_partition_num]; //number of AI Core Blocks + SPM
        foreach (mem_part[i])
            mem_part[i] = axe_uvm_memory_range::type_id::create($sformatf("mem_part[%0d]",i));
        spm_part = new[3]; //SPM has 3 parts INSTR, CMD, PRG
        foreach (spm_part[i])
            spm_part[i] = axe_uvm_memory_range::type_id::create($sformatf("spm_part[%0d]",i));

         // Memory Allocator
        m_mem_allocator.base           = 0;
        m_mem_allocator.top            = mem_size*8 - 1;
        m_mem_allocator.partition_size = mem_size*8 / mem_partition_num;
        `uvm_info("ACD_MEM_MANAGER",$sformatf("Mmeory alocator b4 initialize: \n%0p",m_mem_allocator),UVM_LOW) 
        
        m_mem_allocator.available.delete();
        m_mem_allocator.reserved.delete();
        m_mem_allocator.initialize();
        
        //`uvm_info("ACD_MEM_MANAGER",$sformatf("Created mem alocator"),UVM_LOW)
        uvm_config_db#(axe_uvm_memory_allocator)::set(this,                                       "m_*", "m_mem_allocator", m_mem_allocator);     
        //`uvm_info("ACD_MEM_MANAGER",$sformatf("Set mem alocator to config db"),UVM_LOW)

    
        //mem_part = new[mem_partition_num];
        `uvm_info("ACD_MEM_MANAGER",$sformatf("Initialized mem_part"),UVM_LOW)

        for (int i = 0; i < mem_partition_num; i++) begin
            mem_range = new();
            mem_range = m_mem_allocator.allocate();
            mem_part[i] = mem_range;
            //`uvm_info("ACD_MEM_MANAGER",$sformatf("Mem partition[%0d]:  [[0x%0h : 0x%0h]] ",i,mem_part[i].base,i,mem_part[i].base),UVM_LOW)
            `uvm_info("ACD_MEM_MANAGER",$sformatf("Mem partition[%0d]:  [[0x%0h : 0x%0h]] ",i, mem_part[i].base, mem_part[i].top),UVM_LOW)
        end 

         `uvm_info("ACD_MEM_MANAGER",$sformatf("spm_partition_idx = %0d",spm_partition_idx),UVM_LOW)
         `uvm_info("ACD_MEM_MANAGER",$sformatf("cmd_mem_size = %0d",cmd_mem_size),UVM_LOW)
         `uvm_info("ACD_MEM_MANAGER",$sformatf("prg_mem_size = %0d",prg_mem_size),UVM_LOW)
         `uvm_info("ACD_MEM_MANAGER",$sformatf("Allocated partitions"),UVM_LOW)

        //define the SPM partitions
        //spm_partition_idx = 0;
        override_spm_partition_space();

        addr = mem_part[spm_partition_idx].base;
        
        addr += offset_tsk2base;
        mem_range = new($sformatf("0x%x-0x%x", addr, addr+task_list_size-1), addr, addr+task_list_size*8-1);
        spm_part[0] = mem_range;  //TASK LIST PARTITION
        addr += task_list_size*8;

        addr += offset_cmd2tsk;
        mem_range = new($sformatf("0x%x-0x%x", addr, addr+cmd_mem_size-1), addr, addr+cmd_mem_size*8-1);
        spm_part[1] = mem_range; //CMD PARTITION
        addr += cmd_mem_size*8;
        
        addr += offset_prg2cmd;
        mem_range = new($sformatf("0x%x-0x%x", addr, addr+prg_mem_size-1), addr, addr+prg_mem_size*8-1);
        spm_part[2] = mem_range; //PRG PARTITION
        addr += prg_mem_size*8-1;

        foreach (spm_part[i])
            `uvm_info("ACD_MEM_MANAGER",$sformatf("SPM partition[%0d]:  [[0x%0h : 0x%0h]] ",i, spm_part[i].base, spm_part[i].top),UVM_LOW)

        //check we have not exceeded the SPM partition 
        //if (addr > mem_part[spm_partition_idx].top)
        //    `uvm_fatal("ACD_MEM_MANAGER",$sformatf("SPM Partition alocation exceeded SPM space. SPM Top: %0h  |  Addr: %0h",mem_part[spm_partition_idx].top,addr))
    
        
        `uvm_info("post_randomize", "Exiting...", UVM_LOW)
    endfunction : post_randomize
  
    function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        eot_check_expected_queues();
    endfunction : check_phase
  
  // --- CONSTRAINT AND METHOD PSEUDO --- //
    // //command constraints
    // A <= TP < B
    // TP + TLlen < TLtop
    // C <= CtrlO < E
    // 
    // //instruction constraints
    // CtrlO + cmd_ptr + cmd_len <= E
    // CtrlO + prg_ptr + prg_len <= E
    // 
    // //GENERATION FLOW
    // generate commands
    // generate instructions
    // 
    // foreach of the commands
    //     go over the targeted instructions and update the cmd_id targetting them
    // 
    // 
    // //resolve_offset_cmd2instr_precedence
    // foreach of the instructions 
    //     update the cmd_ptr, prg_ptr and len as to not exceed the partition space (E addr)
    // 
    // //resolve_offset_instr2cmd_precedence
    // foreach of the instructions 
    //     update the cmd[cmd_id].offset as to not exceed the partition space (E addr)
  
  
  // --- ENV METHODS --- //
    
    virtual task monitor_timestamp_if();
        forever begin
            //@(tms_vif.mon iff tms_vif.mon.timestamp_active_pulse == 1)
            @(tms_vif.mon)
            if (tms_vif.timestamp_active_pulse == 1) begin
                `uvm_info("TMS_MON",$sformatf("Detected Active:%0d Timespamp ID:%0d", tms_vif.timestamp_active_pulse, tms_vif.timestamp_id),UVM_LOW)
            
                add_actual_timestamp(tms_vif.timestamp_id);
            end

        end
    endtask : monitor_timestamp_if
  
  // --- MEM MANAGER METHODS --- //

    function void associate_cmd_instr_ids();
        int instr_idx_base;
        int instr_list_length;

        foreach (command_list[cmd_idx])
        begin
            command_list[cmd_idx].command_idx = cmd_idx; //assignment not necessarily needed since it is kep in the constraints

            //instr_idx_base = command_list[cmd_idx].task_list_ptr - offset_tsk2base; //instr_list[0] sits at SPM base + offset_tsk2base
            instr_idx_base = command_list[cmd_idx].task_list_ptr;
            instr_list_length = command_list[cmd_idx].length;

            for (int instr_idx= instr_idx_base; instr_idx < instr_idx_base + instr_list_length; instr_idx++)
            begin 
                 `uvm_info("MEM_MANAGER",$sformatf("instr_idx_base: %0d | instr_idx: %0d", instr_idx_base, instr_idx),UVM_LOW)
                task_list.instr_list[instr_idx].command_ids.push_back(command_list[cmd_idx].command_id);
                command_list[cmd_idx].instr_ids.push_back(task_list.instr_list[instr_idx].instr_id);
            end 

            for (int instr_idx= instr_idx_base; instr_idx < instr_idx_base + instr_list_length; instr_idx++)
            begin 
                 `uvm_info("MEM_MANAGER",$sformatf("instr_idx_base: %0d | instr_idx: %0d", instr_idx_base, instr_idx),UVM_LOW)
                task_list.instr_list[instr_idx].command_idxs.push_back(cmd_idx);
                command_list[cmd_idx].instr_idxs.push_back(instr_idx);
            end 
        end
    endfunction : associate_cmd_instr_ids

    //makes sure that the program makes sense from a token consume / produce standpoint as to not get ACD stuck
    //This is only needed if we have a token counter which DESIGN says that we do not
    function void cleanup_token_order_for_commands(); 
        //global_token_num
        //local_token_num

        //go through every command

        //go through every instr that the crt command is targetting 

        //if the instr is a token instr

        //if produce token -> then increment the counter

        //if consume token 
          //if counter is 0 -> then change the instruction to produce and increment the counter

          //else -> decrement the counter
    endfunction : cleanup_token_order_for_commands


    function void resolve_offset_cmd2instr_precedence();
    endfunction : resolve_offset_cmd2instr_precedence


    function void resolve_offset_instr2cmd_precedence();
        ai_core_cd_instruction t_instr;
        ai_core_cd_cmd_instr t_cmd_instr;
        ai_core_cd_prg_instr t_prg_instr;

        foreach (task_list.instr_list[instr_idx]) begin
            t_instr = task_list.instr_list[instr_idx];
            case (t_instr.instr_type)
                CMD : begin
                    if(!$cast(t_cmd_instr, t_instr))
                        `uvm_fatal(get_type_name(), "Cast of rhs object failed")
                end

                PRG : begin
                    if(!$cast(t_prg_instr, t_instr))
                        `uvm_fatal(get_type_name(), "Cast of rhs object failed")

                end
            endcase 
        end
    endfunction : resolve_offset_instr2cmd_precedence


    function void update_command_instr_ptrs();
        foreach (command_list[cmd_idx])
            command_list[cmd_idx].task_list_ptr = command_list[cmd_idx].task_list_ptr*8 + offset_tsk2base;
    endfunction : update_command_instr_ptrs


    //copies data from one mem space to another 
    function void execute_copy(bit[64-1:0] src_base, bit[64-1:0] dst_src_base, int length);
        ref_mem.copy_mem_range_src2dst(src_base, dst_src_base, length);
    endfunction : execute_copy



    //patches address in the indicated mem space 
    function void execute_addr_patch(bit[64-1:0] src_base, int start_word_num, int num_bytes, int addr_patch);
        //ToDO: implement address patching 
        //for now we will just do a regular copy instead 
        //execute_copy(src_base, dst_src_base, length);
        ref_mem.patch_address_in_mem(src_base, start_word_num, num_bytes, addr_patch);
    endfunction : execute_addr_patch


    function void initialize();
        `uvm_info("MEM_MANAGER",$sformatf("command_list_size = %0d",command_list_size),UVM_LOW)
        `uvm_info("MEM_MANAGER",$sformatf("Command_list.size() = %0d",command_list.size()),UVM_LOW)
        `uvm_info("MEM_MANAGER",$sformatf("Instr_list.size() = %0d",task_list.instr_list.size()),UVM_LOW)

        `uvm_info("MEM_MANAGER","Generated the following command and instr list",UVM_LOW)
        foreach(command_list[i])
            `uvm_info("MEM_MANAGER",$sformatf("Command[%0d] : %0p",i,command_list[i].sprint()),UVM_LOW)
        foreach(task_list.instr_list[i])
            `uvm_info("MEM_MANAGER",$sformatf("Instr[%0d] : %0p",i,task_list.instr_list[i].sprint()),UVM_LOW)


        override_cmd_list();    //hooks for the user to use specific commmands
        override_instr_list();  //hooks for the user to use specific instructions

        if (1==1) begin  //ToDO: add a toggle 
            resolve_offset_instr2cmd_precedence();
        end
        else 
        begin
            resolve_offset_cmd2instr_precedence();
        end


        associate_cmd_instr_ids();  //esablish relationship between commands and targetted instructions
        `uvm_info("MEM_MANAGER","Updated the following command and instr list",UVM_LOW)
        foreach(command_list[i])
            `uvm_info("MEM_MANAGER",$sformatf("Command[%0d] : %0p",i,command_list[i].sprint()),UVM_LOW)
        foreach(task_list.instr_list[i])
            `uvm_info("MEM_MANAGER",$sformatf("Instr[%0d] : %0p",i,task_list.instr_list[i].sprint()),UVM_LOW)


        update_command_instr_ptrs(); //update the command pointers to reflect the SPM TASK List partition space 
        `uvm_info("MEM_MANAGER","Updated the following command task_list_pointers",UVM_LOW)
        foreach(command_list[i])
            `uvm_info("MEM_MANAGER",$sformatf("Command[%0d] : %0p",i,command_list[i].sprint()),UVM_LOW)


        cleanup_token_order_for_commands(); //makes sure we have enough tokens to consume so as not to get ACD stuck


        `uvm_info("MEM_MANAGER","Populating Memory",UVM_LOW)
        populate_spm();


        //foreach(ref_mem[i]) begin
        //    `uvm_info("ACD_MEM_MANAGER",$sformatf("Ref_mem[%0d] : %0h",i,ref_mem[i]),UVM_LOW)
        //end

        //print generated SPM contents 
        print_partitions(mem_part, "mem_part");
        print_partitions(spm_part, "spm_part");

        ref_mem.print_memory_part(mem_part[spm_partition_idx].base, mem_part[spm_partition_idx].top ,"spm_part");

        //`uvm_info("MEM_MANAGER","Printing ref mem ",UVM_LOW)
        //ref_mem.print_memory();
    endfunction : initialize


    virtual function void start_of_simulation_phase(uvm_phase phase);
        `uvm_info("start_of_simulation_phase", "Entered...",UVM_LOW)

        `uvm_info("start_of_simulation_phase", "Exiting...",UVM_LOW)
    endfunction : start_of_simulation_phase


    task run_phase(uvm_phase phase);
      `uvm_info("run_phase", "Entered...", UVM_LOW)
      super.run_phase(phase);
      reset_done_vif(); //this method will be moved to ACD driver

      //start monitoring tasks
      fork begin
          fork
            monitor_timestamp_if();
          join_none
      end join

      `uvm_info("run_phase", "Exiting...", UVM_LOW)
    endtask : run_phase


    function void print_partitions(axe_uvm_memory_range partition[], string part_name);
        `uvm_info("MEM_MANAGER",$sformatf("Mem space %0s has %0d partitions \n ----------------------------------",
                                            part_name, partition.size()),UVM_LOW)
        foreach(partition[i])
            `uvm_info("MEM_MANAGER",$sformatf("%0s[%0d] : [[%0h:%0h]]",part_name, i, partition[i].base, partition[i].top),UVM_LOW)
    endfunction : print_partitions


    function void gen_rand_data_in_mem(bit[63:0] base, bit[63:0] top);
        bit[63:0] data;
        //for (bit[63:0] addr=base; addr<=top; addr++)
        for (bit[63:0] addr=top; addr>=base; addr--)
        begin
            if (addr[2:0] == 0) begin
                data = $urandom();
                ref_mem.write(addr,data,0-1);
            end
        end
    endfunction : gen_rand_data_in_mem
    

    function void push_instr_data_in_mem(bit[63:0] base, bit[63:0] top);
        bit[63:0] data;
        bit[63:0] addr=base;
        bit data_array[];
        //check that base address is aligned
        //ToDO

        foreach (task_list.instr_list[i]) 
        begin
            task_list.instr_list[i].pack(data_array);


            `uvm_info("MEM_MANAGER",$sformatf("Instruction: \n%0s",task_list.instr_list[i].sprint()),UVM_LOW)
            `uvm_info("MEM_MANAGER",$sformatf("data_array.size(): %0d",data_array.size()),UVM_LOW)
            `uvm_info("MEM_MANAGER",$sformatf("data_array:  \n%0p",data_array),UVM_LOW)

            data = {>>{data_array}};

            `uvm_info("MEM_MANAGER",$sformatf("Instruction to pack: \n%p",task_list.instr_list[i]),UVM_LOW)
            `uvm_info("MEM_MANAGER",$sformatf("Instruction packed:  \n%0h",data),UVM_LOW)

            ref_mem.write(addr,data,0-1);
            addr = addr+8;
        end

        //check that we did not exceed top address with current instruction list 
        addr--;
        if (addr>top)
            `uvm_fatal("MEM_MANAGER",$sformatf("Last Populated Instr Addr: 0x%0h  exceeded Partition Top: 0x%0h", addr,top));
    endfunction : push_instr_data_in_mem


    function void populate_spm();
        foreach (spm_part[mp_iter]) begin
            //grab addresses 
            bit[63:0] base = spm_part[mp_iter].base;
            bit[63:0] top = spm_part[mp_iter].top;

            case(mp_iter)
                0 : begin
                    `uvm_info("MEM_MANAGER",$sformatf("push_instr_data_in_mem(0x%0h,0x%0h)",base,top),UVM_LOW)
                    //populate the memory with the task list
                    push_instr_data_in_mem(base,top);
                end
                default : begin
                    `uvm_info("MEM_MANAGER",$sformatf("gen_rand_data_in_mem(0x%0h,0x%0h)",base,top),UVM_LOW)
                    //populate the memory with random data 
                    gen_rand_data_in_mem(base,top);
                end
            endcase
        end
    endfunction : populate_spm


    function void print_spm_memory();
    endfunction : print_spm_memory


    virtual function void compare_ref_to_svt();
        //ToDO: implement this method to compare reference memory addr_range data to SVT address range data
        `uvm_error("REF_MODEL","METHOD IS NOT IMPLEMENTED: compare_ref_to_svt()")
    endfunction : compare_ref_to_svt


    //function void get_data()  //returns data array for a give mem space
    //function void get_instr_list()  //retuns the instruction list of a give length starting from the indicated address 
    //function void get_rand_instr_list_addr() //return a random addressing within the instr list space
    //function void get_rand_cmd_prg_addr()
  
  
  // --- REF MODEL METHODS --- //

    virtual function void reset_done_vif();
        done_vif.done_o ='b0;
    endfunction : reset_done_vif


    virtual function void add_actual_timestamp(int id);
        timestamp_t exp_tms;
        
        //check that queue is not empty
        if (exp_timestamp_q.size() == 0) begin
            `uvm_fatal("REF_MODEL",$sformatf("Queue is empty for received timestamp ID: %0d", id))
        end
    
        //get item from queue
        exp_tms = exp_timestamp_q.pop_front();

        //ToDO: compare item and print details 
        if (exp_tms.tms_id !== id) begin
            `uvm_error("REF_MODEL",$sformatf("Did not match TIMESTAMP ID.  EXP:%0d  ACT:%0d",exp_tms.tms_id,id))
        end
        `uvm_info("REF_MODEL",$sformatf("Compared TIMESTAMP trans: %0p",exp_tms),UVM_LOW)

        //remove instruction from queue or decrement instr_q_count
        if (instr_q_count > 0) begin
            instr_q_count--;
        end
        else begin
            `uvm_fatal("REF_MODEL","instr_q_count is already 0")
        end

    endfunction : add_actual_timestamp


    virtual function void receive_addr_from_svt(svt_axi_transaction::xact_type_enum xact_type, int x_id, svt_axi_transaction::resp_type_enum bresp,  bit[64-1:0] addr_range[$]); 
        `uvm_info("MEM_MANAGER_CALLBACK","This was printed from the AXI SVT monitor ",UVM_LOW)

        `uvm_info("MEM_MANAGER_CALLBACK",$sformatf("ACD X_ID: %0h %0p the following addresses: \n %0p",x_id, xact_type, addr_range),UVM_LOW)


        //if status of the transaction is FAILED
        if (bresp != svt_axi_transaction::OKAY) begin
            if (xact_type == svt_axi_transaction::READ) begin
                //ToDO: what field in the trans differenciated between the two?
                //irq_status["COPY_AXI_READ_RESP_SLVERR"]     = data_from_reg[17];
                //env.aicd_refmodel.set_irq_status("COPY_AXI_READ_RESP_SLVERR");  //handle_irq_status();
                //irq_status["COPY_AXI_READ_RESP_DECERR"]     = data_from_reg[18];
                //env.aicd_refmodel.set_irq_status("COPY_AXI_READ_RESP_DECERR"); //handle_irq_status();
            end 
            
            if (xact_type == svt_axi_transaction::READ) begin
                //ToDO: what field in the trans differenciated between the two?
                //irq_status["COPY_AXI_WRITE_RESP_SLVERR"]    = data_from_reg[19];
                //env.aicd_refmodel.set_irq_status("COPY_AXI_WRITE_RESP_SLVERR");  //handle_irq_status();
                //irq_status["COPY_AXI_WRITE_RESP_DECERR"]    = data_from_reg[20];
                //env.aicd_refmodel.set_irq_status("COPY_AXI_WRITE_RESP_DECERR");  //handle_irq_status();
            end 

            //return;  
            //TODO: how do we end the test in this case. The Stored expected will mismatch from here on out. Do we add an exception handler?
        end 

        //compare the address range with the expected address range for the particular operation RD/WR X ID
        case (xact_type)
            svt_axi_transaction::READ : begin
                if (x_id == `INSTR_ID) begin
                    compare_actual_to_expected_addr_access_q(addr_range, exp_instr_rd_addr_q, $sformatf("X_ID:%0d READ ACCESS", x_id));
                end 
                else begin
                    compare_actual_to_expected_addr_access_q(addr_range, exp_copy_rd_addr_q, $sformatf("X_ID:%0d READ ACCESS", x_id));
                end
            end
            svt_axi_transaction::WRITE : begin
                compare_actual_to_expected_addr_access_q(addr_range, exp_copy_wr_addr_q, $sformatf("X_ID:%0d WRITE ACCESS", x_id), 1);
            end
            default : `uvm_fatal("REF_MODEL","UNKNOWN CASE BRANCH")
        endcase 
    endfunction : receive_addr_from_svt


    function void check_is_0(int mvar, string var_name, fatal=0);
        if (mvar != 0) begin
             if (fatal) begin
                 `uvm_fatal("ZERO_CHECK",$sformatf("VAR %0s is not 0. %0s=%0d", var_name, var_name, mvar))
             end
             else begin
                 `uvm_error("ZERO_CHECK",$sformatf("VAR %0s is not 0. %0s=%0d", var_name, var_name, mvar))
             end
        end
    endfunction : check_is_0


    function void eot_check_expected_queues();
        general_q_manipulator#(mem_access_st) memaccess_q_man;
        general_q_manipulator#(timestamp_t) timestamp_q_man;

        
        memaccess_q_man.check_q_is_empty(exp_instr_rd_addr_q, "exp_instr_rd_addr_q");
        memaccess_q_man.check_q_is_empty(exp_copy_rd_addr_q,  "exp_copy_rd_addr_q");
        memaccess_q_man.check_q_is_empty(exp_copy_wr_addr_q,  "exp_copy_wr_addr_q");
        timestamp_q_man.check_q_is_empty(exp_timestamp_q,     "exp_timestamp_q");

        check_is_0(command_q_count, "command_q_count");
        check_is_0(instr_q_count,   "instr_q_count");

        //if (exp_instr_rd_addr_q.size())
        //    `uvm_error("REF_MODEL","QUEUE exp_instr_rd_addr_q IS NOT EMPTY AT EOT")
        //if (exp_copy_rd_addr_q.size())
        //    `uvm_error("REF_MODEL","QUEUE exp_copy_rd_addr_q IS NOT EMPTY AT EOT")
        //if (exp_copy_wr_addr_q.size())
        //    `uvm_error("REF_MODEL","QUEUE exp_copy_wr_addr_q IS NOT EMPTY AT EOT")        
        //if (exp_timestamp_q.size())
        //    `uvm_error("REF_MODEL","QUEUE exp_timestamp_q IS NOT EMPTY AT EOT")
    endfunction : eot_check_expected_queues


    //compare the received addr access from monitor with the targeted expected queue
    function void compare_actual_to_expected_addr_access_q(bit[64-1:0] addr_range[$], ref mem_access_st exp_addr_q[$], input string access_name="", decrq_on_last_write=0);
        mem_access_st mem_access;
        string pstr;

        
        $swriteh(pstr,"%0p", addr_range);
        `uvm_info("REF_MODEL",$sformatf("Comparing access %0s actual_addr_range:  %p", access_name, pstr),UVM_LOW)
        foreach(addr_range[i])
            begin
            //check that queue has elements in it
            if (exp_addr_q.size() == 0)
                `uvm_fatal("REF_MODEL",$sformatf("Queue is empty for received access %0s", access_name))

            mem_access = exp_addr_q.pop_front();
            if (mem_access.addr !== addr_range[i])
            begin
                $swriteh(pstr,"%0p", mem_access);
                `uvm_info("REF_MODEL",$sformatf("Crt expected addr for access %0s is:  %s", access_name, pstr),UVM_LOW)
                //print information about the command and instruction
                `uvm_error("REF_MODEL",$sformatf("Address did not match for access: %0s. Exp: %0h Act: %0h  || %s", 
                    access_name, mem_access.addr, addr_range[i], pstr ))
            end
            else begin
                $swriteh(pstr,"%0p", mem_access);
                `uvm_info("REF_MODEL",$sformatf("Crt expected addr for access %0s is:  %s", access_name, pstr),UVM_LOW)
                `uvm_info("REF_MODEL",$sformatf("Matched access %0s ADDR  %0h", access_name, addr_range[i]),UVM_LOW)
            end


            //ToDO: if this is the last address for the command or instruction then trigger 
                //decrease cmd or instr q size 
                //trigger memory checks for the address range 
            if (mem_access.addr == mem_access.range_top) //ToDO: Does the condition change slightly for unaligned addressing?
            begin
                //if this access is command driven
                if (mem_access.instr_idx < 0) begin
                    //ToDO: pull out the command from the command queue 
                    //until the command queue is implemented we will implement a command counter instead
                    if (command_q_count==0) begin
                        `uvm_fatal("SANITY_CHECK","Command Q already empty");
                    end
                    command_q_count--;  //all instr copy operations have finished so ACD can remove the CMD from its FIFO
                end
                else begin //if this access is instruction driven 
                    if (decrq_on_last_write==1) begin
                        //ToDO: pull out the instruction from the instr queue //until the command queue is implemented we will implement a command counter instead
                        if (instr_q_count==0) begin
                            `uvm_fatal("SANITY_CHECK","Instruction Q already empty");
                        end
                        instr_q_count--;  //all instr copy operations have finished so ACD can remove the INSTR from its FIFO
    
                        //ToDO: compare partial memory
                        compare_ref_to_svt();  //whe should consider if other copy operations are underway to the same addresses (even partial range) then we might have a mismatch when comparing to reference (data updates in TB ref (mem model) not yet transferred to RTL(SVT))
                    end 
                end 
            end

            //if it matches then all good 
            //if it does not match > print the accessed address range then the expected addr range with the associated instr/ cmd that failed, timestamp and everything

            //add method to remove/mark as complete the expected instruction with instr/cmd_ID provided by the address rand once the last addr per that instr is noticed
            //on the instruction/cmd removal check that the ID matches and that the order is correct -> copies do not happen before timestamp -> actually the order check will be performed by the cmd/instr remove method itself
    
        end
    endfunction : compare_actual_to_expected_addr_access_q


  // --- DEBUG / CONSTRAIN / OVERRIDE METHODS --- //
    //ToDO: ToDO: ToDO: review where these methods are called and ensure no debug code is left active 

    virtual function void override_cmd_list();
        foreach (command_list[i])
        begin
            command_list[i].control_offset = 0;
            command_list[i].length = 2;        //inside {[0:task_list_size-command_list[i].task_list_ptr]};
            command_list[i].task_list_ptr = 0; //inside {[0:task_list_size-1]}
        end
    endfunction : override_cmd_list


    function void override_instr_list_timestamp();
        ai_core_cd_timestamp_instr tms_instr;
        tms_instr.gen_instr_num = 0; //reset the instructions ids

        foreach(task_list.instr_list[i])
        begin
            tms_instr = ai_core_cd_timestamp_instr::type_id::create("tms_instr", this);
            if (!tms_instr.randomize() with {
                instr_idx == i;
            })
                `uvm_fatal("MEM_MANAGER","Randomization failed")
            
            task_list.instr_list[i] = tms_instr;
        end
    endfunction : override_instr_list_timestamp


    function void override_instr_list_token_with_errors();
        ai_core_cd_token_instr tkn_instr;
        tkn_instr.gen_instr_num = 0; //reset the instructions ids

        foreach(task_list.instr_list[i])
        begin
            tkn_instr = ai_core_cd_token_instr::type_id::create("tkn_instr", this);
            if (!tkn_instr.randomize() with {
                instr_idx == i;
            })
                `uvm_fatal("MEM_MANAGER","Randomization failed")
            
            task_list.instr_list[i] = tkn_instr;
        end
    endfunction : override_instr_list_token_with_errors


    function void override_instr_list_token();
        ai_core_cd_token_instr tkn_instr;
        tkn_instr.gen_instr_num = 0; //reset the instructions ids

        foreach(task_list.instr_list[i])
        begin
            tkn_instr = ai_core_cd_token_instr::type_id::create("tkn_instr", this);
            if (!tkn_instr.randomize() with {
                instr_idx == i;
                token_type inside {CONS_LOC,  PROD_LOC } -> token_num < 2**17 -1; //ToDO: replace 17 with cfg param
                token_type inside {CONS_GLOB, PROD_GLOB} -> token_num < 2**7  -1; //ToDO: replace 17 with cfg param
                solve token_type before token_num;
            })
                `uvm_fatal("MEM_MANAGER","Randomization failed")
            
            task_list.instr_list[i] = tkn_instr;
        end
    endfunction : override_instr_list_token


    function void override_instr_list_prg();
        ai_core_cd_prg_instr prg_instr;
        prg_instr.gen_instr_num = 0; //reset the instructions ids

        foreach(task_list.instr_list[i])
        begin
            prg_instr = ai_core_cd_prg_instr::type_id::create("prg_instr", this);
            if (!prg_instr.randomize() with {
                instr_idx == i;
                dst_id <=17;  //ToDO: replace 17 with cfg param
                prg_ptr >= spm_part[2].base;
                prg_ptr <= spm_part[2].top;
                prg_ptr[2:0] == 0;
                dst_addr inside {['h200:'h300]};
                dst_addr[2:0] == prg_ptr[2:0]; //unalignment should match between the two
                length <= prg_mem_size - (spm_part[2].top - prg_ptr);
                solve prg_ptr before length;
                solve prg_ptr before dst_addr;  //need to match alignment between the two
            })
                `uvm_fatal("MEM_MANAGER","Randomization failed")
            
            //just to have a lower word-aligned data and incremental value / independed of randomization //ToDO: remove these 2 lines after debug
            prg_instr.length = (i+1)*8;

            //copy gen instr to list
            task_list.instr_list[i] = prg_instr;
        end
    endfunction : override_instr_list_prg


    function void override_instr_list_prg_unaligned_addr();
        ai_core_cd_prg_instr prg_instr;
        prg_instr.gen_instr_num = 0; //reset the instructions ids

        foreach(task_list.instr_list[i])
        begin
            prg_instr = ai_core_cd_prg_instr::type_id::create("prg_instr", this);
            if (!prg_instr.randomize() with {
                instr_idx == i;
                dst_id <=17;  //ToDO: replace 17 with cfg param
                dst_addr inside {['h200:'h300]};
                dst_addr[2:0] == prg_ptr[2:0]; //unalignment should match between the two
                prg_ptr >= spm_part[2].base;
                prg_ptr <= spm_part[2].top;
                length <= prg_mem_size - (spm_part[2].top - prg_ptr);
                solve prg_ptr before length;
                solve prg_ptr before dst_addr;  //need to match alignment between the two
            })
                `uvm_fatal("MEM_MANAGER","Randomization failed")
            
            //just to have a lower and incremental value / independed of randomization //ToDO: remove these 2 lines after debug
            prg_instr.length = 16+i*2;
            prg_instr.prg_ptr[2:0] = prg_instr.dst_addr[2:0];  //this is a mandatory constraint (spec)

            //copy gen instr to list
            task_list.instr_list[i] = prg_instr;
        end
    endfunction : override_instr_list_prg_unaligned_addr


    function void override_instr_list_cmd();
        ai_core_cd_cmd_instr cmd_instr;
        cmd_instr.gen_instr_num = 0; //reset the instructions ids

        foreach(task_list.instr_list[i])
        begin
            cmd_instr = ai_core_cd_cmd_instr::type_id::create("cmd_instr", this);
            if (!cmd_instr.randomize() with {
                instr_idx == i;
                dst_id <= 17; //ToDO: replace 17 with cfg param
                patch_mode == 0;
                patch_id0 == 0;
                patch_id1 == 0;

                cmd_ptr >= spm_part[1].base;
                cmd_ptr <= spm_part[1].top;
                cmd_ptr %8 == 0;
                length <= cmd_mem_size - (spm_part[1].top - cmd_ptr);
                length %8 == 0;
                solve cmd_ptr before length;
            })
                `uvm_fatal("MEM_MANAGER","Randomization failed")
            
            //just to have a lower and incremental value / independed of randomization //ToDO: remove this line after debug
            cmd_instr.cmd_ptr[2:0] = 0;
            cmd_instr.length = 8+i*8;

            //copy gen instr to list
            task_list.instr_list[i] = cmd_instr;
        end
    endfunction : override_instr_list_cmd


    virtual function void override_instr_list(); 
        //override_instr_list_timestamp();
        //override_instr_list_token_with_errors();
        //override_instr_list_token();
        override_instr_list_prg();
        //override_instr_list_prg_unaligned_addr();
        //override_instr_list_cmd();
    endfunction : override_instr_list


    //ToDO: remove this
    function void override_spm_partition_space();
        `uvm_info("ACD_MEM_MANAGER",$sformatf("spm_partition_idx: %0d",spm_partition_idx),UVM_LOW)
        mem_part[spm_partition_idx].base =   0;   //start from 0 until the configuration register is properly handled
        mem_part[spm_partition_idx].top  = 100; //random value chose to accomodate the 3 SPM partitions 
    endfunction : override_spm_partition_space

    //function add_expected_address

    //function void generate_cmd_list

    //function void execute_instr_cmd()
    //function void execute_instr_prg()
    //function void execute_instr_tkn()
    //function void execute_instr_tms()

    //function void copy_mem_ref2svt();

    //function void apply_address_patching();
    //function void get_address_from_cmd();
    //function void get_address_from_prg();

endclass : ai_core_cd_mem_manager



`endif // GUARD_AI_CORE_CD_MEM_MANAGER_SVH



