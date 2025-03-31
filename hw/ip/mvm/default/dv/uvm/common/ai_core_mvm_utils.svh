`ifndef AI_CORE_MVM_UTILS_SVH
`define AI_CORE_MVM_UTILS_SVH

class mvm_prg_cmd_tb_data extends uvm_object;

  rand struct {
  rand bit [7:0] extra;
  rand bit [7:0] a_s;
  rand bit [7:0] a_u_pw;
  rand bit [7:0] a_t_pw;
  rand bit [7:0] wb_u_pw;
  rand bit [7:0] wb_t_pw;
  } mvm_prg_cmd_struct;

  /** Variable that enables the randomization of the token information in the header. If disabled, then the token information will be equal to 0 */
  rand bit enable_tokens;

  /** Variable that represents the header of the command */
  rand mvm_cmd_header_t header;


  //rand mvm_prg_cmd_struct_z mvm_prg_cmd_struct;
  bit [AXI_LT_DATA_WIDTH -1: 0] mvm_prg_cmd_data;
  bit [7: 0] mvm_prg_row_width;
  bit [7: 0] mvm_prg_column_width;
  int ifdw_burst_len[$];
  /******************************************************************************************************************************
  Op_code	0	// CMDB descriptor operation codes0=MVM_PRG_CMDB_WR_WB_OPC (MVM-DP write weights)
  A_s	0..IMC_NB_WEIGHT_SETS-1	IMC weights set to be programmed
  A_u_pw	0..7	Programming row offset
  A_t_pw	0..7	Programming column offset
  Wb_u_pw	0..7	Programming row size, a value 0 maps to 1x64(PW gran) rows, a value of 7 maps to 8x64(PW gran) rows
  Wb_t_pw	0..7	Programming column size, a value 0 maps to 1x64(PW gran) cols, a value of 7 maps to 8x64(PW gran) cols
  *******************************************************************************************************************************/

  constraint mvm_prg_cmd_a_s_c     { mvm_prg_cmd_struct.a_s     < WEIGHT_SETS;}
  // Avoid overflow from 512x512
  constraint mvm_prg_cmd_a_u_pw_wb_u_pw_c  { soft (mvm_prg_cmd_struct.a_u_pw + mvm_prg_cmd_struct.wb_u_pw) < 9;}
  constraint mvm_prg_cmd_a_t_pw_wb_t_pw_c  { soft (mvm_prg_cmd_struct.a_t_pw + mvm_prg_cmd_struct.wb_t_pw) < 8;}

  constraint c_sanity_header {
    header.rsvd == 0;
    header.token_cons inside {[0:3]};
    header.token_prod inside {[0:3]};

    soft enable_tokens == 1'b0; //by default tokens are disabled
    
    if(enable_tokens == 1'b0) {
      header.token_cons == 1'b0;
      header.token_prod == 1'b0;
    }
  }

  constraint c_prg_mode { soft mvm_prg_cmd_struct.extra == 1'b0;}

   
  function new(string name = "mvm_prg_cmd_tb_data");
  super.new(name);
  endfunction : new

  function void post_randomize();
    mvm_prg_cmd_data = {mvm_prg_cmd_struct.wb_t_pw,mvm_prg_cmd_struct.wb_u_pw,
                        mvm_prg_cmd_struct.a_t_pw,mvm_prg_cmd_struct.a_u_pw,
                        mvm_prg_cmd_struct.a_s,mvm_prg_cmd_struct.extra};
     mvm_prg_row_width = {mvm_prg_cmd_struct.wb_u_pw + 1};
     mvm_prg_column_width = {mvm_prg_cmd_struct.wb_t_pw + 1};
     ifdw_burst_len = {};
     ifdw_burst_len.push_back(MATRIX * mvm_prg_row_width * mvm_prg_column_width);
  endfunction : post_randomize

  `uvm_object_utils_begin(mvm_prg_cmd_tb_data)
    `uvm_field_int(mvm_prg_cmd_struct.extra  , UVM_ALL_ON) 
    `uvm_field_int(mvm_prg_cmd_struct.a_s    , UVM_ALL_ON)
    `uvm_field_int(mvm_prg_cmd_struct.a_u_pw , UVM_ALL_ON)
    `uvm_field_int(mvm_prg_cmd_struct.a_t_pw , UVM_ALL_ON)
    `uvm_field_int(mvm_prg_cmd_struct.wb_u_pw, UVM_ALL_ON)
    `uvm_field_int(mvm_prg_cmd_struct.wb_t_pw, UVM_ALL_ON)
    `uvm_field_int(header.token_cons         , UVM_ALL_ON)
    `uvm_field_int(header.token_prod         , UVM_ALL_ON)
    `uvm_field_int(header.cmd_id             , UVM_ALL_ON)
    `uvm_field_int(mvm_prg_cmd_data, UVM_ALL_ON)
    `uvm_field_int(mvm_prg_row_width, UVM_ALL_ON)
    `uvm_field_int(mvm_prg_column_width, UVM_ALL_ON)
    `uvm_field_queue_int(ifdw_burst_len, UVM_ALL_ON)
  `uvm_object_utils_end

endclass : mvm_prg_cmd_tb_data



class mvm_exe_instr_tb_data extends uvm_object;

  rand struct {
    rand bit [1:0] a_s;
    rand bit [3:0] a_u_pw;
    rand bit [2:0] a_t_pw;
    rand bit [3:0] wb_u_pw;
    rand bit [2:0] wb_t_pw;
  } mvm_exe_instr_struct;


  bit [AXI_LT_DATA_WIDTH -1: 0] mvm_exe_instr_data;
  bit [3: 0] mvm_exe_instr_input_size;
  bit [3: 0] mvm_exe_instr_output_size;
  bit [AXI_LT_DATA_WIDTH-1:0] concurrent_prg_data;

  /******************************************************************************************************************************
  A_s	0..IMC_NB_WEIGHT_SETS-1	IMC weights to be used for compute
  A_u_pw	0..8	Compute row offset (input offset)
  A_t_pw	0..7	Compute column offset (output offset)
  Wb_u_pw	0..8	Compute row size (input size) A value of 0 maps to an operation on 1 PW, a value of 7 maps to an operation on 8 PWs
  Wb_t_pw	0..7	Compute column size (output size) A value of 0 maps to an operation on 1PW, a value of 7 maps to an operation on 8PWs
  *******************************************************************************************************************************/

  constraint mvm_exe_instr_a_s_c     { mvm_exe_instr_struct.a_s     < WEIGHT_SETS;}
  // Avoid overflow from 512x512
  constraint mvm_exe_instr_a_u_pw_wb_u_pw_c  { soft (mvm_exe_instr_struct.a_u_pw + mvm_exe_instr_struct.wb_u_pw) < 9;}
  constraint mvm_exe_instr_a_t_pw_wb_t_pw_c  { soft (mvm_exe_instr_struct.a_t_pw + mvm_exe_instr_struct.wb_t_pw) < 8;}

  function new(string name = "mvm_exe_instr_tb_data");
  super.new(name);
  endfunction : new

  function void post_randomize();
    mvm_exe_instr_data = {mvm_exe_instr_struct.wb_t_pw,mvm_exe_instr_struct.wb_u_pw,
                        mvm_exe_instr_struct.a_t_pw,mvm_exe_instr_struct.a_u_pw,
                        mvm_exe_instr_struct.a_s};
    mvm_exe_instr_input_size  =  mvm_exe_instr_struct.wb_u_pw + 1;
    mvm_exe_instr_output_size =  mvm_exe_instr_struct.wb_t_pw + 1;
  endfunction : post_randomize

  `uvm_object_utils_begin(mvm_exe_instr_tb_data)
    `uvm_field_int(mvm_exe_instr_struct.a_s    , UVM_ALL_ON)
    `uvm_field_int(mvm_exe_instr_struct.a_u_pw , UVM_ALL_ON)
    `uvm_field_int(mvm_exe_instr_struct.a_t_pw , UVM_ALL_ON)
    `uvm_field_int(mvm_exe_instr_struct.wb_u_pw, UVM_ALL_ON)
    `uvm_field_int(mvm_exe_instr_struct.wb_t_pw, UVM_ALL_ON)
    `uvm_field_int(mvm_exe_instr_data, UVM_ALL_ON)
    `uvm_field_int(mvm_exe_instr_input_size, UVM_ALL_ON)
    `uvm_field_int(mvm_exe_instr_output_size, UVM_ALL_ON)
  `uvm_object_utils_end

endclass : mvm_exe_instr_tb_data

class mvm_exe_instr_tb_data_packet extends uvm_object;

  rand bit [AXI_LT_ADDR_WIDTH -1: 0] mvm_exe_instr_addr[];
  bit [AXI_LT_DATA_WIDTH -1: 0] mvm_exe_instr_data[];
  bit [3: 0] mvm_exe_instr_input_size[256];
  bit [3: 0] mvm_exe_instr_output_size[256];
 

  constraint mvm_exe_instr_addr_c1 { foreach( mvm_exe_instr_addr[i] ) mvm_exe_instr_addr[i] inside {[0:255]}; 
                                     foreach( mvm_exe_instr_addr[i] ) mvm_exe_instr_addr[i] dist {
                                                                                                  [0:25]   := 1,
                                                                                                  [26:50]  := 1,
                                                                                                  [51:75]  := 1,
                                                                                                  [76:100] := 1,
                                                                                                  [101:125]:= 1,
                                                                                                  [126:150]:= 1,
                                                                                                  [151:175]:= 1,
                                                                                                  [176:200]:= 1,
                                                                                                  [201:225]:= 1,
                                                                                                  [226:255]:= 1
                                                                                                 };
                                   }
  constraint mvm_exe_instr_addr_c2 { soft mvm_exe_instr_addr.size dist { [1:10] :/ 50, [50:256] :/ 50 };}

  function new(string name = "mvm_exe_instr_tb_data_packet");
  super.new(name);
  endfunction : new

  function void post_randomize();
    mvm_exe_instr_data = new[mvm_exe_instr_addr.size];
  endfunction : post_randomize

  `uvm_object_utils_begin(mvm_exe_instr_tb_data_packet)
    `uvm_field_array_int(mvm_exe_instr_addr, UVM_ALL_ON)
    `uvm_field_array_int(mvm_exe_instr_data, UVM_ALL_ON)
    `uvm_field_sarray_int(mvm_exe_instr_input_size, UVM_ALL_ON)
    `uvm_field_sarray_int(mvm_exe_instr_output_size, UVM_ALL_ON)
  `uvm_object_utils_end

endclass : mvm_exe_instr_tb_data_packet


class mvm_exe_cmd_tb_data extends uvm_object;

  rand struct {
    rand bit [15:0] loop_ptr;
    rand bit [15:0] loop_len;
    rand bit [23:0] loop_iter;
    rand bit [7:0]  extra;
  } mvm_exe_cmd_struct;

  /** Variable that enables the randomization of the token information in the header. If disabled, then the token information will be equal to 0 */
  rand bit enable_tokens;
  /** Variable that represents the header of the command */
  rand mvm_cmd_header_t header;
  struct {
    bit [15:0]  id;
    bit [15:0]  token_prod;
    bit [15:0]  token_cons;
    bit [7:0]   cmd_format;
    bit [7:0]   rsvd;
  } mvm_exe_cmd_header_struct;

  bit [AXI_LT_DATA_WIDTH -1: 0] mvm_exe_cmd_data;
  bit [15:0]  loop_len;
  bit [15:0]  loop_ptr;
  bit [23:0] loop_iter;
  bit [7:0]  extra; 
  bit [7:0]  loop_len_q[$];
  bit [15:0] loop_ptr_q[$];
  bit [31:0] loop_iter_q[$];
  /******************************************************************************************************************************
  loop_len	1..MVM_EXE_INSTR_MEM_DEPTH-1 //Length of the qcmd section that is repeated by a qcmd iteration
  loop_ptr	0.. MVM_EXE_INSTR_MEM_DEPTH-1	Start pointer for the used qcmd section
  loop_iter	1..2**32-1	Number of iterations to run

  *******************************************************************************************************************************/

  constraint mvm_exe_cmd_loop_len_c   {   mvm_exe_cmd_struct.loop_len	 inside {[1:255]};}
  constraint mvm_exe_cmd_loop_ptr_c   {   (mvm_exe_cmd_struct.loop_len + mvm_exe_cmd_struct.loop_ptr)   <= 256;}
  constraint mvm_exe_cmd_loop_iter_c1 { soft  mvm_exe_cmd_struct.loop_iter  != 0;}
  constraint mvm_exe_cmd_loop_iter_c2 { soft  mvm_exe_cmd_struct.loop_iter dist { [1:10] :/ 100, [11:49] :/50, [50:256] :/ 50 };}  // Change 2**32

  constraint c_sanity_header {
    header.rsvd == 0;
    header.token_cons inside {[0:3]};
    header.token_prod inside {[0:3]};

    soft enable_tokens == 1'b0; //by default tokens are disabled

    if(enable_tokens == 1'b0) {
      header.token_cons == 1'b0;
      header.token_prod == 1'b0;
    }
  }

  constraint mvm_exe_cmd_extra_c { soft mvm_exe_cmd_struct.extra == 0;}  
    
    
  function new(string name = "mvm_exe_cmd_tb_data");
  super.new(name);
  endfunction : new

  function void post_randomize();
    mvm_exe_cmd_data = {mvm_exe_cmd_struct.extra,mvm_exe_cmd_struct.loop_iter,mvm_exe_cmd_struct.loop_len,
                        mvm_exe_cmd_struct.loop_ptr};
    loop_len  = mvm_exe_cmd_struct.loop_len;
    loop_ptr  = mvm_exe_cmd_struct.loop_ptr;
    loop_iter = mvm_exe_cmd_struct.loop_iter;
    extra     = mvm_exe_cmd_struct.extra;
 
    loop_len_q.push_back(loop_len);
    loop_ptr_q.push_back(loop_ptr);
    loop_iter_q.push_back(loop_iter);
  endfunction : post_randomize

  `uvm_object_utils_begin(mvm_exe_cmd_tb_data)
    `uvm_field_int(mvm_exe_cmd_data, UVM_ALL_ON)
    `uvm_field_int(loop_len, UVM_ALL_ON)
    `uvm_field_int(loop_ptr, UVM_ALL_ON)
    `uvm_field_int(loop_iter, UVM_ALL_ON)
    `uvm_field_int(extra, UVM_ALL_ON)     
    `uvm_field_int(header.token_cons , UVM_ALL_ON)
    `uvm_field_int(header.token_prod , UVM_ALL_ON)
    `uvm_field_int(header.cmd_id     , UVM_ALL_ON)
    `uvm_field_queue_int(loop_len_q, UVM_ALL_ON)
    `uvm_field_queue_int(loop_ptr_q, UVM_ALL_ON)
    `uvm_field_queue_int(loop_iter_q, UVM_ALL_ON)
  `uvm_object_utils_end

  endclass : mvm_exe_cmd_tb_data


class mvm_exe_cmd_tb_data_packet extends uvm_object;

  mvm_cmd_header_t               header[$];
  bit [AXI_LT_DATA_WIDTH -1: 0] mvm_exe_cmd_data[$];
  bit [AXI_LT_ADDR_WIDTH -1: 0] mvm_exe_instr_addr_sort[4][$];
  bit [7:0] ptr=0;
  bit [7:0] len =1;
  bit [7:0] current_addr;
  bit [7:0] next_addr;
  bit [7:0] extra;


  function new(string name = "mvm_exe_cmd_tb_data_packet");
  super.new(name);
  endfunction : new


  `uvm_object_utils_begin(mvm_exe_cmd_tb_data_packet)
    `uvm_field_queue_int(mvm_exe_cmd_data	, UVM_ALL_ON)
    `uvm_field_queue_int(mvm_exe_instr_addr_sort[0] , UVM_ALL_ON)
    `uvm_field_queue_int(mvm_exe_instr_addr_sort[1] , UVM_ALL_ON)
    `uvm_field_queue_int(mvm_exe_instr_addr_sort[2] , UVM_ALL_ON)
    `uvm_field_queue_int(mvm_exe_instr_addr_sort[3] , UVM_ALL_ON)
    `uvm_field_int(ptr, UVM_ALL_ON)
    `uvm_field_int(len, UVM_ALL_ON)
    `uvm_field_int(current_addr, UVM_ALL_ON)
    `uvm_field_int(next_addr, UVM_ALL_ON)
    `uvm_field_int(extra, UVM_ALL_ON)
  `uvm_object_utils_end



  virtual function void do_copy(uvm_object rhs);
    mvm_exe_cmd_tb_data_packet seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);

    foreach (seq_rhs.header[i]) begin
      this.header.push_back(seq_rhs.header[i]);
    end
  endfunction
 
endclass : mvm_exe_cmd_tb_data_packet



`endif
