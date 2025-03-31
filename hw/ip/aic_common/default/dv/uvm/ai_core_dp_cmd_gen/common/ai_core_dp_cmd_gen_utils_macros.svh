`define GET_INPUT_STREAM_INFO(READ_INPUT_COND, INCREMENT) \
  function ai_core_dp_cmd_gen_uvm_pkg::data_stream_cfg_t get_input_stream_info(ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb cmd_info); \
  ai_core_dp_cmd_gen_uvm_pkg::data_stream_cfg_t stream_cfg; \
  int main_start[   3]; \
  int main_end[     3]; \
  int main_iter[    3]; \
  int nested_start[ 2]; \
  int nested_end[   2]; \
  int nested_iter[  2]; \
 \
  /** Initialize main variables (used from program size) */ \
  for (int i=0; i<3; i++) begin \
    if(cmd_info.main_valid(i) && (cmd_info.format!=aic_dp_cmd_gen_pkg::Bypass)) begin \
      main_start[i]   = cmd_info.get_start(     1, i); \
      main_end[i]     = cmd_info.get_end(       1, i); \
      main_iter[i]    = cmd_info.get_iteration( 1, i); \
    end \
  end \
  /** Initialize nested variables */ \
  for (int i=0; i<2; i++) begin \
    if(cmd_info.nested_valid(i) && (cmd_info.format!=aic_dp_cmd_gen_pkg::Bypass)) begin \
      nested_start[i]   = cmd_info.get_start(     0, i); \
      nested_end[i]     = cmd_info.get_end(       0, i); \
      nested_iter[i]    = cmd_info.get_iteration( 0, i); \
    end \
  end \
\
  stream_cfg.main_dt_cnt[0]= 0; \
  stream_cfg.main_dt_cnt[1]= 0; \
  stream_cfg.main_dt_cnt[2]= 0; \
  stream_cfg.nested_dt_cnt[0] = 0; \
  stream_cfg.nested_dt_cnt[1] = 0; \
  /** if main is valid */ \
  for (int main_idx=0; main_idx<3; main_idx++) begin \
    if(cmd_info.main_valid(main_idx)) begin \
      for(int mem_pos = main_start[main_idx]; mem_pos <= main_end[main_idx]; mem_pos++) begin \
        //verify if the current instruction needs input \
        if(READ_INPUT_COND) begin \
          /** if inside nested 1 */ \
          if((cmd_info.get_map_main(1)==main_idx) && cmd_info.nested_valid(1) && (mem_pos inside {[nested_start[1] : nested_end[1]]}) ) begin \
            stream_cfg.nested_dt_cnt[1]+= INCREMENT; \
            `uvm_info("get_input_stream_info", $sformatf("inside nested 1 mem_pos : %0d -> read_input: 1",mem_pos), UVM_FULL) \
          end \
          /** else if it is inside the nested 0 */ \
          else if((cmd_info.get_map_main(0)==main_idx) && cmd_info.nested_valid(0) && (mem_pos inside {[nested_start[0] : nested_end[0]]})) begin \
            stream_cfg.nested_dt_cnt[0]+= INCREMENT; \
            `uvm_info("get_input_stream_info", $sformatf("inside nested 0 mem_pos : %0d -> read_input: 1",mem_pos), UVM_FULL) \
          end \
          else begin \
            stream_cfg.main_dt_cnt[main_idx]+= INCREMENT; \
            `uvm_info("get_input_stream_info", $sformatf("inside main %0d mem_pos : %0d -> read_input: 1",main_idx, mem_pos), UVM_FULL) \
          end \
        end \
      end \
\
      /** multiply the counters by the neccessary iterations */ \
      stream_cfg.main_dt_cnt[main_idx] *=main_iter[main_idx]; \
      //nested 0 \
      if(cmd_info.nested_valid(0) && (cmd_info.get_map_main(0)==main_idx)) begin \
        stream_cfg.nested_dt_cnt[0] *= (main_iter[main_idx]*nested_iter[0]); \
      end \
      //nested 1 \
      if(cmd_info.nested_valid(1) && (cmd_info.get_map_main(1)==main_idx)) begin \
        stream_cfg.nested_dt_cnt[1] *= (main_iter[main_idx]*nested_iter[1]); \
        //if co-nested then we need to multiply also with the nested 0 iteration number \
        if(cmd_info.co_nested() && (!cmd_info.is_parallel())) begin \
          stream_cfg.nested_dt_cnt[1] *= nested_iter[0]; \
        end \
      end \
    end \
  end \
\
  `uvm_info ("body", $sformatf("n of data in stream: %p", stream_cfg), UVM_HIGH) \
  return stream_cfg; \
endfunction : get_input_stream_info

