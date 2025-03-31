`ifndef __DPU_CMD_DESCRIPTOR_SEQUENCE__
`define __DPU_CMD_DESCRIPTOR_SEQUENCE__

typedef bit [63:0] bit_64_queue_t[$]; 

class dpu_cmd_descriptor_sequence extends svt_axi_master_base_sequence;
  rand dpu_cmd_descriptor_t cmd_desc;
  rand bit enable_tokens;
  rand int prog_start_addr;
  rand int prog_size;
  rand int prog_iteration;
  rand int base;
  rand int top;
  rand bit start_0; 
  ai_core_dp_cmd_gen_cmdb dp_cmd; 
  constraint cmd_header_token_c {
    cmd_desc.header.h_config    inside {[0:1]};
    cmd_desc.header.triggers    == 0;
    cmd_desc.header.rsvd        == 0;
    cmd_desc.header.rsvd_format == 0;
    cmd_desc.header.token_cons inside {[0:1]};
    cmd_desc.header.token_prod inside {[0:1]};

    soft enable_tokens == 1'b0; //by default tokens are disabled

    if(enable_tokens == 1'b0) {
      cmd_desc.header.token_cons == 1'b0;
      cmd_desc.header.token_prod == 1'b0;
    }
  }

  constraint c_program_size{
    soft cmd_desc.cmd.main_0.iteration   inside {[1:20]};
    soft cmd_desc.cmd.main_1.iteration   inside {[1:20]};
    soft cmd_desc.cmd.main_2.iteration   inside {[1:20]};
    soft cmd_desc.cmd.nested_0.iteration inside {[1:20]};
    soft cmd_desc.cmd.nested_1.iteration inside {[1:20]};

    soft cmd_desc.cmd.main_0.length   inside {[1:PROG_MEM_DEPTH]};
    soft cmd_desc.cmd.main_1.length   inside {[1:PROG_MEM_DEPTH]};
    soft cmd_desc.cmd.main_2.length   inside {[1:PROG_MEM_DEPTH]};
    soft cmd_desc.cmd.nested_0.length inside {[1:PROG_MEM_DEPTH]};
    soft cmd_desc.cmd.nested_1.length inside {[1:PROG_MEM_DEPTH]};

    soft base == 0;
    soft top  == PROG_MEM_DEPTH; 
  }

  `uvm_object_utils(dpu_cmd_descriptor_sequence)
 

  function new(string name = "dpu_cmd_descriptor_sequence");
    super.new(name);
  endfunction


  task body();
    svt_axi_master_transaction write_tran;
    svt_configuration get_cfg;
    bit status;
    int burst_length;
    bit_64_queue_t dpcmd_payload;
    dp_cmd = new();
    dp_cmd.base = base;
    dp_cmd.top  = top;
    `uvm_info(get_name, $sformatf("command parameters: base: %0d, top: %0d format: %s PW32: %b \n", base, top, cmd_desc.header.format.name, cmd_desc.header.h_config[0]), UVM_HIGH)
    `uvm_info(get_name, $sformatf("command parameters: main_0: %p", cmd_desc.cmd.main_0), UVM_HIGH)
    `uvm_info(get_name, $sformatf("command parameters: main_1: %p", cmd_desc.cmd.main_1), UVM_HIGH)
    `uvm_info(get_name, $sformatf("command parameters: main_2: %p", cmd_desc.cmd.main_2), UVM_HIGH)
    `uvm_info(get_name, $sformatf("command parameters: nested_0: %p", cmd_desc.cmd.nested_0), UVM_HIGH)
    `uvm_info(get_name, $sformatf("command parameters: nested_1: %p", cmd_desc.cmd.nested_1), UVM_HIGH)

    assert(dp_cmd.randomize with {
      format             == cmd_desc.header.format;
      valid              == 1;
      extra              == 0;
      if(`_main_0_valid_)   main_0.iteration   == cmd_desc.cmd.main_0.iteration;
      if(`_main_1_valid_)   main_1.iteration   == cmd_desc.cmd.main_1.iteration;
      if(`_main_2_valid_)   main_2.iteration   == cmd_desc.cmd.main_2.iteration;
      if(`_nested_0_valid_) nested_0.iteration == cmd_desc.cmd.nested_0.iteration;
      if(`_nested_1_valid_) nested_1.iteration == cmd_desc.cmd.nested_1.iteration;

      if(`_main_0_valid_)   main_0.length   == cmd_desc.cmd.main_0.length;
      if(`_main_1_valid_)   main_1.length   == cmd_desc.cmd.main_1.length;
      if(`_main_2_valid_)   main_2.length   == cmd_desc.cmd.main_2.length;
      if(`_nested_0_valid_) nested_0.length == cmd_desc.cmd.nested_0.length;
      if(`_nested_1_valid_) nested_1.length == cmd_desc.cmd.nested_1.length;

      if (start_0) {
        main_0.start   == 0;
        main_1.start   == 0;
        main_2.start   == 0;
        nested_0.start == 0;
        nested_1.start == 0;
      }
    });

   dp_cmd.valid             = 1;
   dp_cmd.errors            = 0;

   cmd_desc.cmd.nested_1_map_main = dp_cmd.nested_1_map_main ; 
   cmd_desc.cmd.nested_1          = dp_cmd.nested_1          ; 
   cmd_desc.cmd.nested_0_map_main = dp_cmd.nested_0_map_main ; 
   cmd_desc.cmd.nested_0          = dp_cmd.nested_0          ; 
   cmd_desc.cmd.main_2            = dp_cmd.main_2            ; 
   cmd_desc.cmd.main_1            = dp_cmd.main_1            ; 
   cmd_desc.cmd.extra             = dp_cmd.extra             ; 
   cmd_desc.cmd.main_0            = dp_cmd.main_0            ; 

    dpcmd_payload = decode_cmd(cmd_desc);
    burst_length = dpcmd_payload.size();

    `uvm_info(get_name, $sformatf("writing command descriptor: %p", cmd_desc), UVM_HIGH);
    dp_cmd.print();
    `uvm_info(get_name, $sformatf("main_0: %p", dp_cmd.main_0), UVM_HIGH);
    `uvm_info(get_name, $sformatf("nested_0: %p", dp_cmd.nested_0), UVM_HIGH);
    `uvm_info(get_name, $sformatf("nested_map_main_0: %p", dp_cmd.nested_0_map_main), UVM_HIGH);
    `uvm_create(write_tran)
    write_tran.port_cfg     = cfg;
    write_tran.xact_type    = svt_axi_transaction::WRITE;
    write_tran.addr         = DPU_CMD_ADDR_ST;
    write_tran.burst_type   = svt_axi_transaction::INCR;
    write_tran.burst_size   = svt_axi_transaction::BURST_SIZE_64BIT;
    write_tran.atomic_type  = svt_axi_transaction::NORMAL;

    write_tran.burst_length = burst_length;

    write_tran.data         = new[write_tran.burst_length];
    write_tran.wstrb        = new[write_tran.burst_length];
    write_tran.data_user    = new[write_tran.burst_length];
    write_tran.wvalid_delay = new[write_tran.burst_length];

    foreach (dpcmd_payload[i]) begin
      write_tran.data[i]         = dpcmd_payload[i]; 
      write_tran.wstrb[i]        = 8'hff;
      write_tran.wvalid_delay[i] = $urandom_range(0,4);
    end

    `uvm_send(write_tran)
    get_response(rsp);
  endtask


  function bit_64_queue_t decode_cmd(ref dpu_cmd_descriptor_t cmd);
    bit_64_queue_t payload;
    
    //case BYPASS: only header is sent
    payload.push_back(cmd.header);
    case (cmd.header.format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.nested_0_map_main, cmd.cmd.nested_0});
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.nested_0_map_main, cmd.cmd.nested_0});
        payload.push_back({cmd.cmd.nested_1_map_main, cmd.cmd.nested_1});
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_1});
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_1});
        payload.push_back({cmd.cmd.nested_0_map_main, cmd.cmd.nested_0});
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_1});
        payload.push_back({cmd.cmd.nested_0_map_main, cmd.cmd.nested_0});
        payload.push_back({cmd.cmd.nested_1_map_main, cmd.cmd.nested_1});
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_1});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_2});
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_1});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_2});
        payload.push_back({cmd.cmd.nested_0_map_main, cmd.cmd.nested_0});
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_1});
        payload.push_back({cmd.cmd.reserved_0, cmd.cmd.main_2});
        payload.push_back({cmd.cmd.nested_0_map_main, cmd.cmd.nested_0});
        payload.push_back({cmd.cmd.nested_1_map_main, cmd.cmd.nested_1});
      end
      //invalid cmds : m1n1 format because cmd_fifo expects at least 3 words to them send it to dp_cmd_gen
      default : begin
        `uvm_warning(get_name, $sformatf("%0d format not implemented yet",cmd.header.format));
        payload.push_back({cmd.cmd.extra, cmd.cmd.main_0});
        payload.push_back({cmd.cmd.nested_0_map_main, cmd.cmd.nested_0});
      end
    endcase

    return payload;
  endfunction


endclass

`endif
