`ifndef IAU_CMD_DESC_SEQUENCE_SV
`define IAU_CMD_DESC_SEQUENCE_SV

typedef bit [63:0] bit_64_queue_t[$]; 
class iau_cmd_descriptor_sequence extends svt_axi_master_base_sequence;
  rand aic_dp_cmd_gen_pkg::cmdb_cmd_struct_t cmd;   
  rand iau_cmd_header_t header;
  rand bit enable_tokens;
  rand int base;
  rand int top;
  rand bit start_0; 

  ai_core_dp_cmd_gen_cmdb dp_cmd; 
//  constraint cmd_opcode_c     { cmd.cmd_opcode == header.cmd_format;}

  constraint cmd_header_token_c {
    header.h_config    == 0;
    header.triggers    == 0;
    header.rsvd        == 0;
    header.rsvd_format == 0;
    header.token_cons inside {[0:1]};
    header.token_prod inside {[0:1]};

    soft enable_tokens == 1'b0; //by default tokens are disabled

    if(enable_tokens == 1'b0) {
      header.token_cons == 1'b0;
      header.token_prod == 1'b0;
    }
  }

  constraint c_program_size{
    soft cmd.main_0.iteration   inside {[1:20]};
    soft cmd.main_1.iteration   inside {[1:20]};
    soft cmd.main_2.iteration   inside {[1:20]};
    soft cmd.nested_0.iteration inside {[1:20]};
    soft cmd.nested_1.iteration inside {[1:20]};

    soft cmd.main_0.length   inside {[1:PROG_MEM_DEPTH]};
    soft cmd.main_1.length   inside {[1:PROG_MEM_DEPTH]};
    soft cmd.main_2.length   inside {[1:PROG_MEM_DEPTH]};
    soft cmd.nested_0.length inside {[1:PROG_MEM_DEPTH]};
    soft cmd.nested_1.length inside {[1:PROG_MEM_DEPTH]};

    soft base == 0;
    soft top  == PROG_MEM_DEPTH; 
  }

  `uvm_object_utils(iau_cmd_descriptor_sequence)

  function new(string name = "iau_cmd_descriptor_sequence");
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

    `uvm_info(get_name, $sformatf("command parameters: base: %0d, top: %0d \n cmd: %p ", base, top, cmd), UVM_HIGH)

    dp_cmd.valid            = 1;
    dp_cmd.format           = header.format;
    dp_cmd.main_0.start     = cmd.main_0.start;
    dp_cmd.main_0.length    = cmd.main_0.length;
    dp_cmd.main_0.iteration = cmd.main_0.iteration;
    dp_cmd.errors           = 0;
/*
    dp_cmd.randomize with {
      valid              == 1;
      extra              == 0;
      format             == header.format;
      if (header.format == aic_dp_cmd_gen_pkg::Bypass) {
        main_0.iteration   == 0;
        main_1.iteration   == 0;
        main_2.iteration   == 0;
        nested_0.iteration == 0;
        nested_1.iteration == 0;
                             
        main_0.length   == 0;
        main_1.length   == 0;
        main_2.length   == 0;
        nested_0.length == 0;
        nested_1.length == 0;
      }
      else {
        if(`_main_0_valid_)   main_0.iteration   == cmd.main_0.iteration;
        if(`_main_1_valid_)   main_1.iteration   == cmd.main_1.iteration;
        if(`_main_2_valid_)   main_2.iteration   == cmd.main_2.iteration;
        if(`_nested_0_valid_) nested_0.iteration == cmd.nested_0.iteration;
        if(`_nested_1_valid_) nested_1.iteration == cmd.nested_1.iteration;

        if(`_main_0_valid_)   main_0.length   == cmd.main_0.length;
        if(`_main_1_valid_)   main_1.length   == cmd.main_1.length;
        if(`_main_2_valid_)   main_2.length   == cmd.main_2.length;
        if(`_nested_0_valid_) nested_0.length == cmd.nested_0.length;
        if(`_nested_1_valid_) nested_1.length == cmd.nested_1.length;

        if (start_0) {
          main_0.start   == 0;
          main_1.start   == 0;
          main_2.start   == 0;
          nested_0.start == 0;
          nested_1.start == 0;
        }
        else {
          main_0.start == cmd.main_0.start; 
        }
      }
    };

    cmd.nested_1_map_main = dp_cmd.nested_1_map_main;
    cmd.nested_1          = dp_cmd.nested_1;
    cmd.nested_0_map_main = dp_cmd.nested_0_map_main;
    cmd.nested_0          = dp_cmd.nested_0;
    cmd.main_2            = dp_cmd.main_2;
    cmd.main_1            = dp_cmd.main_1;
    cmd.extra             = dp_cmd.extra;
    cmd.main_0            = dp_cmd.main_0;
*/
    dpcmd_payload = decode_cmd(header,cmd);
    burst_length = dpcmd_payload.size();

    `uvm_info(get_name, $sformatf("writing command: %p", cmd), UVM_HIGH);
    dp_cmd.print();
    `uvm_info(get_name, $sformatf("main_0: %p", dp_cmd.main_0), UVM_HIGH);

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    `uvm_info ("run_phase", $sformatf("ADDR: %0h, Writing header: %p\ncmd: %p",
              IAU_CMD_BLOCK_ADDR_ST, header, cmd), UVM_LOW)

    /** Set up the write transaction */
    `uvm_create(write_tran)
    write_tran.port_cfg        = cfg;
    write_tran.xact_type       = svt_axi_transaction::WRITE;
    write_tran.addr            = IAU_CMD_BLOCK_ADDR_ST;
    write_tran.burst_type      = svt_axi_transaction::INCR;
    write_tran.burst_size      = svt_axi_transaction::BURST_SIZE_64BIT;
    write_tran.atomic_type     = svt_axi_transaction::NORMAL;
    write_tran.burst_length    = burst_length;
    write_tran.data            = new[write_tran.burst_length];
    write_tran.wstrb           = new[write_tran.burst_length];
    write_tran.data_user       = new[write_tran.burst_length];
    write_tran.wvalid_delay    = new[write_tran.burst_length];

    foreach (dpcmd_payload[i]) begin
      write_tran.data[i]         = dpcmd_payload[i]; 
      write_tran.wstrb[i]        = 8'hff;
      write_tran.wvalid_delay[i] = $urandom_range(0,4);
    end

    /** Send the write transaction */
    `uvm_send(write_tran)

    /** Wait for the write transaction to complete */
    get_response(rsp);
  endtask

  function bit_64_queue_t decode_cmd(ref iau_cmd_header_t header, ref aic_dp_cmd_gen_pkg::cmdb_cmd_struct_t cmd); 
    bit_64_queue_t payload;
    
    //case BYPASS: only header is sent
    payload.push_back(header);
    case (header.format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        payload.push_back({cmd.extra, cmd.main_0});
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        payload.push_back({cmd.extra, cmd.main_0});
        payload.push_back({cmd.nested_0_map_main, cmd.nested_0});
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        payload.push_back({cmd.extra, cmd.main_0});
        payload.push_back({cmd.nested_0_map_main, cmd.nested_0});
        payload.push_back({cmd.nested_1_map_main, cmd.nested_1});
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        payload.push_back({cmd.extra, cmd.main_0});
        payload.push_back({cmd.reserved_0, cmd.main_1});
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        payload.push_back({cmd.extra, cmd.main_0});
        payload.push_back({cmd.reserved_0, cmd.main_1});
        payload.push_back({cmd.nested_0_map_main, cmd.nested_0});
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        payload.push_back({cmd.extra, cmd.main_0});
        payload.push_back({cmd.reserved_0, cmd.main_1});
        payload.push_back({cmd.nested_0_map_main, cmd.nested_0});
        payload.push_back({cmd.nested_1_map_main, cmd.nested_1});
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        payload.push_back({cmd.extra, cmd.main_0});
        payload.push_back({cmd.reserved_0, cmd.main_1});
        payload.push_back({cmd.reserved_0, cmd.main_2});
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        payload.push_back({cmd.extra, cmd.main_0});
        payload.push_back({cmd.reserved_0, cmd.main_1});
        payload.push_back({cmd.reserved_0, cmd.main_2});
        payload.push_back({cmd.nested_0_map_main, cmd.nested_0});
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        payload.push_back({cmd.extra, cmd.main_0});
        payload.push_back({cmd.reserved_0, cmd.main_1});
        payload.push_back({cmd.reserved_0, cmd.main_2});
        payload.push_back({cmd.nested_0_map_main, cmd.nested_0});
        payload.push_back({cmd.nested_1_map_main, cmd.nested_1});
      end
    endcase

    return payload;
  endfunction


endclass
`endif
