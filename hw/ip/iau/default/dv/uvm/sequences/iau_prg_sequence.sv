`ifndef IAU_PRG_SEQUENCE_SV
`define IAU_PRG_SEQUENCE_SV

class iau_prg_sequence extends svt_axi_master_base_sequence;

  /** UVM Object Utility macro */
  `uvm_object_utils(iau_prg_sequence)

  bit gen_output_irq;
  bit set_rfs;
  rand iau_common_pkg::iau_dp_cmd_t prog_mem[$];
  rand int prog_start_addr;
  rand int prog_size;
  rand int prog_iteration;
  rand bit prg_mem_invalid_range;
  rand bit invalid_reg_space;
  rand bit burst_transaction;
  rand svt_axi_transaction::burst_type_enum burst_type;
  rand svt_axi_transaction::burst_size_enum burst_size;

  bit [AXI_DW-1:0] data;
  bit [AXI_AW-1:0] addr;

  constraint c_axi_burst_cfg {
    //send aligned addrs only
    if (burst_transaction) {
      burst_type  dist {svt_axi_transaction::INCR := 20, svt_axi_transaction::WRAP := 5};
      burst_size  inside {[svt_axi_transaction::BURST_SIZE_16BIT:svt_axi_transaction::BURST_SIZE_64BIT]};

      prog_start_addr % (2 ** burst_size) == 0;
    }
    else {burst_size == svt_axi_transaction::BURST_SIZE_16BIT;}

    if (burst_type == svt_axi_master_transaction::WRAP) {
      prog_size inside {2,4,8,16};
      prog_start_addr == prog_size * 16; 
    }


  }

  constraint c_prog_cfg {
    soft burst_transaction     == 0;
    soft prg_mem_invalid_range == 0;
    soft invalid_reg_space     == 0;
  }

  constraint c_prog_size_start_addr {
    if (prg_mem_invalid_range) {
      prog_start_addr inside {PROG_MEM_DEPTH};
      prog_size       inside {'h3EFF};// full space between 'h8200 and 'hFFFF
    }
    else if (invalid_reg_space) {
      prog_start_addr inside {'h48};
      prog_size       inside {'h3EE}; // space between regs from 'h48 to 'h1000
    }
    else {
      prog_start_addr inside {[0 : (PROG_MEM_DEPTH)-1]};
      prog_size       dist { 1:= 10, [2:PROG_MEM_DEPTH-prog_start_addr] := 10};
    }
  }

  constraint c_prog_mem {
    solve prog_size before prog_mem;
    soft prog_iteration inside {[1:20]};
    prog_mem.size == prog_size;
    foreach (prog_mem[i]) {

      prog_mem[i].opcode dist {
        OP_NOP         := 1,
        [OP_MV:OP_MIN] := 10,
        OP_ADD         := 40
      };

      //more chance to source get input data
      //than internal regs
      prog_mem[i].src0 dist {
        POP := 10,
        [REG0 : REG7] :/ 40
      };
      prog_mem[i].src1 dist {
        POP := 10,
        [REG0 : REG7] :/ 40
      };


      //more chance to destination pushes data
      //than store in internal regs
      soft prog_mem[i].dst dist {
        PUSH := 5,
        [REG0:REG7] :/ 40
      };

      if (set_rfs) {
        prog_mem[i].rfs dist {
        1 := 20,
        0 := 10
        };
        //one of the sources need to get input data
        //rfs: consume whole input stream data
        if (prog_mem[i].rfs) {
          prog_mem[i].opcode > OP_NOP;
          if (i == prog_size -1) {
            prog_mem[i].dst == PUSH_TLAST;
          }
          else { prog_mem[i].dst <= PUSH; }
          if (prog_mem[i].opcode == OP_MV) {
            prog_mem[i].src0[3] == 1;
          }
          else {
            prog_mem[i].src0[3] == 1 || prog_mem[i].src1[3] == 1;
          }
        }
        else {
          prog_mem[i].dst < PUSH;
          prog_mem[i].src0[3] != 1 && prog_mem[i].src1[3] != 1;
        }
      }
      else {
        prog_mem[i].rfs == 0;
      }

      //at least one instruction gets data from input
      if (i == 0) {
        prog_mem[i].src0 == POP;
        prog_mem[i].opcode != OP_NOP;
      }
      
      //last instruction always push-last data
      if (i == prog_size - 1) {
        //generates unfinished output stream situation
        //that should make IAU activate output stream IRQ
        prog_mem[i].opcode > OP_NOP;
        if (gen_output_irq) {
          prog_mem[i].dst == PUSH;
        }
        else {
          prog_mem[i].dst == PUSH_TLAST;
        }
      }
    }
  }


  //return the number of input data needed for the generated program
  function int_index_arr_t get_input_stream_info();
    int idx;
    int_index_arr_t dt_cnt;
    foreach (prog_mem[i]) begin
      if ( prog_mem[i].opcode > OP_MV && (prog_mem[i].src0[3] || prog_mem[i].src1[3]) ||
           prog_mem[i].opcode == OP_MV && prog_mem[i].src0[3]) begin
        //rfs : create a new data stream with random number os input data
        if (prog_mem[i].rfs) begin
          dt_cnt[idx] += $urandom_range(5,10);
          idx++;
        end
        //instr pop: generate a new data in the same stream
        else
          dt_cnt[idx]++;
      end
    end
    `uvm_info ("body", $sformatf("N of stream data generated: %p",dt_cnt ), UVM_HIGH)
    return dt_cnt;
  endfunction

  function iau_cmd_desc_t get_cmd();
    iau_cmd_desc_t cmd;
    cmd.loop_iter  = prog_iteration;
    cmd.loop_start = prog_start_addr;
    cmd.loop_len   = prog_size;
    return cmd;
  endfunction

  /** Class Constructor */
  function new(string name="iau_prg_sequence");
    super.new(name);
  endfunction


  virtual task body();
    svt_axi_master_transaction write_tran,read_tran;
    svt_configuration get_cfg;
    bit status;
    bit [31:0] iau_dpcmd_addr_offset;

    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    `uvm_info ("body", $sformatf("Writing program start_addr: 0x%0h, len: %0d, burst_transaction: %b, burst size: %s, type: %s",
                prog_start_addr, prog_mem.size(), burst_transaction, burst_size.name, burst_type.name), UVM_HIGH)
    foreach (prog_mem[i]) begin
      `uvm_info ("body", $sformatf("[%0d] :%p", i, prog_mem[i]), UVM_FULL)
    end

    iau_dpcmd_addr_offset = (invalid_reg_space==1) ? 0 : IAU_DPCMD_ADDR_ST ;

    /** Set up the write transaction */
    if (burst_transaction) begin
      int div = burst_size == svt_axi_transaction::BURST_SIZE_32BIT ? 2 : (burst_size == svt_axi_transaction::BURST_SIZE_64BIT ? 4 : 1);
      int burst_length = $ceil(prog_mem.size() / real'(div));
      `uvm_create(write_tran)
      if(!write_tran.randomize() with {
        write_tran.port_cfg        == cfg;
        write_tran.xact_type       == svt_axi_transaction::WRITE;
        write_tran.burst_type      == local::burst_type; 
        write_tran.burst_size      == local::burst_size; 
        write_tran.atomic_type     == svt_axi_transaction::NORMAL;
        write_tran.addr            == IAU_DPCMD_ADDR_ST + prog_start_addr *2;
        write_tran.burst_length    == local::burst_length;
        foreach (write_tran.wvalid_delay[i]) 
          write_tran.wvalid_delay[i] == 0; 
      })
        `uvm_fatal("run_phase", "Failed to randomize");

      if (burst_size == svt_axi_transaction::BURST_SIZE_16BIT) begin
        foreach (prog_mem[i]) begin
          write_tran.data[i]  = prog_mem[i];
          write_tran.wstrb[i] = 'h3;  
        end
      end
      else begin
        //32 or 64 bits
        int burst_size_cnt = burst_size == svt_axi_transaction::BURST_SIZE_32BIT ? 2 : 4;
        foreach (write_tran.data[i]) begin
          int j = 0;
          while (j < burst_size_cnt) begin
            iau_common_pkg::iau_dp_cmd_t prg;
            write_tran.data[i][j * 16  +:16] = prog_mem.pop_front();
            prg = write_tran.data[i][j *16 +: 16];
            if (prog_mem.size() == 0) break;
            j++;
          end
          if (prog_mem.size() > 0 || prog_size % burst_size_cnt == 0)
            write_tran.wstrb[i] = burst_size_cnt == 2 ? 'hF : 'hFF;  
          else begin
            int ps = (prog_size % burst_size_cnt) * 2;
            for (int wb = 0; wb < ps; wb++)
              write_tran.wstrb[i][wb] = 1'b1;
          end
        end
      end
      `uvm_info(get_type_name(), $sformatf("sending transaction = \n %s", write_tran.sprint()), UVM_HIGH);
      `uvm_send(write_tran)

      /** Wait for the write transaction to complete */
      get_response(rsp);
    end
    else begin
      foreach (prog_mem[i]) begin
        `uvm_create(write_tran)
        write_tran.port_cfg        = cfg;
        write_tran.xact_type       = svt_axi_transaction::WRITE;
        write_tran.burst_type      = svt_axi_transaction::INCR;
        write_tran.burst_size      = svt_axi_transaction::BURST_SIZE_16BIT;
        write_tran.atomic_type     = svt_axi_transaction::NORMAL;
        write_tran.burst_length    = 1;
        write_tran.data            = new[write_tran.burst_length];
        write_tran.wstrb           = new[write_tran.burst_length];
        write_tran.data_user       = new[write_tran.burst_length];
        write_tran.wvalid_delay    = new[write_tran.burst_length];
        write_tran.wvalid_delay[0] = 0;
        write_tran.wstrb[0]        = invalid_reg_space ? 8'h0f : 8'h03;
        write_tran.addr            = iau_dpcmd_addr_offset+(i*2 + prog_start_addr*(2+(2*invalid_reg_space)));
        write_tran.data[0]         = prog_mem[i];
        /** Send the write transaction */
        `uvm_info ("body", $sformatf("sending: %p", prog_mem[i]), UVM_HIGH)
        `uvm_info ("PROGRAM TRANSACTION", $sformatf("IAU_DPCMD_ADDR_OFFSET: %h", IAU_DPCMD_ADDR_ST), UVM_LOW)
        `uvm_info ("PROGRAM TRANSACTION", $sformatf("transaction addr: %h, prg_mem_invalid_range %0d", write_tran.addr , prg_mem_invalid_range), UVM_LOW)
        `uvm_send(write_tran)

        /** Wait for the write transaction to complete */
        get_response(rsp);

        if ((prg_mem_invalid_range && rsp.bresp inside {svt_axi_transaction::SLVERR}) || (invalid_reg_space && rsp.bresp inside {svt_axi_transaction::SLVERR}) )
        `uvm_info("INVALID_WR_RANGE_CHK", "error response on write in valid program space : OK",UVM_LOW)
        else if (prg_mem_invalid_range || invalid_reg_space)
        `uvm_error("INVALID_WR_RANGE_CHK", $sformatf("Expected error on read transaction addr: %h", write_tran.addr))
        else  if (rsp.bresp inside {svt_axi_transaction::SLVERR})
        `uvm_error("INVALID_WR_RANGE_CHK", $sformatf("SLV error on write transaction addr: %h", write_tran.addr))

        `uvm_info("body", "AXI CFG WRITE transaction completed", UVM_LOW);

        /** Set up the read transaction */
        `uvm_create(read_tran)
        read_tran.port_cfg     = cfg;
        read_tran.xact_type    = svt_axi_transaction::READ;
        read_tran.addr         = iau_dpcmd_addr_offset+(i*2 + prog_start_addr*(2+(2*invalid_reg_space)));
        read_tran.burst_type   = svt_axi_transaction::INCR;
        read_tran.burst_size   = svt_axi_transaction::BURST_SIZE_32BIT;
        read_tran.atomic_type  = svt_axi_transaction::NORMAL;
        read_tran.burst_length = 1;
        read_tran.rresp        = new[read_tran.burst_length];
        read_tran.data         = new[read_tran.burst_length];
        read_tran.rready_delay = new[read_tran.burst_length];
        read_tran.data_user    = new[read_tran.burst_length];
        foreach (read_tran.rready_delay[i]) begin
          read_tran.rready_delay[i]=i;
        end

        /** Send the read transaction */
        `uvm_send(read_tran)

        /** Wait for the read transaction to complete */
        get_response(rsp);

        if ((prg_mem_invalid_range && rsp.rresp[0] inside {svt_axi_transaction::SLVERR}) || (invalid_reg_space && rsp.rresp[0] inside {svt_axi_transaction::SLVERR}) )
        `uvm_info("INVALID_RD_RANGE_CHK", "error response on write in valid program space : OK",UVM_LOW)
        else if (prg_mem_invalid_range || invalid_reg_space)
        `uvm_error("INVALID_RD_RANGE_CHK", $sformatf("Expected error on read transaction addr: %h", read_tran.addr))
        else  if (rsp.rresp[0] inside {svt_axi_transaction::SLVERR})
        `uvm_error("INVALID_RD_RANGE_CHK", $sformatf("SLV error on read transaction addr: %h", read_tran.addr))

        `uvm_info("body", "AXI READ transaction completed", UVM_LOW);

      end
    end
    `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: iau_prg_sequence


`endif


/*
class iau_prg_sequence extends svt_axi_master_base_sequence;
  `uvm_object_utils(iau_prg_sequence)

  bit gen_output_irq;
  bit set_rfs;
  aic_dp_cmd_gen_pkg::cmdb_cmd_struct_t cmd;   
  iau_cmd_header_t header;
  rand iau_common_pkg::iau_dp_cmd_t prog_mem[int];
  rand iau_instruction_sequence instr_seq;

  function new(string name="iau_prg_sequence");
    super.new(name);
    instr_seq = new();
  endfunction

  function void pre_randomize();
    prog_mem.delete();
    `uvm_info(get_name, $sformatf("received header: %p \n cmd: %p", header, cmd), UVM_HIGH);
    case (header.format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_0.start; i <= `_end_(cmd.nested_0); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_0.start; i <= `_end_(cmd.nested_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_1.start; i <= `_end_(cmd.nested_1); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_1.start; i <= `_end_(cmd.main_1); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_1.start; i <= `_end_(cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_0.start; i <= `_end_(cmd.nested_0); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_1.start; i <= `_end_(cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_0.start; i <= `_end_(cmd.nested_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_1.start; i <= `_end_(cmd.nested_1); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_1.start; i <= `_end_(cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_2.start; i <= `_end_(cmd.main_2); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_1.start; i <= `_end_(cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_2.start; i <= `_end_(cmd.main_2); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_0.start; i <= `_end_(cmd.nested_0); i++)
          prog_mem[i] = 0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        for (int i = cmd.main_0.start; i <= `_end_(cmd.main_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_1.start; i <= `_end_(cmd.main_1); i++)
          prog_mem[i] = 0;
        for (int i = cmd.main_2.start; i <= `_end_(cmd.main_2); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_0.start; i <= `_end_(cmd.nested_0); i++)
          prog_mem[i] = 0;
        for (int i = cmd.nested_1.start; i <= `_end_(cmd.nested_1); i++)
          prog_mem[i] = 0;
      end
    endcase
  endfunction

  function void post_randomize();
    int rand_index;
    foreach (prog_mem[i]) begin
      instr_seq.randomize() with {
        if (set_rfs) {
          instr.rfs inside {[0:1]}; 
        }
        else {
          instr.rfs == 0; 
        }
      };

      prog_mem[i] = instr_seq.instr;
    end

    //verif program rules
    //at least one instruction should receive input data
    //last instruction send data with tlast at end of program
    case (header.format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        gen_rnd_instr(cmd.main_0);
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        gen_rnd_instr(cmd.main_0);
        gen_rnd_instr(cmd.nested_0);
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        gen_rnd_instr(cmd.main_0);
        gen_rnd_instr(cmd.nested_0);
        gen_rnd_instr(cmd.nested_1);
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        gen_rnd_instr(cmd.main_0);
        gen_rnd_instr(cmd.main_1);
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        gen_rnd_instr(cmd.main_0);
        gen_rnd_instr(cmd.main_1);
        gen_rnd_instr(cmd.nested_0);
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        gen_rnd_instr(cmd.main_0);
        gen_rnd_instr(cmd.main_1);
        gen_rnd_instr(cmd.nested_0);
        gen_rnd_instr(cmd.nested_1);
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        gen_rnd_instr(cmd.main_0);
        gen_rnd_instr(cmd.main_1);
        gen_rnd_instr(cmd.main_2);
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        gen_rnd_instr(cmd.main_0);
        gen_rnd_instr(cmd.main_1);
        gen_rnd_instr(cmd.main_2);
        gen_rnd_instr(cmd.nested_0);
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        gen_rnd_instr(cmd.main_0);
        gen_rnd_instr(cmd.main_1);
        gen_rnd_instr(cmd.main_2);
        gen_rnd_instr(cmd.nested_0);
        gen_rnd_instr(cmd.nested_1);
      end
    endcase

    `uvm_info(get_name, "generated program:", UVM_HIGH)
    foreach (prog_mem[i]) 
      `uvm_info(get_name, $sformatf("prog mem[%0h]: %p", i, prog_mem[i]), UVM_HIGH)
  endfunction

  function void gen_rnd_instr(aic_dp_cmd_gen_pkg::loop_description_t loop_desc);
    //at least one instruction gets data from input
    instr_seq.randomize() with {instr.src0 == POP; instr.opcode != OP_NOP;};
    prog_mem[0] = instr_seq.instr;

    //last instruction always push-last data
    instr_seq.randomize() with {
      instr.opcode != OP_NOP;
      if (gen_output_irq) {
      instr.dst == PUSH; 
      }
      else {
        instr.dst == PUSH_TLAST; 
      }
    };
    prog_mem[`_end_(loop_desc)] = instr_seq.instr;
  endfunction

  //return the number of input data needed for the generated program
  function int_index_arr_t get_input_stream_info();
    int idx;
    int_index_arr_t dt_cnt;
    foreach (prog_mem[i]) begin
      if ( prog_mem[i].opcode > OP_MV && (prog_mem[i].src0[3] || prog_mem[i].src1[3]) ||
           prog_mem[i].opcode == OP_MV && prog_mem[i].src0[3]) begin
        //rfs : create a new data stream with random number os input data
        if (prog_mem[i].rfs) begin
          dt_cnt[idx] += $urandom_range(5,10);
          idx++;
        end
        //instr pop: generate a new data in the same stream
        else
          dt_cnt[idx]++;
      end
    end
    `uvm_info ("body", $sformatf("N of stream data generated: %p",dt_cnt ), UVM_HIGH)
    return dt_cnt;
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran,read_tran;
    svt_configuration get_cfg;
    bit status;
    bit [31:0] IAU_DPCMD_ADDR_OFFSET;

    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    foreach (prog_mem[i]) begin
      `uvm_create(write_tran)
      write_tran.port_cfg        = cfg;
      write_tran.xact_type       = svt_axi_transaction::WRITE;
      write_tran.burst_type      = svt_axi_transaction::INCR;
      write_tran.burst_size      = svt_axi_transaction::BURST_SIZE_16BIT;
      write_tran.atomic_type     = svt_axi_transaction::NORMAL;
      write_tran.burst_length    = 1;
      write_tran.data            = new[write_tran.burst_length];
      write_tran.wstrb           = new[write_tran.burst_length];
      write_tran.data_user       = new[write_tran.burst_length];
      write_tran.wvalid_delay    = new[write_tran.burst_length];
      write_tran.wvalid_delay[0] = 0;
      write_tran.wstrb[0]        = 8'h03;
      write_tran.addr            = IAU_DPCMD_ADDR_OFFSET + i*2;
      write_tran.data[0]         = prog_mem[i];
      `uvm_info ("body", $sformatf("writing instr @%0h, prog_mem[%0h]: %p",write_tran.addr, i, prog_mem[i]), UVM_HIGH)
      `uvm_send(write_tran)

      get_response(rsp);

      if (rsp.bresp inside {svt_axi_transaction::SLVERR})
        `uvm_error("INVALID_WR_RANGE_CHK", $sformatf("SLV error on write transaction addr: %h", write_tran.addr))

      `uvm_info("body", "AXI CFG WRITE transaction completed", UVM_LOW);

      `uvm_create(read_tran)
      read_tran.port_cfg     = cfg;
      read_tran.xact_type    = svt_axi_transaction::READ;
      read_tran.addr         = IAU_DPCMD_ADDR_OFFSET + i * 2;
      read_tran.burst_type   = svt_axi_transaction::INCR;
      read_tran.burst_size   = svt_axi_transaction::BURST_SIZE_32BIT;
      read_tran.atomic_type  = svt_axi_transaction::NORMAL;
      read_tran.burst_length = 1;
      read_tran.rresp        = new[read_tran.burst_length];
      read_tran.data         = new[read_tran.burst_length];
      read_tran.rready_delay = new[read_tran.burst_length];
      read_tran.data_user    = new[read_tran.burst_length];
      foreach (read_tran.rready_delay[i]) begin
        read_tran.rready_delay[i]=i;
      end

      `uvm_send(read_tran)
      get_response(rsp);

      if (rsp.rresp[0] inside {svt_axi_transaction::SLVERR})
        `uvm_error("INVALID_RD_RANGE_CHK", $sformatf("SLV error on read transaction addr: %h", read_tran.addr))

      `uvm_info("body", "AXI READ transaction completed", UVM_LOW);

    end
  endtask: body

endclass: iau_prg_sequence

`endif
*/
