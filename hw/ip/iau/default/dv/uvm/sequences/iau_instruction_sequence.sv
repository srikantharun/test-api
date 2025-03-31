`ifndef IAU_INSTRUCTION_SEQUENCE_SV
`define IAU_INSTRUCTION_SEQUENCE_SV

class iau_instruction_sequence extends svt_axi_master_base_sequence;

  /** UVM Object Utility macro */
  `uvm_object_utils(iau_instruction_sequence)

  rand bit [AXI_AW-1:0] addr;
  rand iau_common_pkg::iau_dp_cmd_t instr;
  bit gen_output_irq;
  bit set_rfs;

  constraint c_addr {
    addr inside {[IAU_DPCMD_ADDR_ST : IAU_DPCMD_ADDR_END]};
    addr % 2 == 0;
  }
  
  constraint c_instr {
    soft instr.opcode dist {
      OP_NOP         := 1,
      [OP_MV:OP_MIN] := 10,
      OP_ADD         := 40
    };

    //more chance to source get input data
    //than internal regs
    instr.src0 dist {
      POP := 10,
      [REG0 : REG7] :/ 40
    };

    instr.src1 dist {
      POP := 10,
      [REG0 : REG7] :/ 40
    };

    //more chance to destination pushes data
    //than store in internal regs
    soft instr.dst dist {
      PUSH := 5,
      [REG0:REG7] :/ 40
    };

    if (set_rfs) {
      instr.rfs dist {
      1 := 20,
      0 := 10
      };
      //one of the sources need to get input data
      //rfs: consume whole input stream data
      if (instr.rfs) {
        instr.opcode > OP_NOP;
        if (instr.opcode == OP_MV) {
          instr.src0[3] == 1;
        }
        else {
          instr.src0[3] == 1 || instr.src1[3] == 1;
        }
      }
      else {
        instr.dst < PUSH;
        instr.src0[3] != 1 && instr.src1[3] != 1;
      }
    }
    else {
      instr.rfs == 0;
    }
  }

  /** Class Constructor */
  function new(string name="iau_instruction_sequence");
    super.new(name);
  endfunction


  virtual task body();
    svt_axi_master_transaction write_tran;
    svt_configuration get_cfg;
    bit status;

    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    `uvm_info ("body", $sformatf(" instr generated @%0h: %p",addr, instr), UVM_FULL)

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
    write_tran.wstrb[0]        = 8'h0f;
    write_tran.addr            = addr; 
    write_tran.data[0]         = instr;
    `uvm_send(write_tran)

    /** Wait for the write transaction to complete */
    get_response(rsp);

    `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: iau_instruction_sequence


`endif
