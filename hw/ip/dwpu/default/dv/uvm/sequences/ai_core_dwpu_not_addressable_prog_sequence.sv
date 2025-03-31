/**
 * Sequence that verifies program memory addresses that are not accessible return SLV_ERR
 */
class ai_core_dwpu_not_addressable_prog_sequence extends ai_core_dwpu_base_sequence;
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;
  // Register list
  uvm_reg reg_list[$];
  int iterations = 20;

  `uvm_object_utils(ai_core_dwpu_not_addressable_prog_sequence)

  // Class Constructor
  function new (string name = "ai_core_dwpu_not_addressable_prog_sequence");
    super.new(name);
  endfunction

  extern virtual task body();

endclass

task ai_core_dwpu_not_addressable_prog_sequence::body();
  uvm_status_e status;
  uvm_status_e expected_status;
  uvm_reg_addr_t not_avail_address_list[$];
  int success;
  `uvm_info("body", $sformatf("Start not addressable csr sequence body..."), UVM_HIGH)
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");

    //repeat "iterations" times the following steps
    repeat (iterations) begin
      `uvm_info("body", $sformatf("INSTR_MEM_DEPTH= %0d Size of instr mem in address: 0x%0x", INSTR_MEM_DEPTH, ((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8)), UVM_LOW)
      `uvm_info("body", $sformatf("Randomizing addresses inside the invalid region [0x%0x : 0x%0x]", DWPU_IMEM_ST_ADDR+((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8), DWPU_IMEM_END_ADDR-7), UVM_LOW)
      //randomize the list of not_avail_address_list
      success = std::randomize(not_avail_address_list) with {
        not_avail_address_list.size ==  20;
        foreach(not_avail_address_list[i]) {
          (not_avail_address_list[i] % 8) == 0;
          not_avail_address_list[i] inside {[DWPU_IMEM_ST_ADDR+((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8) : DWPU_IMEM_END_ADDR-7]};
          //make sure the maximum position is acheived
          if(i==0) {
            not_avail_address_list[i] == (DWPU_IMEM_END_ADDR-7);
          }
          else {
            not_avail_address_list[i] inside {[DWPU_IMEM_ST_ADDR+((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8) : DWPU_IMEM_END_ADDR-7 -(8*100)]}; //address from the beginning of program memory until the max memory -100 positions
          }
        }
      } ;
      if(success) begin
        `uvm_info(get_type_name(), $sformatf("Randomization of not_avail_address_list was successful and size is equal to %0d", not_avail_address_list.size), UVM_HIGH)
      end
      else begin
        `uvm_error(get_type_name(), $sformatf("Randomization of not_avail_address_list was unsuccessful"))
      end
      foreach (not_avail_address_list[i]) begin
        `uvm_info(get_type_name(), $sformatf("not_avail_address_list[%0d] = 0x%0x", i, not_avail_address_list[i]), UVM_HIGH)
      end

      //go through every address and request a write and a read. The answer shall be always the same (DECERR)
      foreach (not_avail_address_list[i]) begin
        //write register
        `uvm_info("DWPU_REG",$sformatf("DWPU axi reg starting for register 0x%0x", not_avail_address_list[i]), UVM_LOW)
        // Randomize the sequence
        if(!axi_wr_seq.randomize() with {
          cfg_addr        == not_avail_address_list[i];
          sequence_length == 'd1;
          burst_size == BURST_SIZE_64BIT;
          burst_type inside {svt_axi_master_transaction::INCR, svt_axi_master_transaction::FIXED};
          if(i==0) cfg_data.size == 1;
          else     cfg_data.size inside {[1:100]};
        }) `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
        // Start the sequence on the respective sequencer
        axi_wr_seq.start(p_sequencer.cfg_seqr);
        if(axi_wr_seq.write_tran.bresp == AXI_SLVERR_RESPONSE)
          `uvm_info("DWPU_WRITE_REG_COMPARE: PASSED", $sformatf("Address= 0x%0x and BRESP = %s", not_avail_address_list[i], axi_wr_seq.write_tran.bresp), UVM_LOW)
        else
         `uvm_error("DWPU_WRITE_REG_COMPARE: FAILED", $sformatf("Address= 0x%0x and BRESP = %s", not_avail_address_list[i], axi_wr_seq.write_tran.bresp))

        //read register
        if(!axi_rd_seq.randomize() with {
          cfg_addr        == not_avail_address_list[i];
          sequence_length == 'd1;
          burst_size == BURST_SIZE_64BIT;
          burst_type == INCR;
          if(i==0) burst_length == 1;
          else     burst_length inside {[1:100]};
        }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
        axi_rd_seq.start(p_sequencer.cfg_seqr);
        foreach(axi_rd_seq.read_transaction.rresp[j]) begin
          if(axi_rd_seq.read_transaction.rresp[j] == AXI_SLVERR_RESPONSE)
           `uvm_info("DWPU_READ_REG_COMPARE: PASSED", $sformatf("Address= 0x%0x and RRESP[%0d] = %s", not_avail_address_list[i]+(j*8), j, axi_rd_seq.read_transaction.rresp[j]), UVM_LOW)
          else
           `uvm_error("DWPU_READ_REG_COMPARE: FAILED", $sformatf("Address= 0x%0x and RRESP[%0d] = %s", not_avail_address_list[i]+(j*8), j, axi_rd_seq.read_transaction.rresp[j]))
        end
      end
    end

  `uvm_info("body", $sformatf("Finished not addressable prog sequence body..."), UVM_HIGH)
endtask : body
