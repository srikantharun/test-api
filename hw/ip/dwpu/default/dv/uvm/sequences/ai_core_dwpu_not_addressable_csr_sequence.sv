/**
 * File that will be used to aggregate the sequences to be used on the testcases
 */
/**
 * Sequence that verifies that address that are not a CSR return SLV_ERR
 */
class ai_core_dwpu_not_addressable_csr_sequence extends ai_core_dwpu_base_sequence;
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;
  // Register list
  uvm_reg reg_list[$];

  `uvm_object_utils(ai_core_dwpu_not_addressable_csr_sequence)

  // Class Constructor
  function new (string name = "ai_core_dwpu_not_addressable_csr_sequence");
    super.new(name);
  endfunction

  extern virtual task body();

endclass

task ai_core_dwpu_not_addressable_csr_sequence::body();
  uvm_status_e status;
  uvm_status_e expected_status;
  uvm_reg_addr_t avail_address_list[$];
  uvm_reg_addr_t not_avail_address_list[$];
  int success;
  `uvm_info("body", $sformatf("Start not addressable csr sequence body..."), UVM_HIGH)
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");

    // Get register list
    p_sequencer.regmodel.get_registers(reg_list);

    //get the addresses available for accessing
    foreach (reg_list[i]) begin
      avail_address_list.push_back(reg_list[i].get_address());
    end
    foreach (avail_address_list[i]) begin
      `uvm_info(get_type_name(), $sformatf("avail_address_list[%0d] = 0x%0x", i, avail_address_list[i]), UVM_HIGH)
    end

    //repeat 20 times the following steps
    repeat (20) begin
      //randomize the list of not_avail_address_list
      success = std::randomize(not_avail_address_list) with {
        not_avail_address_list.size ==  20;
        foreach(not_avail_address_list[i]) {
          foreach(avail_address_list[j]) {
            not_avail_address_list[i] != avail_address_list[j];
          }
          (not_avail_address_list[i] % 8) == 0;
          not_avail_address_list[i] inside {[DWPU_CSR_ST_ADDR: DWPU_CSR_END_ADDR]};
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

      //go through every address and request a write and a read. The answer shall be always the same (SLVERR)
      foreach (not_avail_address_list[i]) begin
        //write register
        `uvm_info("DWPU_REG",$sformatf("DWPU axi reg starting for register 0x%0x", not_avail_address_list[i]), UVM_LOW)
        // Randomize the sequence
        if(!axi_wr_seq.randomize() with {
          cfg_addr        == not_avail_address_list[i];
          sequence_length == 'd1;
          burst_size == BURST_SIZE_64BIT;
          burst_type == INCR;
          cfg_data.size == 1;
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
          burst_length == BURST_LENGTH_1;
        }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
        axi_rd_seq.start(p_sequencer.cfg_seqr);
        foreach(axi_rd_seq.read_transaction.rresp[i]) begin
          if(axi_rd_seq.read_transaction.rresp[i] == AXI_SLVERR_RESPONSE)
           `uvm_info("DWPU_READ_REG_COMPARE: PASSED", $sformatf("Address= 0x%0x and RRESP[%0d] = %s", not_avail_address_list[i], i, axi_rd_seq.read_transaction.rresp[i]), UVM_LOW)
          else
           `uvm_error("DWPU_READ_REG_COMPARE: FAILED", $sformatf("Address= 0x%0x and RRESP[%0d] = %s", not_avail_address_list[i], i, axi_rd_seq.read_transaction.rresp[i]))
        end
      end
    end

  `uvm_info("body", $sformatf("Finished not addressable csr sequence body..."), UVM_HIGH)
endtask : body
