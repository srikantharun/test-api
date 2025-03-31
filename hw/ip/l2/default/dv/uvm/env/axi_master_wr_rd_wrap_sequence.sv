
/**
 * Abstract:
 * axi_master_wr_rd_sequence is used by test to provide initiator scenario
 * information to the Master agent present in the System agent.  This class
 * defines a sequence in which a random AXI WRITE followed by a random AXI READ
 * sequence is generated using `uvm_do_with macros.
 *
 * Execution phase: main_phase
 * Sequencer: Master agent sequencer
 */

`ifndef GUARD_AXI_MASTER_WR_RD_WRAP_SEQUENCE_SV
`define GUARD_AXI_MASTER_WR_RD_WRAP_SEQUENCE_SV

class axi_master_wr_rd_wrap_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 10;

  bit [`AXI_LP_ADDR_WIDTH-1:0] write_addr;


  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {
    sequence_length <= 100;
  }


  /** UVM Object Utility macro */
  `uvm_object_utils(axi_master_wr_rd_wrap_sequence)

  /** Class Constructor */
  function new(string name="axi_master_wr_rd_wrap_sequence");
    super.new(name);
  endfunction

  virtual task body();
    bit status;
    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

    status = uvm_config_db #(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
    `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_LOW);

    fork
    forever begin
      get_response(rsp);
    end
    join_none


    repeat (sequence_length) begin
      `ifndef SVT_UVM_1800_2_2017_OR_HIGHER
        `uvm_do_with(req,
        {
          xact_type == svt_axi_transaction::WRITE;
          data_before_addr == 0;
          burst_type == svt_axi_transaction::WRAP;
        })
      `else
       `uvm_do(req,,,
        {
          xact_type == svt_axi_transaction::WRITE;
          data_before_addr == 0;
          burst_type == svt_axi_transaction::WRAP;
        })
      `endif

        
      `ifndef SVT_UVM_1800_2_2017_OR_HIGHER
        `uvm_do_with(req,
        {
          xact_type == svt_axi_transaction::READ;
          burst_type == svt_axi_transaction::WRAP;
          data_before_addr == 0;
        })
      `else
        `uvm_do(req,,,
        {
          xact_type == svt_axi_transaction::READ;
          burst_type == svt_axi_transaction::WRAP;
          data_before_addr == 0;
        })
      `endif
    end

    `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: axi_master_wr_rd_wrap_sequence

`endif // GUARD_AXI_MASTER_WR_RD_WRAP_SEQUENCE_SV
