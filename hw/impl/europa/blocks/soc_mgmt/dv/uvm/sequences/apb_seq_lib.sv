`ifndef GUARD_APB_MASTER_WR_RD_SEQUENCE_SV
`define GUARD_APB_MASTER_WR_RD_SEQUENCE_SV

class apb_master_wr_rd_sequence extends svt_apb_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand bit[11:0]    cfg_addr;
  rand bit[31:0]    cfg_data;
  /** Constrain the sequence length to a reasonable value */

  /** UVM Object Utility macro */
  `uvm_object_utils(apb_master_wr_rd_sequence)

  /** Class Constructor */
  function new(string name="apb_master_wr_rd_sequence");
    super.new(name);
  endfunction
  
  virtual task body();
    svt_apb_master_transaction write_tran, read_tran;
    bit status;
    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

      /** Set up the write transaction */
      `uvm_create(write_tran)
      write_tran.cfg       = cfg;
      write_tran.xact_type = svt_apb_transaction::WRITE;
      write_tran.address   = cfg_addr;
      write_tran.data      = cfg_data;
      write_tran.num_wait_cycles = 3;

      /** Send the write transaction */
      `uvm_send(write_tran)

      /** Wait for the write transaction to complete */
      get_response(rsp);

      `uvm_info("body", "APB WRITE transaction completed", UVM_LOW);

      /** Set up the read transaction */
      `uvm_create(read_tran)
      read_tran.cfg       = cfg;
      read_tran.xact_type = svt_apb_transaction::READ;
      read_tran.address   = cfg_addr;

      /** Send the read transaction */
      `uvm_send(read_tran)

      /** Wait for the read transaction to complete */
      get_response(rsp);
    
      `uvm_info("body", "APB READ transaction completed", UVM_LOW);

    `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: apb_master_wr_rd_sequence

class apb_master_wr_sequence extends svt_apb_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand bit[15:0]    cfg_addr;
  rand bit[31:0]    cfg_data;
  /** Constrain the sequence length to a reasonable value */

  /** UVM Object Utility macro */
  `uvm_object_utils(apb_master_wr_sequence)

  /** Class Constructor */
  function new(string name="apb_master_wr_sequence");
    super.new(name);
  endfunction
  
  virtual task body();
    svt_apb_master_transaction write_tran;
    bit status;
    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

      /** Set up the write transaction */
      `uvm_create(write_tran)
      write_tran.cfg       = cfg;
      write_tran.xact_type = svt_apb_transaction::WRITE;
      write_tran.address   = cfg_addr;
      write_tran.data      = cfg_data;

      /** Send the write transaction */
      `uvm_send(write_tran)

      /** Wait for the write transaction to complete */
      get_response(rsp);

      `uvm_info("body", "APB WRITE transaction completed", UVM_LOW);

    `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: apb_master_wr_sequence


class apb_master_rd_sequence extends svt_apb_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand bit[15:0]    cfg_addr;
  rand bit[31:0]    rd_data;
  /** Constrain the sequence length to a reasonable value */

  /** UVM Object Utility macro */
  `uvm_object_utils(apb_master_rd_sequence)

  /** Class Constructor */
  function new(string name="apb_master_rd_sequence");
    super.new(name);
  endfunction
  
  virtual task body();
    svt_apb_master_transaction read_tran;
    bit status;
    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

      /** Set up the read transaction */
      `uvm_create(read_tran)
      read_tran.cfg       = cfg;
      read_tran.xact_type = svt_apb_transaction::READ;
      read_tran.address   = cfg_addr;

      /** Send the read transaction */
      `uvm_send(read_tran)

      /** Wait for the read transaction to complete */
      get_response(rsp);
      rd_data             = read_tran.data;
    
      `uvm_info("body", "APB READ transaction completed", UVM_LOW);

    `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: apb_master_rd_sequence


`endif // GUARD_APB_MASTER_WR_RD_SEQUENCE_SV
