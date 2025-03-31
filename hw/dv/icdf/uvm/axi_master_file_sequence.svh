
/**
 * Abstract:
 * axi_master_file_sequence is used by test to provide initiator
 * scenario information to the Master agent present in the System Env.
 * This class defines a sequence by assigning values from a file
 * to the transactions rather than randomization, and then transmitted
 * using `uvm_send.
 * Execution phase: main_phase
 * Sequencer: Master agent sequencer
 */

`ifndef GUARD_AXI_MASTER_FILE_SEQUENCE_SV
`define GUARD_AXI_MASTER_FILE_SEQUENCE_SV

class axi_master_file_sequence extends svt_axi_master_base_sequence;

  /** UVM Object Utility macro */
  `uvm_object_utils(axi_master_file_sequence)

  /** Class Constructor */
  function new(string name="axi_master_file_sequence");
    super.new(name);
  endfunction

  virtual function void trunc_addr(ref logic [31:0] address);
    address = address[aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0];
  endfunction : trunc_addr

  virtual task body();
    svt_axi_master_transaction transaction;
    svt_configuration get_cfg;
    bit status;
    string path;
    string filename;
    int file;
    bit write;
    logic [31:0] address;
    logic [7:0] strobe;
    logic [63:0] data;
    bit          csr_poll;
    logic [31:0] cnt='0;

    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

    /** Read the input filename  */
    status = uvm_config_db #(string)::get(null, get_full_name(), "filename", filename);
    `uvm_info("body", $sformatf("filename is %0s", filename), UVM_LOW);

    /** Read the test path DIR  */
    status = uvm_config_db #(string)::get(null, get_full_name(), "path", path);
    `uvm_info("body", $sformatf("Path DIR is %0s", path), UVM_LOW);

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    #20;
    //$display("can reuse the data width %s",$sformatf(get_cfg) );
    /** Open the input stimuli data file */
    file = $fopen({path,filename,".txt"}, "r");
    if (!file)  // if no AXI cfg file, die
      `uvm_fatal("body", $sformatf("ICDF test not found: %s", {path, filename, ".txt"}));

    /** Until the end of the file read the data */
    while (!$feof(file)) begin
      /** Read the data arguments */
      /** The file format currently supported is: */
      /**  write(hex fotmat) [space] address(hex format) [space] data(binary format) */
      /** The data refer to read data if write = 0 and write data if write = 1 */
      /** Binary format has been chosen for the data  */
      $fscanf(file, "%h %h %b %b", write, address, strobe, data);
      `uvm_info(get_name(), $sformatf("READ from %s/%s.txt: write_type: %0x, address: 0x%0x, strobe: 0x%0x, data: 0x%0x", path, filename, write, address, strobe, data), UVM_LOW)

      /** Callback to truncate the address if needed */
      trunc_addr(address);

      /** Set up the read transaction */
      /** Poll the  CMD status CSR to wait for the completion of all previous instructions */
      /** Polling of this register should repeat until the */
      csr_poll = 1'b1;

      if (~write) begin
          while (csr_poll == 1'b1) begin

           `uvm_create(transaction)
            transaction.port_cfg     = cfg;
            transaction.xact_type    = svt_axi_transaction::READ;
            transaction.addr         = address;
            transaction.burst_type   = svt_axi_transaction::INCR;
            transaction.burst_size   = svt_axi_transaction::BURST_SIZE_64BIT;
            transaction.atomic_type  = svt_axi_transaction::NORMAL;
            transaction.burst_length = 1;

            transaction.data         = new[transaction.burst_length];
            transaction.wstrb        = new[transaction.burst_length];
            transaction.data_user    = new[transaction.burst_length];
            transaction.wvalid_delay = new[transaction.burst_length];

            transaction.data[0] = data;
            transaction.wstrb[0] = strobe;
            transaction.wvalid_delay[0]=4;

            transaction.rresp        = new[transaction.burst_length];
            transaction.rready_delay = new[transaction.burst_length];
            transaction.rready_delay[0]=$urandom_range(0,10);

            cnt=0;

            // Lines used for debug only
            //$display("AXI READ iteration : %d",cnt);

            /** Send the write transaction */
           `uvm_send(transaction)

            /** Wait for the write transaction to complete */
            get_response(rsp);

            // Lines used for debug only
            //$display("AXI transaction response is: %s",rsp.sprint());

            /**  Compare expected data with actual data */
            foreach (data[i]) begin
              if (data[i] != "?") begin
                if (data[i] != rsp.data[0][i]) begin
                  cnt=cnt+1;
                  `uvm_info("ICDF", $sformatf("Polling CMD_STATUS CSR @addr=%h did not find expected value.\n Expected data: %b \n Actual data  : %b\n Diff         : %b\n Polling request will be repeated.",address, data[i],rsp.data[0][i],data[i]^rsp.data[0][i] ), UVM_MEDIUM );
                end
              end
             end //foreach

             if (~|cnt) begin
               csr_poll = 1'b0;
             end else begin
               csr_poll = 1'b1;
             end
           end //while

      end else begin
         /** Set up the write transaction */
        `uvm_create(transaction)
         transaction.port_cfg     = cfg;
         transaction.xact_type    = svt_axi_transaction::WRITE;
         transaction.addr         = address;
         transaction.burst_type   = svt_axi_transaction::INCR;
         transaction.burst_size   = svt_axi_transaction::BURST_SIZE_64BIT;
         transaction.atomic_type  = svt_axi_transaction::NORMAL;
         transaction.burst_length = 1;

         transaction.data         = new[transaction.burst_length];
         transaction.wstrb        = new[transaction.burst_length];
         transaction.data_user    = new[transaction.burst_length];
         transaction.wvalid_delay = new[transaction.burst_length];

         transaction.data[0] = data;
         transaction.wstrb[0] = '1;
         transaction.wvalid_delay[0]=$urandom_range(0,10);


        /** Send the write transaction */
        `uvm_send(transaction)

        /** Wait for the write transaction to complete */
        get_response(rsp);

      end

      `uvm_info("body", "AXI transaction completed", UVM_MEDIUM);

      `uvm_info("body", "Exiting...", UVM_HIGH)
    end
    $fclose(file);

  endtask: body

endclass: axi_master_file_sequence

`endif // GUARD_AXI_MASTER_FILE_SEQUENCE_SV
