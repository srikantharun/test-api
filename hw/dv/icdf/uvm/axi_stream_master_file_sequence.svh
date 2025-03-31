//=======================================================================
// COPYRIGHT (C) 2010, 2011, 2012, 2013 SYNOPSYS INC.
// This software and the associated documentation are confidential and
// proprietary to Synopsys, Inc. Your use or disclosure of this software
// is subject to the terms and conditions of a written license agreement
// between you, or your company, and Synopsys, Inc. In the event of
// publications, the following notice is applicable:
//
// ALL RIGHTS RESERVED
//
// The entire notice above must be reproduced on all authorized copies.
//-----------------------------------------------------------------------

/**
 * Abstract:
 * axi_stream_master_file_sequence is used by test to provide initiator scenario
 * information to the Master agent present in the System agent.  This class
 * defines a sequence in which an AXI4 STREAM
 * sequence is generated using `uvm_do_with macros and the data are provided via a file.
 *
 * Execution phase: main_phase
 * Sequencer: Master agent sequencer
 */

`ifndef GUARD_AXI_STREAM_MASTER_FILE_SEQUENCE_SV
`define GUARD_AXI_STREAM_MASTER_FILE_SEQUENCE_SV

class axi_stream_master_file_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 10;
  string filename;
  string path;
  int file;
  string line;
  logic [2047:0] data [$];
  string data_string [$];
  logic [31:0] burst_length;
  string burst_len_string;


  /** UVM Object Utility macro */
  `uvm_object_utils(axi_stream_master_file_sequence)

  /** Class Constructor */
  function new(string name="axi_stream_master_file_sequence");
    super.new(name);
  endfunction

   function string split_using_delimiter_fn(input longint offset, string str,string del, output longint cnt);
     for (longint i = offset; i < str.len(); i=i+1)
       if (str.getc(i) == del) begin
          cnt = i;
          return str.substr(offset,i-1);
        end
   endfunction


  virtual task body();
    bit status;
    svt_axi_master_transaction transaction;
    svt_configuration get_cfg;
    longint offset_in;
    longint offset_out;

    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

     /** Read the input filename  */
    status = uvm_config_db #(string)::get(null, get_full_name(), "filename", filename);
    `uvm_info("ICDF", $sformatf("filename is %0s", filename), UVM_LOW);

    /** Read the test path DIR  */
    status = uvm_config_db #(string)::get(null, get_full_name(), "path", path);
    `uvm_info("ICDF", $sformatf("Path DIR is %0s", path), UVM_LOW);

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    #20;

    /** Open the input stimuli data file */
    file = $fopen({path,filename,".txt"}, "r");
    if (!file) begin
      `uvm_info("ICDF", $sformatf("Couldn't open %s/%s.txt, exiting!", path, filename), UVM_LOW);  // there isn't necessary a command for every AXI MASTER every test (not both ODR are working), so if there isn't, no problem, just don't run anything
    end else begin

      /** Until the end of the file read the data */
      while (!$feof(file)) begin

        /**  Get transaction info from file */
        status = $fgets(line,file);
        offset_in=0;
        offset_out=0;

        /**  Read transanction burst length from the first argument of the file */
        status = $sscanf(split_using_delimiter_fn(offset_in,line," ",offset_out),"%0d", burst_length);

        offset_in = offset_out+1;
        `uvm_info("ICDF", $sformatf("offset_in=%0d offset_out=%0d",offset_in,offset_out), UVM_MEDIUM);
        `uvm_info("ICDF", $sformatf("BURST_LN=%0d",burst_length), UVM_MEDIUM);

        for (longint i=0; i < burst_length; i++) begin
            data_string[i] = split_using_delimiter_fn(offset_in,line," ",offset_out);
            if(offset_in >= offset_out) begin
              data_string[i] = line.substr(offset_in,line.len()-1);
            end else begin
              offset_in = offset_out+1;
            end
            // Lines used in debug only:
            `uvm_info("ICDF", $sformatf("offset_in=%0d offset_out=%0d",offset_in,offset_out), UVM_MEDIUM);
            `uvm_info("ICDF", $sformatf("DATA STRING %0d is %s",i,data_string[i]), UVM_MEDIUM);
        end

        /**  Read the data of the transaction from the string into the data array */
        foreach (data_string[i]) begin
          status =  $sscanf(data_string[i], "%0h", data[i]);
        end

        `uvm_create(transaction)
        transaction.port_cfg            = cfg;
        transaction.xact_type           = svt_axi_transaction::DATA_STREAM;
        transaction.stream_burst_length = burst_length;
        transaction.enable_interleave   = 0;
        transaction.tdata               = new[transaction.stream_burst_length];
        transaction.tvalid_delay        = new[transaction.stream_burst_length];
        transaction.interleave_pattern  = svt_axi_transaction::RANDOM_BLOCK;

        foreach (transaction.tdata[i]) begin
          transaction.tdata[i] = data[i];
        end

        foreach (transaction.tvalid_delay[i]) begin
          transaction.tvalid_delay[i] = 0;
        end

        `uvm_send(transaction)

        get_response(rsp);

      end

      `uvm_info("body", "Exiting...", UVM_LOW)
      $fclose(file);
    end

  endtask: body

endclass: axi_stream_master_file_sequence

`endif // GUARD_AXI_STREAM_MASTER_FILE_SEQUENCE_SV

