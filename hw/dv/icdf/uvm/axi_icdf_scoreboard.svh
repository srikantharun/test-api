`ifndef GUARD_AXI_ICDF_SCOREBOARD_SV
`define GUARD_AXI_ICDF_SCOREBOARD_SV
//The uvm_analysis_imp_decl allows for a scoreboard (or other analysis component) to
// support input from many places
/** Macro that define two analysis ports with unique suffixes */
`uvm_analysis_imp_decl(_out_stream)

class axi_icdf_scoreboard extends uvm_scoreboard;

  /** Analysis port conneted to the AXI Slave Agent */
  uvm_analysis_imp_out_stream#(svt_axi_transaction, axi_icdf_scoreboard) item_observed_out_stream_export;

  /** UVM Component Utility macro */
  `uvm_component_utils(axi_icdf_scoreboard)

  string last_path;
  int line_cnt = 1;
  int prev_tot_num_lines = 0;
  int curr_tot_num_lines = 0;

  function new (string name = "axi_icdf_scoreboard", uvm_component parent=null);
    super.new(name, parent);
  endfunction : new

  function string split_using_delimiter_fn(input longint offset, string str,string del, output longint cnt);
    for (longint i = offset; i < str.len(); i=i+1)
      if (str.getc(i) == del) begin
        cnt = i;
        return str.substr(offset,i-1);
      end
  endfunction

  function int get_num_lines_in_file(input string file_path);
    int num_lines=0;
    int fd;
    string line;
    bit status;
    //open file
    fd = $fopen(file_path, "r");
    `uvm_info("ICDF", $sformatf("filename is %0s", file_path), UVM_HIGH);
    //get the total number of lines
    while (!$feof(fd)) begin
      status = $fgets(line, fd);
      num_lines++;
    end
    //close file
    $fclose(fd);

    return num_lines;
  endfunction

  function void build_phase(uvm_phase phase);

    super.build();
    /** Construct the analysis ports */
    item_observed_out_stream_export = new("item_observed_out_stream_export", this);

  endfunction

  function bit is_output_data_consumed();
    `uvm_info ("is_output_data_consumed", $sformatf("line_cnt= %0d | curr_tot_num_lines= %0d", line_cnt-1, curr_tot_num_lines), UVM_HIGH)
    if((line_cnt-1) == curr_tot_num_lines) begin
      line_cnt=0;
      return 1;
    end
    else return 0;
  endfunction : is_output_data_consumed

  /** This method is called by item_observed_out_stream_export */
  virtual function void write_out_stream(input svt_axi_transaction xact);

    svt_axi_transaction resp_xact;
    int fd;
    string file;
    bit status;
    string line;
    logic [2047:0] data[$];
    string data_string [$];
    logic [31:0] burst_length;
    longint offset_in;
    longint offset_out;
    string path;
    string output_filename;

    status = uvm_config_db #(string)::get(null, "*", "path", path);
    `uvm_info("ICDF", $sformatf("Path DIR is %0s", path), UVM_LOW);
    status = uvm_config_db #(string)::get(null, "*", "output_filename", output_filename);
    `uvm_info("ICDF", $sformatf("Output filename is %0s.txt", output_filename), UVM_LOW);

    if (last_path != path) begin
      //get current total number of lines to be used in is_output_data_consumed() function
      curr_tot_num_lines = get_num_lines_in_file({path,output_filename,".txt"});
      line_cnt = 1;
    end

    last_path = path;

    file = {path,output_filename,".txt"};
    fd = $fopen(file, "r");

    if (!fd) begin  // in case we can't find the output filename, we die, because this is called from AXI SLAVE port, thus should always have a related file
      `uvm_fatal("ICDF", $sformatf("Couldn't open %s/%s.txt!", path, output_filename));
    end else begin
      if (!$cast(resp_xact, xact.clone())) begin
        `uvm_fatal("ICDF", "Unable to $cast the received transaction to svt_axi_transaction");
      end
      begin
        // Lines used in debug only:
        `uvm_info("ICDF", $sformatf("xact:\n%s", resp_xact.sprint()), UVM_MEDIUM)

        // Read the right line from the output file
        repeat (line_cnt)
          status = $fgets(line,fd);
        line_cnt++;
        offset_in=0;
        offset_out=0;

        /** Read transanction burst length from the first argument of the file */
        status = $sscanf(split_using_delimiter_fn(offset_in,line," ",offset_out),"%0d", burst_length);
        offset_in = offset_out+1;
        if (burst_length != resp_xact.stream_burst_length)
          `uvm_fatal("ICDF",  $sformatf("Burst length is not matching \n, Expected burst=%h \n Actual burst=%h",burst_length,resp_xact.stream_burst_length) );

        /** Read data bits from the file */
        for (int i=0; i < burst_length; i++) begin
          data_string[i] = split_using_delimiter_fn(offset_in,line," ",offset_out);
          if(offset_in >= offset_out) begin
            data_string[i] = line.substr(offset_in,line.len()-1);
          end else begin
            offset_in = offset_out+1;
          end
          // Lines used in debug only:
          `uvm_info("ICDF", $sformatf("offset_in=%0d offset_out=%0d",offset_in,offset_out), UVM_MEDIUM);
          `uvm_info("ICDF", $sformatf("DATA STRING %0d is %s",i+1,data_string[i]), UVM_MEDIUM);
        end

        foreach (data_string[i]) begin
          status = $sscanf(data_string[i], "%0h", data[i]);
          // Lines used in debug only:
          if (data[i] != resp_xact.tdata[i]) begin
            `uvm_fatal("ICDF",  $sformatf("Data of AXI stream do not match.\n Expected data: %h \n Actual data  : %h\n Diff         : %h", data[i],resp_xact.tdata[i],data[i]^resp_xact.tdata[i] ) );
          end
        end
      end
    end
    $fclose(fd);

  endfunction:write_out_stream

endclass // axi_icdf_scoreboard
`endif
