`ifndef GUARD_AXI_STREAM_SLAVE_MONITOR_SV
`define GUARD_AXI_STREAM_SLAVE_MONITOR_SV

class axi_stream_slave_monitor;

//** UVM Object Utility macro */
//
//virtual svt_axi_port_if axi_port_if;
//
//virtual task run ( input int index);
//
// int fds;
// string filename;
//
// filename = "out_data.txt";
// fds= $fopen(filename_end, "a+");
//
//  forever @(posedge axi_port_if.clk) begin
//       if(axi_port_if.tvalid & axi_port_if.tready) begin
//          $fdisplay(fds,axi_port_if.tdata);
//       end
//   end
//
//    $fclose(fds);
//
// endtask

   //virtual function void build_phase(uvm_phase phase);
   //    super.build_phase(phase);
   //    `uvm_info("MON_INPUT_SRAM", "build", UVM_FULL);
   //    fd = $fopen(file_path, "w");
   //    if(!uvm_config_db #(virtual input_SRAM_out_uvm)::get(this,"","in_sram_out_if", in_sram_out_if)) begin
   //        `uvm_error("build_phase", "configDB")
   //    end
   //endfunction

  // virtual task run_phase(uvm_phase phase);
  //     `uvm_info("MON_INPUT_SRAM", "run", UVM_FULL);
  //     input_sram_pro();
  // endtask

  //  virtual function void report_phase(uvm_phase phase);
  //    `uvm_info ("MON_INPUT_SRAM", "report", UVM_FULL);
  //    $fclose(fd);
  //  endfunction

  //  virtual task input_sram_pro();
  //      forever begin
  //          @(posedge in_sram_out_if.clk iff(in_sram_out_if.rst_n));
  //          if(in_sram_out_if.data_out != 0) begin
  //            $fwrite(fd, "%X\n", in_sram_out_if.data_out);
  //            //for(int i = 0; i < no_of_byte_in_out; i++)
  //            //  byte_data = in_sram_out_if.data_out[((i+1)*8)-1 : i*8];
  //            //  $fwrite(fd, "%d\n", byte_data);
  //          end
  //      end
  //  endtask


endclass: axi_stream_slave_monitor


`endif //GUARD_AXI_STREAM_SLAVE_MONITOR_SV
