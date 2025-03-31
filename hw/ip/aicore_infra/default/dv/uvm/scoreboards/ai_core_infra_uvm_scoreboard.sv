`ifndef ai_core_infra_uvm_scoreboard_SV
`define ai_core_infra_uvm_scoreboard_SV
`uvm_numbered_analysis_imp_decl(_reference_data_init)
`uvm_numbered_analysis_imp_decl(_actual_data_targ)

class ai_core_infra_uvm_scoreboard extends uvm_scoreboard;


  parameter LOG1 = "log1.txt";
  parameter LOG2 = "log2.txt";
  
  // Analysis ports connections

  uvm_analysis_imp_reference_data_init#(svt_axi_transaction, ai_core_infra_uvm_scoreboard)  init_reference_data_export[`MST_NUM];
  uvm_analysis_imp_actual_data_targ#(svt_axi_transaction, ai_core_infra_uvm_scoreboard)     targ_actual_data_export[`SLV_NUM];

  // UVM Component Utility macro
  `uvm_component_utils(ai_core_infra_uvm_scoreboard)

  // Variables to track the count of initiators pkts
  int num_of_exp_wr_pkts[`MST_NUM];
  int num_of_exp_rd_pkts[`MST_NUM];

  // Variables to track the count of targets pkts
  int num_of_act_wr_pkts[`SLV_NUM];
  int num_of_act_rd_pkts[`SLV_NUM];

  // Associative array to store reference data from initiators
  svt_axi_transaction ref_txn_arry[`MST_NUM][int];

  // Associative array to store actual data from targets 
  svt_axi_transaction act_txn_temp[`SLV_NUM];

  // Queues to store reference data from initiators 
  svt_axi_transaction ref_txn_wr_Q_init[`MST_NUM][$],
                      ref_txn_rd_Q_init[`MST_NUM][$],
  // Queues to store actual data from targets 
                      act_txn_wr_Q_targ[`SLV_NUM][$],
                      act_txn_rd_Q_targ[`SLV_NUM][$];

  bit [40-1:0]    targ_addr_min[`SLV_NUM], targ_addr_max[`SLV_NUM];



  int fid1,fid2;    
  
  bit [(512-1):0] global_mem[*];


  // Constructor class 
  function new (string name = "ai_core_infra_uvm_scoreboard", uvm_component parent=null);
    super.new(name, parent);
  endfunction : new

  // Build phase to create ports 
  function void build_phase(uvm_phase phase);
    super.build();
    
    // Construct the analysis ports for initiators
    for (int i = 0; i < `MST_NUM; i++) begin
      init_reference_data_export[i] = new($sformatf("init_reference_data_export_%0d", i)  , this);
      init_reference_data_export[i].imp_id = i;
    end

    // Construct the analysis ports for targets
    for (int i = 0; i < `SLV_NUM; i++) begin
      targ_actual_data_export[i] = new($sformatf("targ_actual_data_export_%0d", i)  , this);
      targ_actual_data_export[i].imp_id = i;
    end

  endfunction : build_phase

  // Run Phase 
  task run_phase(uvm_phase phase);
    fid1 =$fopen(LOG1,"w");
    fid2 =$fopen(LOG2,"w");
    
    mem_init(); 
    //fork
    //  write_channel();
    //  read_channel();
    //join
  endtask : run_phase
 
  function bit valid_write_trans(ref svt_axi_transaction tr);
    return tr.xact_type == svt_axi_transaction::WRITE && tr.bresp == svt_axi_transaction::OKAY ||
           tr.xact_type == svt_axi_transaction::COHERENT && tr.coherent_xact_type == svt_axi_transaction::WRITENOSNOOP && tr.bresp == svt_axi_transaction::EXOKAY;
  endfunction
 
  function bit valid_read_trans(ref svt_axi_transaction tr);
    return tr.xact_type == svt_axi_transaction::READ && tr.rresp[0] == svt_axi_transaction::OKAY ||
           tr.xact_type == svt_axi_transaction::COHERENT && tr.coherent_xact_type == svt_axi_transaction::READNOSNOOP && tr.rresp[0] == svt_axi_transaction::EXOKAY;
  endfunction


  function bit check_bresp(ref svt_axi_transaction tr);
    return tr.atomic_type == svt_axi_transaction::NORMAL && tr.bresp != svt_axi_transaction::OKAY ||
           tr.atomic_type == svt_axi_transaction::EXCLUSIVE && tr.bresp != svt_axi_transaction::EXOKAY;

  endfunction

  function bit check_rresp(ref svt_axi_transaction tr);
    return tr.atomic_type == svt_axi_transaction::NORMAL && tr.rresp[0] != svt_axi_transaction::OKAY ||
           tr.atomic_type == svt_axi_transaction::EXCLUSIVE && tr.rresp[0] != svt_axi_transaction::EXOKAY;
  endfunction

 
  // write methods which are called by initiators export 
  virtual function void  write_reference_data_init(input svt_axi_transaction ref_txn, int imp_id);
    svt_axi_transaction txn;
    masters_t mst = imp_id;
    string mst_name = $sformatf("%0d_%s", imp_id, mst.name);
    

    bit [(64-1):0] wstrb_q[`MST_NUM][$];
    bit [(512-1):0] wdata_q[`MST_NUM][$];
    bit [(512-1):0] rdata_q[`MST_NUM][$];

    `uvm_info("aic_infra_scb", $sformatf("write_reference_data_init_%s received packet", mst_name), UVM_LOW)
    ref_txn.print();

    if(valid_write_trans(ref_txn)) begin
      `uvm_info("aic_infra_scb", $sformatf("%s packet received from scoreboard and addr is %0h ", mst_name, ref_txn.addr), UVM_LOW)
      //ref_txn.print();
      ref_txn_wr_Q_init[imp_id].push_back(ref_txn);
      num_of_exp_wr_pkts[imp_id]++;

      // BURST_TYPE -> FIXED
      if(ref_txn.burst_type == svt_axi_transaction::FIXED)begin
          for(int unsigned index = 0, bit [(40-1):0] start_addr = ref_txn.addr;
              index < ref_txn.burst_length;
              index++) begin
            for (int unsigned byte_index = 0; byte_index < (1 << ref_txn.burst_size); byte_index++) begin
              if (ref_txn.wstrb[index][byte_index] == 1) begin
                global_mem[start_addr + byte_index] = ref_txn.data[index][((byte_index + 1)*8 - 1) -: 8];
              end
            end
            $fwrite(fid1,"%0t MASTER[%s] Local_MEM[%0h] = %h, AWADDR = %0h, AWSTRB = %0b, AWLEN = %0d, AWSIZE = %0h, AWBURST = %0d, BID = %0d, BRESP = %0d\n", $time, mst_name, start_addr, ref_txn.data[index], start_addr, ref_txn.wstrb[index], ref_txn.burst_length, ref_txn.burst_size, ref_txn.burst_type, ref_txn.id, ref_txn.get_response_status());
          end
      end

      // BURST_TYPE -> INCR
      if(ref_txn.burst_type == svt_axi_transaction::INCR)begin
          for(int unsigned index = 0, bit [(40-1):0] start_addr = ref_txn.addr;
              index<ref_txn.burst_length;
              index++,start_addr=start_addr+(2**(ref_txn.burst_size))) begin
            for (int unsigned byte_index = 0; byte_index < (1 << ref_txn.burst_size); byte_index++) begin
              if (ref_txn.wstrb[index][byte_index] == 1) begin
                global_mem[start_addr + byte_index] = ref_txn.data[index][((byte_index + 1)*8 - 1) -: 8];
              end
            end         
            $fwrite(fid1,"%0t MASTER[%0s] Local_MEM[%0h] = %0h, AWADDR = %0h, AWSTRB = %0b, AWLEN = %0d, AWSIZE = %0h, AWBURST = %0d, BID = %0d, BRESP = %0d, WDATA[%0d] = %0h\n", $time, mst_name, start_addr, ref_txn.data[index], start_addr, ref_txn.wstrb[index], ref_txn.burst_length, ref_txn.burst_size, ref_txn.burst_type, ref_txn.id, ref_txn.get_response_status(), index, ref_txn.data[index]);
          end
      end

      // BURST_TYPE -> WRAP
      if(ref_txn.burst_type == svt_axi_transaction::WRAP)begin
          bit [(35-1):0]  start_addr;
          int unsigned total_no_of_bytes,aligned_addr,wrap_boundary,net;
        
          start_addr         =  ref_txn.addr;
          total_no_of_bytes  =  ((2**(ref_txn.burst_size))*(ref_txn.burst_length));
          net                =  ((start_addr)/(total_no_of_bytes));
          aligned_addr       =  ((net)*total_no_of_bytes);
          wrap_boundary      =  aligned_addr+(total_no_of_bytes-1);

          for(int unsigned index=0;
              index<ref_txn.burst_length;
              index++,start_addr=start_addr+(2**(ref_txn.burst_size)))begin
            
            if (start_addr > wrap_boundary) begin 
              start_addr = aligned_addr;
              //$fwrite(fid1,"MASTER_NUM[%d] Boundry Crossed:start_addr=%h\n",start_addr); 
            end
            
            for (int unsigned byte_index = 0; byte_index < 64; byte_index++) begin
              if (ref_txn.wstrb[index][byte_index] == 1) begin
                global_mem[start_addr + byte_index] = ref_txn.data[index][((byte_index + 1)*8 - 1) -: 8];
              end 
            end  
            $fwrite(fid1,"%0t MASTER[%s] Local_MEM[%0h] = %0h, AWADDR = %0h, AWSTRB = %0b, AWLEN = %0d, AWSIZE = %0h, AWBURST = %0d, BID = %0d, BRESP = %0d\n", $time, mst_name, start_addr, ref_txn.data[index], start_addr, ref_txn.wstrb[index], ref_txn.burst_length, ref_txn.burst_size, ref_txn.burst_type, ref_txn.id, ref_txn.get_response_status());
          end
        //end 
      end
    
    end//if
    else if(valid_read_trans(ref_txn)) begin
      bit [5:0]   start_valid_byte_pos;
      int         end_valid_byte_pos;
      bit [511:0] exp_data, act_data; //exp - mem data //act - rdata
      start_valid_byte_pos  = (ref_txn.addr % (2**(ref_txn.burst_size)));
      end_valid_byte_pos    = start_valid_byte_pos + (2**(ref_txn.burst_size));
      if(end_valid_byte_pos > 'd64)
        end_valid_byte_pos = 'd64;
      
      `uvm_info("aic_infra_scb", $sformatf("%s reference_data packet received from scoreboard and addr is %0h ", mst_name, ref_txn.addr), UVM_LOW)
      ref_txn_rd_Q_init[imp_id].push_back(ref_txn);
      num_of_exp_rd_pkts[imp_id]++;

    // BURST_TYPE -> FIXED
      if(ref_txn.burst_type == svt_axi_transaction::FIXED)begin

          exp_data = 0;
          for (int k = 0; k < (1 <<  ref_txn.burst_size); k++)
            exp_data[k*8 +: 8] = global_mem[ref_txn.addr + k][7:0];

          for(int unsigned index = 0, bit [(40-1):0] start_addr = ref_txn.addr;
              index<ref_txn.burst_length;
              index++) begin

            if (exp_data === 'hXXXX_XXXX) begin
              $fwrite(fid2,"%0t MASTER[%s] UN WRITTEN: Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, ref_txn.data[index], start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
            else if (exp_data == ref_txn.data[index]) begin 
              $fwrite(fid2,"%0t MASTER[%s] PASS      : Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, ref_txn.data[index], start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
            else begin 
              $fwrite(fid2,"%0t MASTER[%s] FAIL      : Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, ref_txn.data[index], start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
          end
      end
      
      // BURST_TYPE -> INCR
      if(ref_txn.burst_type == svt_axi_transaction::INCR)begin
          foreach (ref_txn.data[idx])
            rdata_q[imp_id].push_back(ref_txn.data[idx]);
          for(int unsigned index = 0, bit [(40-1):0] start_addr = ref_txn.addr;
            index<ref_txn.burst_length;
            index++,start_addr=start_addr+(2**(ref_txn.burst_size))) begin
            exp_data = 0;
            for (int k = 0; k < (1 <<  ref_txn.burst_size); k++)
              exp_data[k*8 +: 8] = global_mem[start_addr + k][7:0];
            exp_data = exp_data >> (start_valid_byte_pos*8);
            act_data = ref_txn.physical_data[index];
            act_data = act_data >> (start_valid_byte_pos*8);

            if (exp_data === 'hXXXX_XXXX) begin
              $fwrite(fid2,"%0t MASTER[%s] UN WRITTEN: Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, rdata_q[imp_id][index], start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
            else if (exp_data == act_data)begin 
              $fwrite(fid2,"%0t MASTER[%s] PASS      : Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, act_data, start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
            else begin 
              $fwrite(fid2,"%0t MASTER[%s] FAIL      : Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, act_data, start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
          end
      end
      
      // BURST_TYPE -> WRAP
      if(ref_txn.burst_type == svt_axi_transaction::WRAP)begin

          bit [(40-1):0]  start_addr;
          int unsigned total_no_of_bytes,aligned_addr,wrap_boundary,net;
          
          start_addr         =  ref_txn.addr;
          total_no_of_bytes  =  ((2**(ref_txn.burst_size))*(ref_txn.burst_length));
          net                =  ((start_addr)/(total_no_of_bytes));
          aligned_addr       =  ((net)*total_no_of_bytes);
          wrap_boundary      =  aligned_addr+(total_no_of_bytes-1);
              
          //$fwrite(fid2,"MASTER_NUM[%d] Aligned_Addr = %h,Wrap_Boundary = %h\n",aligned_addr,wrap_boundary);
          foreach (ref_txn.data[idx])
            rdata_q[imp_id].push_back(ref_txn.data[idx]);
          for(int unsigned index = 0;
              index<ref_txn.burst_length;
              index++,start_addr=start_addr+(2**(ref_txn.burst_size))) begin
          
            if (start_addr > wrap_boundary) begin 
              start_addr = aligned_addr; 
              //$fwrite(fid2,"MASTER_NUM[%d] Boundry Crossed:start_addr=%h\n",start_addr); 
            end

            exp_data = 0;
            for (int k = 0; k < (1 <<  ref_txn.burst_size); k++)
              exp_data[k*8 +: 8] = global_mem[start_addr + k][7:0];
            
            if (exp_data === 'hXXXX_XXXX) begin
              $fwrite(fid2,"%0t MASTER[%s] UN WRITTEN: Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, ref_txn.data[index], start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
            else if (exp_data == rdata_q[imp_id][index]) begin 
              $fwrite(fid2,"%0t MASTER[%s] PASS      : Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, ref_txn.data[index], start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
            else begin 
              $fwrite(fid2,"%0t MASTER[%s] FAIL      : Write_data[%0h] = %0h, Read_data[%0h] = %0h, ARADDR = %0h, ARBURST = %0d, ARLEN = %0d, ARSIZE = %0h, RID = %0d, RRESP = %0d\n", $time, mst_name, start_addr, exp_data, index, ref_txn.data[index], start_addr, ref_txn.burst_type, ref_txn.burst_length, ref_txn.burst_size, ref_txn.id, ref_txn.get_response_status());
            end
          end
        //end
      end
    
    
    end//if
    else if(check_bresp(ref_txn))
      `uvm_info("aic_infra_scb", $sformatf("Received BRESP = %s for illegal access from %s to ADDR = %0h", ref_txn.bresp, mst_name, ref_txn.addr), UVM_LOW)
    else if(check_rresp(ref_txn))
      `uvm_info("aic_infra_scb", $sformatf("Received RRESP = %s for illegal access from %s to ADDR = %0h", ref_txn.rresp[0], mst_name, ref_txn.addr), UVM_LOW)
    else
      `uvm_error("aic_infra_scb",$sformatf("SCOREBOARD ERROR %s reference_data: Neither WRITE nor READ request received, transaction: \n %s ", mst_name, ref_txn.sprint()))

  endfunction : write_reference_data_init

  // write methods which are called by targets export 
  virtual function void write_actual_data_targ(input svt_axi_transaction act_txn, int imp_id);
    svt_axi_transaction txn;
    slaves_t slv = imp_id;
    string slv_name = $sformatf("%0d_%s", imp_id, slv.name);

    `uvm_info("aic_infra_scb", $sformatf("write_actual_data_targ_%s received packet", slv_name), UVM_LOW)
    act_txn.print();

    if(act_txn.xact_type == svt_axi_transaction::WRITE) begin
      `uvm_info("aic_infra_scb", $sformatf("actual_data_targ_%s write packet received with addr %0h ", slv_name, act_txn.addr), UVM_LOW)
      act_txn_wr_Q_targ[imp_id].push_back(act_txn);
      num_of_act_wr_pkts[imp_id]++;
    end
    else if(act_txn.xact_type == svt_axi_transaction::READ) begin
      `uvm_info("aic_infra_scb", $sformatf("actual_data_targ_%s read packet received with addr is %0h ", slv_name, act_txn.addr), UVM_LOW)
      act_txn_rd_Q_targ[imp_id].push_back(act_txn);
      num_of_act_rd_pkts[imp_id]++;
    end
    else
      `uvm_error("aic_infra_scb","SCOREBOARD ERROR Neither WRITE nor READ request received")

  endfunction : write_actual_data_targ

  
  // Memory Initialization Task 
  task mem_init();
    global_mem.delete();
    `uvm_info("aic_infra_scb", "Local MEM Initialized", UVM_LOW)
  endtask : mem_init


endclass
`endif
