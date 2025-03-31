// ===========================================================================================================//
// *** (C) Copyright Axelera AI 2021                                                                      *** //
// *** All Rights Reserved                                                                                *** //
// *** Axelera AI Confidential                                                                            *** //
// *** Owner : srinivas.prakash@axelera.ai                                                                *** //
// *** Description : This module monitors the binded DUT's AXI Interface for performance benchmarking,    *** //
//                   data comparision, & other misc features                                              *** //
// ===========================================================================================================//

`ifndef __AXI_TRACKER_DEFINE__ 
`define __AXI_TRACKER_DEFINE__

module axi_tracker
                 (
                  aclk,
                  arstn,
                  awaddr,
                  awburst,
                  awsize,
                  awcache,
                  awid,
                  awlen,
                  awlock,
                  awprot,
                  awready,
                  awvalid,
                  awqos,
                  wdata, 
                  wstrb,
                  wlast,
                  wready,
                  wvalid,
                  araddr,
                  arburst,
                  arsize,
                  arcache,
                  arid,
                  arlen,
                  arlock,
                  arprot,
                  arready,
                  arvalid,
                  arqos,
                  rid,
                  rdata, 
                  rresp,
                  rlast,
                  rready,
                  rvalid,
                  bid,
                  bresp,
                  bready,
                  bvalid
                 );
  import axi_pkg::*;              
  import axi_tracker_pkg::*;
  
  // ===========================================================================================================
  //  Params declarations 
  // ===========================================================================================================
  parameter WR_TRACE                            = "axi_tracker_wr_txns.txt";
  parameter RD_TRACE                            = "axi_tracker_rd_txns.txt";
  parameter real CLK_PERIOD_IN_NS               = 1.25;
  parameter int unsigned AXI_DATA_WIDTH         = 512;
  parameter int unsigned AXI_ADDR_WIDTH         = 40; 
  parameter int unsigned AXI_ID_WIDTH           = 6;
  
  // ===========================================================================================================
  // Clk & Rst declarations 
  // ===========================================================================================================
  input bit aclk; 
  input bit arstn;
  // ===========================================================================================================
  // AW Channel signal declarations 
  // ===========================================================================================================
  input bit [AXI_ADDR_WIDTH-1  : 0]   awaddr; 
  input bit [AXI_ID_WIDTH-1    : 0]   awid;
  input axi_burst_t                   awburst;
  input axi_size_t                    awsize;
  input axi_cache_t                   awcache;
  input axi_len_t                     awlen;
  input axi_prot_t                    awprot;
  input bit                           awlock;
  input bit                           awready;
  input bit                           awvalid;
  input bit[3:0]                      awqos;
  // ===========================================================================================================
  // W Channel signal declarations 
  // ===========================================================================================================
  input bit [AXI_DATA_WIDTH-1    : 0] wdata;
  input bit [(AXI_DATA_WIDTH/8)-1: 0] wstrb; 
  input bit                           wlast;
  input bit                           wready;
  input bit                           wvalid;
  // ===========================================================================================================
  // B Channel signal declarations 
  // ===========================================================================================================
  input bit [AXI_ID_WIDTH-1      : 0] bid;
  input axi_resp_t                    bresp;
  input bit                           bready;
  input bit                           bvalid;
  // ===========================================================================================================
  // AR Channel signal declarations 
  // ===========================================================================================================
  input bit [AXI_ADDR_WIDTH-1    : 0] araddr; 
  input bit [AXI_ID_WIDTH-1      : 0] arid;
  input axi_burst_t                   arburst;
  input axi_size_t                    arsize;
  input axi_cache_t                   arcache;
  input axi_len_t                     arlen;
  input axi_prot_t                    arprot;
  input bit                           arlock;
  input bit                           arready;
  input bit                           arvalid;
  input bit[3:0]                      arqos;
  // ===========================================================================================================
  // R Channel signal declarations 
  // ===========================================================================================================
  input bit [AXI_ID_WIDTH-1      : 0] rid;
  input bit [AXI_DATA_WIDTH-1    : 0] rdata;
  input axi_resp_t                    rresp;
  input bit                           rlast;
  input bit                           rready;
  input bit                           rvalid;
  // ===========================================================================================================
  // Misc declarations 
  // ===========================================================================================================
  int                                 fid1,fid2,fid3;    
  localparam	  ADDRLSB = $clog2(AXI_DATA_WIDTH/8);
  aw_channel_obj #(.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),.AXI_ID_WIDTH(AXI_ID_WIDTH)) aw_channel_q [$];
  ar_channel_obj #(.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),.AXI_ID_WIDTH(AXI_ID_WIDTH)) ar_channel_q [$];
  r_channel_obj  #(.AXI_ID_WIDTH(AXI_ID_WIDTH),.AXI_DATA_WIDTH(AXI_DATA_WIDTH)) r_channel_q  [$];
  w_channel_obj  #(.AXI_DATA_WIDTH(AXI_DATA_WIDTH))                             w_channel_q  [$];
  b_channel_obj  #(.AXI_ID_WIDTH(AXI_ID_WIDTH))                                 b_channel_q  [$];
  bit[(64-1):0]   wr_txn_count=0, 
                  rd_txn_count=0;
  typedef struct {
    axi_len_t s_awlen;
    axi_size_t s_awsize;
    axi_burst_t s_awburst;
    axi_len_t s_arlen;
    axi_size_t s_arsize;
    axi_burst_t s_arburst;
    bit [AXI_ID_WIDTH-1:0] txn_id;
    real throughput_in; 
    int resp_latency_in;
  } s_axi_attr;
  real total_wr_bytes = 0;
  real total_rd_bytes = 0;
  real clk_period_in_sec = (CLK_PERIOD_IN_NS * 1e-9);
  real total_wr_time_sec = 0, total_rd_time_sec = 0;
  real total_wr_bandwidth = 0, total_rd_bandwidth = 0;
  ar_channel_obj #(.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),.AXI_ID_WIDTH(AXI_ID_WIDTH)) ar_channel_dict[string]; // Associative array for AR transactions
  r_channel_obj #(.AXI_ID_WIDTH(AXI_ID_WIDTH),.AXI_DATA_WIDTH(AXI_DATA_WIDTH)) r_channel_dict[string];   // Associative array for R transactions
  integer ar_txn_id_counter = 0, r_txn_id_counter = 0;  // Unique transaction ID counter
  
  // ===========================================================================================================
  // File I/O Initialization  
  // ===========================================================================================================
  initial begin : FILE_IO_BLK //{
    if($test$plusargs("GEN_REPORT")) begin //{
      fid1 =$fopen(WR_TRACE,"w");
      $fwrite(fid1,"TIME,TXN_ID,THROUGHPUT,BRESP_LATENCY,AWLEN,AWSIZE,AWBURST");
      fid2 =$fopen(RD_TRACE,"w");
      $fwrite(fid2,"TIME,TXN_ID,THROUGHPUT,RRESP_LATENCY,ARLEN,ARSIZE,ARBURST");
    end //}
    else begin //{
      fid1 =$fopen(WR_TRACE,"w");
      $fwrite(fid1,"PERFORMACE TRACKER GENERATE REPORT NOT ENABLED - Pass PLUSARG +GEN_REPORT");
      fid2 =$fopen(RD_TRACE,"w");
      $fwrite(fid2,"PERFORMACE TRACKER GENERATE REPORT NOT ENABLED - Pass PLUSARG +GEN_REPORT");
    end //}
  end //}
  // ===========================================================================================================
  // Initialization  
  // ===========================================================================================================
  initial begin : START_THREADS //{
    if($test$plusargs("EN_TRACKER")) begin //{
      fork
        fwd_aw_txns();
        fwd_w_txns();
        fwd_b_txns();
        align_aw_w_channel();
        fwd_ar_txns();
        fwd_r_txns();
        align_ar_r_channel();
      join
    end //}
    else begin //{
      fid1 =$fopen(WR_TRACE,"w");
      $fwrite(fid1,"PERFORMACE TRACKER NOT ENABLED - Pass PLUSARG +EN_TRACKER");
      fid2 =$fopen(RD_TRACE,"w");
      $fwrite(fid2,"PERFORMACE TRACKER NOT ENABLED - Pass PLUSARG +EN_TRACKER");
    end //}
  end //}
  // ===========================================================================================================
  // Task to forward the AW Channel interface signals to its respective class object 
  // ===========================================================================================================
  task automatic fwd_aw_txns;
    aw_channel_obj #(.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),.AXI_ID_WIDTH(AXI_ID_WIDTH)) aw_obj_h;
    forever begin //{
      @(posedge aclk);
      aw_obj_h = new();
      if(awvalid && awready) begin //{
        aw_obj_h.awaddr                   = awaddr;    
        aw_obj_h.awburst                  = awburst;   
        aw_obj_h.awsize                   = awsize;      
        aw_obj_h.awcache                  = awcache;     
        aw_obj_h.awid                     = awid;        
        aw_obj_h.awlen                    = awlen;       
        aw_obj_h.awlock                   = awlock;        
        aw_obj_h.awprot                   = awprot;
        aw_obj_h.num_bytes                = 2**awsize;
        aw_obj_h.burst_len                = awlen+1;
        aw_obj_h.total_bytes_requested    = ((2**awsize) * (awlen+1));
        aw_obj_h.txn_req_start_time       = $realtime() - CLK_PERIOD_IN_NS; 
        aw_channel_q.push_back(aw_obj_h);
      end//}
    end//}
  endtask : fwd_aw_txns
  // ===========================================================================================================
  // Task to forward the W Channel interface signals to its respective class object 
  // ===========================================================================================================
  task automatic fwd_w_txns();
    bit[(512-1):0] count=0, temp;
    w_channel_obj #(.AXI_DATA_WIDTH(AXI_DATA_WIDTH)) w_obj_h;
    forever begin //{
      @(posedge aclk);
      if(wvalid && wready) begin //{
        if(count == 0)
          w_obj_h = new();
        else
          count=count;

        w_obj_h.zero_wstrb                = w_obj_h.zero_wstrb + !(|wstrb);
        w_obj_h.valid_wstrb               = w_obj_h.valid_wstrb + (|wstrb);
        w_obj_h.wr_beat_count             = w_obj_h.wr_beat_count + 1;
        w_obj_h.wdata.push_back(wdata);         
        w_obj_h.wstrb.push_back(wstrb);  
        
        if(wlast) begin //{
          temp = temp + 1;
          count                     = 0;
          w_obj_h.txn_req_end_time  = $realtime - CLK_PERIOD_IN_NS;
          w_obj_h.zero_wstrb        = w_obj_h.zero_wstrb;
          w_obj_h.valid_wstrb       = w_obj_h.valid_wstrb;
          w_obj_h.wr_beat_count     = w_obj_h.wr_beat_count;
          w_channel_q.push_back(w_obj_h); 
        end //}
        else
          count++;
      end //}
      else if(wvalid && !wready) begin //{
        if(count == 0)
          w_obj_h = new();
        else
          count=count;
        w_obj_h.wr_stall_slv = w_obj_h.wr_stall_slv + 1;
      end //}
      else if(!wvalid && wready) begin //{
        if(count == 0)
          w_obj_h = new();
        else
          count=count;
        w_obj_h.wr_stall_mst = w_obj_h.wr_stall_mst + 1;
      end //}
    end //}
  endtask : fwd_w_txns
  // ===========================================================================================================
  // Task to forward the B Channel interface signals to its respective class object 
  // ===========================================================================================================
  task automatic fwd_b_txns();
    b_channel_obj #(.AXI_ID_WIDTH(AXI_ID_WIDTH)) b_obj_h ;
    forever begin //{
      @(posedge aclk);
      b_obj_h = new();
      if(bvalid && bready) begin //{
        b_obj_h.bid                       = bid;         
        b_obj_h.bresp                     = bresp;         
        b_obj_h.txn_req_end_time          = $realtime - CLK_PERIOD_IN_NS;
        b_channel_q.push_back(b_obj_h); 
      end //}
      else if(bvalid && !bready) begin //{
        b_obj_h.b_stall_mst              = b_obj_h.b_stall_mst + 1;         
      end //}
      else if(!bvalid && bready) begin //{
        b_obj_h.b_stall_slv              = b_obj_h.b_stall_slv + 1;         
      end //}
    end //}
  endtask : fwd_b_txns
  // ===========================================================================================================
  // Task to sync AW & W Channel interface signals to its respective class object 
  // ===========================================================================================================
  task automatic align_aw_w_channel();
    int time2resp=0;
    s_axi_attr struct_attr;
    aw_channel_obj #(.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),.AXI_ID_WIDTH(AXI_ID_WIDTH)) h_aw_channel;
    w_channel_obj  #(.AXI_DATA_WIDTH(AXI_DATA_WIDTH))                             h_w_channel ;
    b_channel_obj  #(.AXI_ID_WIDTH(AXI_ID_WIDTH))                                 h_b_channel ;
    real wr_tp=0, raw_wr_tp=0;
    bit[(512-1):0] w_index,b_index,unique_id;
    forever begin //{ 
      @(posedge aclk);
      h_aw_channel = new();
      h_w_channel  = new();
      h_b_channel  = new();
      
      if((aw_channel_q.size > 0) && (w_channel_q.size > 0) && (b_channel_q.size > 0)) begin //{
        h_b_channel = b_channel_q.pop_front();
        if(w_channel_q.size > 0) begin //{
          b_index = 0;
          while ((h_b_channel.bid != aw_channel_q[b_index].awid)) begin //{
            b_index++;
            wait (aw_channel_q.size > b_index);
          end //}
          h_w_channel = w_channel_q[b_index];
          h_aw_channel = aw_channel_q[b_index];
          time2resp = int'((h_b_channel.txn_req_end_time - h_w_channel.txn_req_end_time)/CLK_PERIOD_IN_NS);
          wr_tp = ((h_w_channel.wr_beat_count * 100.0)/(h_w_channel.wr_beat_count + h_w_channel.zero_wstrb + h_w_channel.wr_stall_slv));
          raw_wr_tp = ((h_w_channel.wr_beat_count * 100.0)/(h_w_channel.wr_beat_count + h_w_channel.zero_wstrb + h_w_channel.wr_stall_slv + h_w_channel.wr_stall_mst + h_b_channel.b_stall_mst + h_b_channel.b_stall_slv));
          struct_attr.txn_id = h_b_channel.bid;
          struct_attr.s_awlen = h_aw_channel.awlen;
          struct_attr.s_awsize = h_aw_channel.awsize;
          struct_attr.s_awburst = h_aw_channel.awburst;
          struct_attr.throughput_in = wr_tp;
          struct_attr.resp_latency_in = time2resp;
          print_txns(/*IS_WRITE*/ 1, struct_attr);
        end  //}
        w_channel_q.delete(b_index);
        aw_channel_q.delete(b_index);
        //TODO: Update the total write bytes transferred
        total_wr_bytes += (h_w_channel.wr_beat_count * (2 ** h_aw_channel.awsize)); // Multiply by data size
        total_wr_time_sec += wr_txn_count * clk_period_in_sec;
        total_wr_bandwidth += ((total_wr_bytes) / total_wr_time_sec) / (1024 * 1024); // Bandwidth in MB/s
        wr_txn_count++;
        //if(aw_channel_q.size == 0 && w_channel_q.size == 0 && b_channel_q.size == 0 && !awvalid  && !wvalid && !bvalid && !arvalid && !rvalid) begin //{
        //  $display("Current Total WR Bytes: %0.2f, Total Time (s): %0.2f", total_wr_bytes, total_wr_time_sec);
        //  $display("Current Total Bandwidth (WR) in MB/s: %0.2f", total_wr_bandwidth);
        //  $fwrite(fid1,"\n-------END OF ALL WR TXNS-------");
        //end //}
       end //}
       
    end //}
  endtask: align_aw_w_channel
  // ===========================================================================================================
  // Task to forward the AR Channel interface signals to its respective class object 
  // ===========================================================================================================
  task automatic fwd_ar_txns();
    ar_channel_obj #(.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),.AXI_ID_WIDTH(AXI_ID_WIDTH)) ar_obj_h;
    string key;
    forever begin
      @(posedge aclk);
      if (arvalid && arready) begin
        ar_obj_h = new();
        ar_obj_h.araddr = araddr;    
        ar_obj_h.arburst = arburst;   
        ar_obj_h.arsize = arsize;      
        ar_obj_h.arcache = arcache;     
        ar_obj_h.arid = arid;        
        ar_obj_h.arlen = arlen;       
        ar_obj_h.arlock = arlock;        
        ar_obj_h.arprot = arprot;        
        ar_obj_h.num_bytes = 2 ** arsize;
        ar_obj_h.burst_len = arlen + 1;
        ar_obj_h.total_bytes_req = ((2 ** arsize) * (arlen + 1));
        ar_obj_h.txn_req_start_time = $realtime - CLK_PERIOD_IN_NS;
        ar_obj_h.txn_id = ar_txn_id_counter++;
        key = $sformatf("%0d:%0d", arid, ar_obj_h.txn_id);// Generate unique transaction ID
        ar_channel_dict[key] = ar_obj_h;
        ar_channel_q.push_back(ar_obj_h);
      end
      else if (arvalid && !arready) begin
        ar_obj_h.ar_stall_slv = ar_obj_h.ar_stall_slv + 1;
      end
    end
  endtask : fwd_ar_txns
  // ===========================================================================================================
  // Task to forward the R Channel interface signals to its respective class object 
  // ===========================================================================================================
  task automatic fwd_r_txns();
    string key;
    r_channel_obj #(.AXI_ID_WIDTH(AXI_ID_WIDTH),.AXI_DATA_WIDTH(AXI_DATA_WIDTH)) r_obj_h;

    forever begin
      @(posedge aclk);
      if (rvalid && rready) begin
        // create unique txn_id 
        key = $sformatf("%0d:%0d", rid, r_txn_id_counter);
        if (r_channel_dict.exists(key)) begin
          r_obj_h = r_channel_dict[key];
        end 
        else begin
          r_obj_h = new();
          r_obj_h.rid = rid;
          r_obj_h.txn_req_start_time = $realtime - CLK_PERIOD_IN_NS;
          r_channel_dict[key] = r_obj_h;
        end
        r_obj_h.rd_beat_count = r_obj_h.rd_beat_count + 1;
        r_obj_h.rdata.push_back(rdata);
        if (rlast) begin
          r_obj_h.txn_id = r_txn_id_counter++; // Store txn_id
          r_obj_h.txn_req_end_time = $realtime - CLK_PERIOD_IN_NS; //TODO: subtract with CLK_PERIOD_IN_NS param
          r_obj_h.rresp = rresp;
          r_channel_q.push_back(r_obj_h);
          r_channel_dict.delete(key); // Remove from dictionary after processing
        end
      end
      else if (rvalid && !rready) begin
        if (r_channel_dict.exists(key)) begin
          r_obj_h = r_channel_dict[key];
          r_obj_h.rd_stall_mst += 1;
        end
      end
      else if (!rvalid && rready) begin
        if (r_channel_dict.exists(key)) begin
          r_obj_h = r_channel_dict[key];
          r_obj_h.rd_stall_slv += 1;
        end
      end
    end
  endtask : fwd_r_txns
  // ===========================================================================================================
  // Task to align AR, R Channel interface signals to its respective class object 
  // ===========================================================================================================
  task automatic align_ar_r_channel();
    string key;
    real rd_tp = 0;
    int time2resp=0;
    ar_channel_obj #(.AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),.AXI_ID_WIDTH(AXI_ID_WIDTH)) h_ar_channel;
    r_channel_obj  #(.AXI_ID_WIDTH(AXI_ID_WIDTH),.AXI_DATA_WIDTH(AXI_DATA_WIDTH)) h_r_channel;
    s_axi_attr struct_attr;
    forever begin
      @(posedge aclk);
      if ((ar_channel_q.size > 0) && (r_channel_q.size > 0)) begin
        h_ar_channel = ar_channel_q.pop_front();
        key = $sformatf("%0d:%0d", h_ar_channel.arid, h_ar_channel.txn_id);
  
        foreach (r_channel_q[i]) begin
          if ((h_ar_channel.arid == r_channel_q[i].rid) && (h_ar_channel.txn_id == r_channel_q[i].txn_id)) begin
            h_r_channel = r_channel_q[i];
            time2resp = int'((h_r_channel.txn_req_start_time - h_ar_channel.txn_req_start_time)/CLK_PERIOD_IN_NS);
            rd_tp = ((h_r_channel.rd_beat_count * 100.0) / (h_r_channel.rd_beat_count + h_r_channel.rd_stall_mst));
            struct_attr.txn_id = h_r_channel.rid;
            struct_attr.s_arlen = h_ar_channel.arlen;
            struct_attr.s_arsize = h_ar_channel.arsize;
            struct_attr.s_arburst = h_ar_channel.arburst;
            struct_attr.throughput_in = rd_tp;
            struct_attr.resp_latency_in = time2resp;
            print_txns(/*IS_WRITE*/ 0, struct_attr);
            r_channel_q.delete(i); // Remove the matched entry from the queue
            // Update the total read bytes transferred
            total_rd_bytes += (h_r_channel.rd_beat_count * (2 ** h_ar_channel.arsize)); // Multiply by data size
            total_rd_time_sec += rd_txn_count * clk_period_in_sec;
            total_rd_bandwidth += ((total_rd_bytes) / total_rd_time_sec) / (1024 * 1024); // Bandwidth in MB/s
            
            //TODO: Update the total read bytes transferred
            //if(ar_channel_q.size == 0 && r_channel_q.size == 0) begin //{
            //  $display("Current Total RD Bytes: %0.2f, Total Time (s): %0.6f", total_rd_bytes, total_rd_time_sec);
            //  $display("Current Total Bandwidth (RD) in MB/s: %0.2f", total_rd_bandwidth);
            //  $fwrite(fid2,"\n-------END OF ALL RD TXNS-------");
            //break; 
            //end
          end
        end
        //TODO: Check reordering
        //ar_channel_array[h_ar_channel.arid] = h_ar_channel;
        //r_channel_array[h_ar_channel.arid] = h_r_channel;
        rd_txn_count++;
      end
    end
  endtask : align_ar_r_channel
  // ===========================================================================================================
  // Task to print throughput and txn_id to plot the performance graphs 
  // ===========================================================================================================
  function void print_txns(input bit is_wr, s_axi_attr struct_attr); 
      if(is_wr)
        $fwrite(fid1,"\n%0d,0x%h,%0.2f%%,%d,%d,%d,%d", $time, struct_attr.txn_id, struct_attr.throughput_in, struct_attr.resp_latency_in, struct_attr.s_awlen, struct_attr.s_awsize, struct_attr.s_awburst);
      else
        $fwrite(fid2,"\n%0d,0x%h,%0.2f%%,%d,%d,%d,%d", $time, struct_attr.txn_id, struct_attr.throughput_in, struct_attr.resp_latency_in, struct_attr.s_arlen, struct_attr.s_arsize, struct_attr.s_arburst);
  endfunction : print_txns

endmodule : axi_tracker

`endif //__AXI_TRACKER_DEFINE__
