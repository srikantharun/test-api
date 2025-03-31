//------------------------------------------------------------------------
//--
// ------------------------------------------------------------------------------
// 
// Copyright 2001 - 2023 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DW_axi
// Component Version: 4.06a
// Release Type     : GA
// Build ID         : 18.26.9.4
// ------------------------------------------------------------------------------

// 
// Release version :  4.06a
// File Version     :        $Revision: #13 $ 
// Revision: $Id: //dwh/DW_ocb/DW_axi/axi_dev_br/sim/testbench/sim_svte/tb_test_tasks.sv#13 $ 
//------------------------------------------------------------------------

`ifndef TB_TEST_TASKS_V
`define TB_TEST_TASKS_V

`define NUM_WR_XACTS 50
`define NUM_RD_XACTS 50
`define NUM_XACTS (`NUM_WR_XACTS + `NUM_RD_XACTS)

/** Single master Single slave traffic */
/**
  * From a randomly selected master to random selected slave:
  * A defined number of random read and write transactions are
  * initiated.  At any point of time, a single master will be
  * initiated traffic towards a single slave.
  *
  * In a seperate task wait for the same number of pre-defined
  * transactions to be completed.
  */
task automatic single_master_single_slave_test;
integer         handle[`NUM_XACTS];
integer         xfer_count_wr,xfer_count_rd;
integer         xfer_count, xact_type;
integer         mas_wr_xfer_cnt,mas_rd_xfer_cnt;
integer         callback_handle_wr,callback_handle_rd;
reg             is_valid_wr,is_valid_rd,is_valid;
integer         master_id,slave_id;
begin
  $display("\n ************** Begin Single Master Single Slave Tests ...  *************\n");
  master_id = ({$random(seed)} % `AXI_NUM_MASTERS) + 1;
  slave_id = ({$random(seed)} % `AXI_NUM_SLAVES) + 1;
  while (visible_slaves[master_id][slave_id] != 1)
  begin
    master_id = ({$random()} % `AXI_NUM_MASTERS) + 1;
    slave_id = ({$random()} % `AXI_NUM_SLAVES) + 1;
  end
  $display("\n@%0d [TB_INFO] {%m} : Selected Master ID is %0d, Slave ID is %0d\n",$time,master_id,slave_id);
  fork 
  begin
    /** Initiate a Read/Write transactions */
    xfer_count_wr = `NUM_WR_XACTS;
    xfer_count_rd = `NUM_RD_XACTS;
    for (xfer_count=0; xfer_count<`NUM_XACTS; xfer_count++) begin
      if (xfer_count_wr && xfer_count_rd) begin
        `TOP.axi_master_rand_xact(master_id,slave_id,0,`SIM_RW_RND,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,0,handle[xfer_count]);
        `GET_DATA_PROP_W_CHECK("master",master_id,handle[xfer_count],"xact_type",xact_type,0,is_valid)
        `TOP.axi_master_apply_wait_for_consumed(master_id,handle[xfer_count]);

        if (xact_type)  xfer_count_wr--;
        else            xfer_count_rd--;
      end
      else if (xfer_count_wr) begin
        `TOP.axi_master_rand_xact(master_id,slave_id,0,`SIM_WRITE,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,0,handle[xfer_count]);
        `TOP.axi_master_apply_wait_for_consumed(master_id,handle[xfer_count]);
        xfer_count_wr--;
      end
      else if (xfer_count_rd) begin
        `TOP.axi_master_rand_xact(master_id,slave_id,0,`SIM_READ,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,0,handle[xfer_count]);
        `TOP.axi_master_apply_wait_for_consumed(master_id,handle[xfer_count]);
        xfer_count_rd--;
      end
    end  
  end
  begin
    /** Test Shutdown thread for Write transactions */
    is_valid_wr = 0;
    callback_handle_wr = `SVT_CMD_NULL_HANDLE;
    mas_wr_xfer_cnt = 0;
    while(callback_handle_wr != `SVT_CMD_RESET_HANDLE) begin
      if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED\n",$time);
      `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
      `TOP.check_for_1(is_valid_wr, "master wait for ending write transfer", `ERROR_SEV);

      mas_wr_xfer_cnt++;

      `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
      `TOP.check_for_1(is_valid_wr, "vip_callback_proceed :: master wait for starting write transfer", `ERROR_SEV);

      if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) write transaction completed from Master \n",$time,mas_wr_xfer_cnt);
      if(mas_wr_xfer_cnt == `NUM_WR_XACTS) begin
        $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last transaction completed from master write transfer (%0d)\n",$time,mas_wr_xfer_cnt);
        break; 
      end 
    end 
  end 
  begin
    /** Test Shutdown thread for Read */
    is_valid_rd = 0;
    callback_handle_rd = `SVT_CMD_NULL_HANDLE;
    mas_rd_xfer_cnt = 0;
    while(callback_handle_rd != `SVT_CMD_RESET_HANDLE) begin
      if (test_debug)  $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED\n", $time);
      `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
      `TOP.check_for_1(is_valid_rd, "master wait for ending read transfer", `ERROR_SEV);

      `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
      `TOP.check_for_1(is_valid_rd, "vip_callback_proceed :: master wait for starting read transfer", `ERROR_SEV);

      if (`TOP.rlast_m_tb[master_id]) begin
        mas_rd_xfer_cnt++;
        if (test_debug)  $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) read transaction completed from Master \n",$time,mas_rd_xfer_cnt);
      end

      if(mas_rd_xfer_cnt == `NUM_RD_XACTS) begin
        $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last transaction completed from master read transfer (%0d)\n",$time,mas_rd_xfer_cnt);
        break; 
      end 
    end 
  end 
  join
  $display("\n ************** End Single Master Single Slave Tests ...  *************\n");
end
endtask

`define TB_WAIT_FOR_WRITE_COMPLETION(master_id) \
begin \
  is_valid_wr[master_id] = 0; \
  callback_handle_wr[master_id] = `SVT_CMD_NULL_HANDLE; \
  mas_wr_xfer_cnt[master_id] = 0; \
  while (callback_handle_wr[master_id] != `SVT_CMD_RESET_HANDLE) begin \
    if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED) for MasterID=%0d \n", $time,master_id); \
    `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr[master_id], is_valid_wr[master_id]); \
    `TOP.check_for_1(is_valid_wr[master_id], "master wait for ending transfer", `ERROR_SEV); \
    mas_wr_xfer_cnt[master_id]++; \
    `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr[master_id], is_valid_wr[master_id]); \
    `TOP.check_for_1(is_valid_wr[master_id], "vip_callback_proceed :: master wait for starting transfer", `ERROR_SEV); \
    if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) write transaction completed from MasterID=%0d \n",$time,mas_wr_xfer_cnt[master_id],master_id); \
    if(mas_wr_xfer_cnt[master_id] == xfer_cnt[master_id] ) begin \
      $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last write transaction completed from MasterID=%0d for transfer (%0d)\n",$time,master_id,mas_wr_xfer_cnt[master_id]); \
      break; \
    end \
  end \
end  

`define TB_WAIT_FOR_READ_COMPLETION(master_id) \
begin \
  is_valid_rd[master_id] = 0; \
  callback_handle_rd[master_id] = `SVT_CMD_NULL_HANDLE; \
  mas_rd_xfer_cnt[master_id] = 0; \
  while (callback_handle_rd[master_id] != `SVT_CMD_RESET_HANDLE) begin \
    if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED for MasterID=%0d \n", $time,master_id); \
    `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd[master_id], is_valid_rd[master_id]); \
    `TOP.check_for_1(is_valid_rd[master_id], "master wait for ending transfer", `ERROR_SEV); \
    `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd[master_id], is_valid_rd[master_id]); \
    `TOP.check_for_1(is_valid_rd[master_id], "vip_callback_proceed :: master wait for starting transfer", `ERROR_SEV); \
    if (`TOP.rlast_m_tb[master_id]) begin \
      mas_rd_xfer_cnt[master_id]++; \
      if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) read transaction completed from MasterID=%0d \n",$time,mas_rd_xfer_cnt[master_id],master_id); \
    end \
    if(mas_rd_xfer_cnt[master_id] == xfer_cnt[master_id] ) begin \
      $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last read transaction completed from MasterID=%0d for transfer (%0d)\n",$time,master_id,mas_rd_xfer_cnt[master_id]); \
      break; \
    end \
  end \
end  

/** Multi Master Multi Slave Traffic */
/** 
  * In this task from every master traffic attempts to generate traffic towards
  * every slave.
  * 
  * Before initiating transactions, make sure that Slave is visible to the
  * master.  If Slave is visible, then make sure to generate transactions to all
  * the regions that are present in that Slave.  This combination is repeated for
  * write and read transactions.
  * 
  * In a seperate thread, wait for all the initiated transactions to be completed.
  */
task automatic multi_master_multi_slave_test;
integer         handle[`AXI_NUM_MASTERS:0][`AXI_NUM_SLAVES:0][8:0][1:0];
integer         xfer_cnt[`AXI_NUM_MASTERS:0];
integer         mas_wr_xfer_cnt[`AXI_NUM_MASTERS:0],mas_rd_xfer_cnt[`AXI_NUM_MASTERS:0];
integer         callback_handle_wr[`AXI_NUM_MASTERS:0],callback_handle_rd[`AXI_NUM_MASTERS:0];
reg             is_valid_wr[`AXI_NUM_MASTERS:0],is_valid_rd[`AXI_NUM_MASTERS:0];
integer         i,j,k;
integer         mst_visibility[`AXI_NUM_MASTERS:0];
begin
  $display("\n ************** Begin Multi Master Multi Slave Tests ...  *************\n");
  /** Calculate number of transactions that will be initiated */
  for (i=1;i<=`AXI_NUM_MASTERS;i++) begin
    xfer_cnt[i] = 0;  
    mst_visibility[i]=0;
    for (j=1;j<=`AXI_NUM_SLAVES;j++) begin
      if(visible_slaves[i][j]) begin 
        mst_visibility[i]=1;
        xfer_cnt[i] = xfer_cnt[i] + slv_num_regions[j];
      end  
    end
  end    

  fork 
  begin
    for (i=1;i<=`AXI_NUM_MASTERS;i++)  // For all Masters
    begin    
      for (j=1;j<=`AXI_NUM_SLAVES;j++) // For all Slaves
      begin
        if(visible_slaves[i][j]) 
        begin    
          for (k=0;k<slv_num_regions[j];k++) // For all Regions in every Slave
          begin    
            /** Initiate transactions */
            `TOP.axi_master_rand_xact(i,j,k,`SIM_WRITE,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,0,handle[i][j][k][0]);
            `TOP.axi_master_apply_wait_for_consumed(i,handle[i][j][k][0]);
            `TOP.axi_master_rand_xact(i,j,k,`SIM_READ,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,0,handle[i][j][k][1]);
            `TOP.axi_master_apply_wait_for_consumed(i,handle[i][j][k][1]);
          end  // End for all Regions
        end
      end  // End for all Slaves
    end  // End for all Masters
  end
  `ifdef AXI_HAS_M1
    begin
      if (mst_visibility[1])  
        `TB_WAIT_FOR_WRITE_COMPLETION (1)
    end  
  `endif
  `ifdef AXI_HAS_M2
    begin
      if (mst_visibility[2])
        `TB_WAIT_FOR_WRITE_COMPLETION (2)
    end  
  `endif
  `ifdef AXI_HAS_M3
    begin
      if (mst_visibility[3])  
      `TB_WAIT_FOR_WRITE_COMPLETION (3)
    end  
  `endif
  `ifdef AXI_HAS_M4
    begin
      if (mst_visibility[4])  
      `TB_WAIT_FOR_WRITE_COMPLETION (4)
    end  
  `endif
  `ifdef AXI_HAS_M5
    begin
      if (mst_visibility[5])  
      `TB_WAIT_FOR_WRITE_COMPLETION (5)
    end  
  `endif
  `ifdef AXI_HAS_M6
    begin
      if (mst_visibility[6])  
      `TB_WAIT_FOR_WRITE_COMPLETION (6)
    end  
  `endif
  `ifdef AXI_HAS_M7
    begin
      if (mst_visibility[7])  
      `TB_WAIT_FOR_WRITE_COMPLETION (7)
    end  
  `endif
  `ifdef AXI_HAS_M8
    begin
      if (mst_visibility[8])  
      `TB_WAIT_FOR_WRITE_COMPLETION (8)
    end  
  `endif
  `ifdef AXI_HAS_M9
    begin
      if (mst_visibility[9]) 
        `TB_WAIT_FOR_WRITE_COMPLETION (9)
    end  
  `endif
  `ifdef AXI_HAS_M10
    begin
      if (mst_visibility[10])  
      `TB_WAIT_FOR_WRITE_COMPLETION (10)
    end  
  `endif
  `ifdef AXI_HAS_M11
    begin
      if (mst_visibility[11])  
      `TB_WAIT_FOR_WRITE_COMPLETION (11)
    end  
  `endif
  `ifdef AXI_HAS_M12
    begin
      if (mst_visibility[12])  
      `TB_WAIT_FOR_WRITE_COMPLETION (12)
    end  
  `endif
  `ifdef AXI_HAS_M13
    begin
      if (mst_visibility[13])  
      `TB_WAIT_FOR_WRITE_COMPLETION (13)
    end  
  `endif
  `ifdef AXI_HAS_M14
    begin
      if (mst_visibility[14])  
      `TB_WAIT_FOR_WRITE_COMPLETION (14)
    end  
  `endif
  `ifdef AXI_HAS_M15
    begin
      if (mst_visibility[15])  
      `TB_WAIT_FOR_WRITE_COMPLETION (15)
    end  
  `endif
  `ifdef AXI_HAS_M16
    begin
      if (mst_visibility[16])  
      `TB_WAIT_FOR_WRITE_COMPLETION (16)
    end  
  `endif
  `ifdef AXI_HAS_M1
    begin
      if (mst_visibility[1])  
      `TB_WAIT_FOR_READ_COMPLETION (1)
    end  
  `endif
  `ifdef AXI_HAS_M2
    begin
      if (mst_visibility[2])
        `TB_WAIT_FOR_READ_COMPLETION (2)
    end  
  `endif
  `ifdef AXI_HAS_M3
    begin
      if (mst_visibility[3])  
      `TB_WAIT_FOR_READ_COMPLETION (3)
    end  
  `endif
  `ifdef AXI_HAS_M4
    begin
      if (mst_visibility[4])  
      `TB_WAIT_FOR_READ_COMPLETION (4)
    end  
  `endif
  `ifdef AXI_HAS_M5
    begin
      if (mst_visibility[5])  
      `TB_WAIT_FOR_READ_COMPLETION (5)
    end  
  `endif
  `ifdef AXI_HAS_M6
    begin
      if (mst_visibility[6])  
      `TB_WAIT_FOR_READ_COMPLETION (6)
    end  
  `endif
  `ifdef AXI_HAS_M7
    begin
      if (mst_visibility[7])  
      `TB_WAIT_FOR_READ_COMPLETION (7)
    end  
  `endif
  `ifdef AXI_HAS_M8
    begin
      if (mst_visibility[8])  
      `TB_WAIT_FOR_READ_COMPLETION (8)
    end  
  `endif
  `ifdef AXI_HAS_M9
    begin
      if (mst_visibility[9])  
       `TB_WAIT_FOR_READ_COMPLETION (9)
    end  
  `endif
  `ifdef AXI_HAS_M10
    begin
      if (mst_visibility[10])  
      `TB_WAIT_FOR_READ_COMPLETION (10)
    end  
  `endif
  `ifdef AXI_HAS_M11
    begin
      if (mst_visibility[11])  
      `TB_WAIT_FOR_READ_COMPLETION (11)
    end  
  `endif
  `ifdef AXI_HAS_M12
    begin
      if (mst_visibility[12])  
      `TB_WAIT_FOR_READ_COMPLETION (12)
    end  
  `endif
  `ifdef AXI_HAS_M13
    begin
      if (mst_visibility[13])  
      `TB_WAIT_FOR_READ_COMPLETION (13)
    end  
  `endif
  `ifdef AXI_HAS_M14
    begin
      if (mst_visibility[14])  
      `TB_WAIT_FOR_READ_COMPLETION (14)
    end  
  `endif
  `ifdef AXI_HAS_M15
    begin
      if (mst_visibility[15])  
      `TB_WAIT_FOR_READ_COMPLETION (15)
    end  
  `endif
  `ifdef AXI_HAS_M16
    begin
      if (mst_visibility[16])  
      `TB_WAIT_FOR_READ_COMPLETION (16)
    end  
  `endif
  join
  $display("\n ************** End Multi Master Multi Slave Tests ...  *************\n");
end
endtask

/** QoS Arbitration for STAR P80002107-3497 */
task automatic test_qos_arbitration;
integer         handle[`AXI_NUM_MASTERS:0][`AXI_NUM_SLAVES:0][9:0];
integer         xfer_cnt[`AXI_NUM_MASTERS:0];
integer         mas_wr_xfer_cnt[`AXI_NUM_MASTERS:0],mas_rd_xfer_cnt[`AXI_NUM_MASTERS:0];
integer         callback_handle_wr[`AXI_NUM_MASTERS:0],callback_handle_rd[`AXI_NUM_MASTERS:0];
reg             is_valid_wr[`AXI_NUM_MASTERS:0],is_valid_rd[`AXI_NUM_MASTERS:0];
integer         i,j,k;
integer         mst_visibility[`AXI_NUM_MASTERS:0];
begin
  $display("\n <1> ************** Begin QOS Arbitration Tests ...  *************\n");
  /** Calculate number of transactions that will be initiated */
  for (i=1;i<=`AXI_NUM_MASTERS;i++) begin
    xfer_cnt[i] = 0;  
    mst_visibility[i]=0;
    for (j=1;j<=`AXI_NUM_SLAVES;j++) begin
      if(visible_slaves[i][j]) begin 
        mst_visibility[i]=1;
        xfer_cnt[i] = xfer_cnt[i] + 5;
      end  
    end
  end    

  fork 
  begin
    for (i=1;i<=`AXI_NUM_MASTERS;i++)  // For all Masters
    begin    
      for (j=1;j<=`AXI_NUM_SLAVES;j++) // For all Slaves
      begin
        if(visible_slaves[i][j]) 
        begin    
          /** Initiate transactions */
          for (k=0;k<=4;k++) begin// 5 Transactions
          `TOP.axi_master_rand_xact(i,j,0,`SIM_WRITE,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,0,handle[i][j][(k*2)]);
          `TOP.axi_master_apply_wait_for_consumed(i,handle[i][j][(k*2)]);
          `TOP.axi_master_rand_xact(i,j,0,`SIM_READ,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,0,handle[i][j][(k*2)+1]);
          `TOP.axi_master_apply_wait_for_consumed(i,handle[i][j][(k*2)+1]);
	  end
        end
      end  // End for all Slaves
    end  // End for all Masters
  end
  `ifdef AXI_HAS_M1
    begin
      if (mst_visibility[1])  
        `TB_WAIT_FOR_WRITE_COMPLETION (1)
    end  
  `endif
  `ifdef AXI_HAS_M2
    begin
      if (mst_visibility[2])
        `TB_WAIT_FOR_WRITE_COMPLETION (2)
    end  
  `endif
  `ifdef AXI_HAS_M3
    begin
      if (mst_visibility[3])  
      `TB_WAIT_FOR_WRITE_COMPLETION (3)
    end  
  `endif
  `ifdef AXI_HAS_M4
    begin
      if (mst_visibility[4])  
      `TB_WAIT_FOR_WRITE_COMPLETION (4)
    end  
  `endif
  `ifdef AXI_HAS_M5
    begin
      if (mst_visibility[5])  
      `TB_WAIT_FOR_WRITE_COMPLETION (5)
    end  
  `endif
  `ifdef AXI_HAS_M6
    begin
      if (mst_visibility[6])  
      `TB_WAIT_FOR_WRITE_COMPLETION (6)
    end  
  `endif
  `ifdef AXI_HAS_M7
    begin
      if (mst_visibility[7])  
      `TB_WAIT_FOR_WRITE_COMPLETION (7)
    end  
  `endif
  `ifdef AXI_HAS_M8
    begin
      if (mst_visibility[8])  
      `TB_WAIT_FOR_WRITE_COMPLETION (8)
    end  
  `endif
  `ifdef AXI_HAS_M9
    begin
      if (mst_visibility[9]) 
        `TB_WAIT_FOR_WRITE_COMPLETION (9)
    end  
  `endif
  `ifdef AXI_HAS_M10
    begin
      if (mst_visibility[10])  
      `TB_WAIT_FOR_WRITE_COMPLETION (10)
    end  
  `endif
  `ifdef AXI_HAS_M11
    begin
      if (mst_visibility[11])  
      `TB_WAIT_FOR_WRITE_COMPLETION (11)
    end  
  `endif
  `ifdef AXI_HAS_M12
    begin
      if (mst_visibility[12])  
      `TB_WAIT_FOR_WRITE_COMPLETION (12)
    end  
  `endif
  `ifdef AXI_HAS_M13
    begin
      if (mst_visibility[13])  
      `TB_WAIT_FOR_WRITE_COMPLETION (13)
    end  
  `endif
  `ifdef AXI_HAS_M14
    begin
      if (mst_visibility[14])  
      `TB_WAIT_FOR_WRITE_COMPLETION (14)
    end  
  `endif
  `ifdef AXI_HAS_M15
    begin
      if (mst_visibility[15])  
      `TB_WAIT_FOR_WRITE_COMPLETION (15)
    end  
  `endif
  `ifdef AXI_HAS_M16
    begin
      if (mst_visibility[16])  
      `TB_WAIT_FOR_WRITE_COMPLETION (16)
    end  
  `endif
  `ifdef AXI_HAS_M1
    begin
      if (mst_visibility[1])  
      `TB_WAIT_FOR_READ_COMPLETION (1)
    end  
  `endif
  `ifdef AXI_HAS_M2
    begin
      if (mst_visibility[2])
        `TB_WAIT_FOR_READ_COMPLETION (2)
    end  
  `endif
  `ifdef AXI_HAS_M3
    begin
      if (mst_visibility[3])  
      `TB_WAIT_FOR_READ_COMPLETION (3)
    end  
  `endif
  `ifdef AXI_HAS_M4
    begin
      if (mst_visibility[4])  
      `TB_WAIT_FOR_READ_COMPLETION (4)
    end  
  `endif
  `ifdef AXI_HAS_M5
    begin
      if (mst_visibility[5])  
      `TB_WAIT_FOR_READ_COMPLETION (5)
    end  
  `endif
  `ifdef AXI_HAS_M6
    begin
      if (mst_visibility[6])  
      `TB_WAIT_FOR_READ_COMPLETION (6)
    end  
  `endif
  `ifdef AXI_HAS_M7
    begin
      if (mst_visibility[7])  
      `TB_WAIT_FOR_READ_COMPLETION (7)
    end  
  `endif
  `ifdef AXI_HAS_M8
    begin
      if (mst_visibility[8])  
      `TB_WAIT_FOR_READ_COMPLETION (8)
    end  
  `endif
  `ifdef AXI_HAS_M9
    begin
      if (mst_visibility[9])  
       `TB_WAIT_FOR_READ_COMPLETION (9)
    end  
  `endif
  `ifdef AXI_HAS_M10
    begin
      if (mst_visibility[10])  
      `TB_WAIT_FOR_READ_COMPLETION (10)
    end  
  `endif
  `ifdef AXI_HAS_M11
    begin
      if (mst_visibility[11])  
      `TB_WAIT_FOR_READ_COMPLETION (11)
    end  
  `endif
  `ifdef AXI_HAS_M12
    begin
      if (mst_visibility[12])  
      `TB_WAIT_FOR_READ_COMPLETION (12)
    end  
  `endif
  `ifdef AXI_HAS_M13
    begin
      if (mst_visibility[13])  
      `TB_WAIT_FOR_READ_COMPLETION (13)
    end  
  `endif
  `ifdef AXI_HAS_M14
    begin
      if (mst_visibility[14])  
      `TB_WAIT_FOR_READ_COMPLETION (14)
    end  
  `endif
  `ifdef AXI_HAS_M15
    begin
      if (mst_visibility[15])  
      `TB_WAIT_FOR_READ_COMPLETION (15)
    end  
  `endif
  `ifdef AXI_HAS_M16
    begin
      if (mst_visibility[16])  
      `TB_WAIT_FOR_READ_COMPLETION (16)
    end  
  `endif
  join
  $display("\n ************** End QOS Arbitration Tests ...  *************\n");
end
endtask : test_qos_arbitration

/** 
  * This test serve two purpose, based on the input argument (test_option)
  * passed to it.
  * 
  * test_option == 1:
  * Test for default slave test. Address a non-existent slave
  * and make sure dec err response is generated, and that is
  * done by default slave.
  * 
  * test_option == 2:
  * Make sure to generate traffic in such a way that address are 
  * always unaligned.  Traffic is towards active slave.
  *
  */
`define NUM_OF_XACTS 8
task automatic default_slave_unaligned_addr_test;
input   [1:0]   test_option;
integer         master_id, slave_id;
integer         handle[`NUM_OF_XACTS:0][1:0], bresp, rresp;
integer         callback_handle_wr,callback_handle_rd;
reg             is_valid_wr,is_valid_rd;
integer         mas_wr_xfer_cnt, mas_rd_xfer_cnt;
integer         i, r, l, m;
integer         addr_gap;

begin
  if (test_option == 1)
    $display("\n ************** Begin Default Slave Test ...  *************\n");
  if (test_option == 2) 
    $display("\n ************** Begin Unaligned Transfer Test ...  *************\n");

  // Below logic will check whether there is an empty slot in the memory map:
  
  // Check1:
  // If none of the end address is `SVT_AXI_MAX_ADDR_WIDTH{1'b1},
  // then there is empty slot in the memory address.
  for (i=1; i<= `AXI_NUM_SLAVES; i=i+1) begin
    for (r=0; r< slv_num_regions[i]; r++) begin
      if (slv_region_end_array[i][r] != {`SVT_AXI_MAX_ADDR_WIDTH{1'b1}})
        addr_gap = 1;
      else begin
        addr_gap = 0;
        break;
      end
    end
    if (!addr_gap)
      break;
  end
  
  // Check2:
  // If none of the start address is `SVT_AXI_MAX_ADDR_WIDTH{1'b0},
  // then there is empty slot in the memory address.
  if(!addr_gap) begin
    for (i=1; i<= `AXI_NUM_SLAVES; i=i+1) begin
      for (r=0; r< slv_num_regions[i]; r++) begin
        if (slv_region_start_array[i][r] != {`SVT_AXI_MAX_ADDR_WIDTH{1'b0}})
          addr_gap = 1;
        else begin
          addr_gap = 0;
          break;
        end
      end
      if (!addr_gap)
        break;
    end
  end
  
  // Check3:
  // For each end address of slave regions, scan through all the start
  // addresses to see if there is a start address value == end address + 1.
  // If such an end address does not exist, then there is empty slot in the memory gap.
  if(!addr_gap) begin
    for (i=1; i<= `AXI_NUM_SLAVES; i=i+1) begin
      for (r=0; r< slv_num_regions[i]; r++) begin
        if (slv_region_end_array[i][r] == {`SVT_AXI_MAX_ADDR_WIDTH{1'b1}})
          break;
        for (l=1; l<= `AXI_NUM_SLAVES; l++) begin
          for (m=0; m< slv_num_regions[l]; m++) begin
            if ((slv_region_end_array[i][r] + 1) != slv_region_start_array[l][m])
              addr_gap = 1;
            else begin 
              addr_gap = 0;
              break;
            end
          end
          if (!addr_gap)
           break;
        end 
        if (addr_gap)
          break;
      end
      if (addr_gap)
        break;
    end
  end
  
  if (test_option == 1 && addr_gap == 0)
    $display("\n ************** Skipping Default Slave Test as there is no empty slot in the memory map *************\n");
  
  else begin
    master_id = ({$random(seed)} % `AXI_NUM_MASTERS) + 1;
    $display("\n@%0d [TB_INFO] {%m} : Selected Master ID is %0d\n",$time,master_id);
    fork 
      begin
        for (i=1; i<=`NUM_OF_XACTS; i++) begin
          slave_id = ({$random(seed)} % `AXI_NUM_SLAVES) + 1;
          `TOP.axi_master_rand_xact(master_id,slave_id,0,`SIM_WRITE,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,test_option,handle[i][0]);
          `TOP.axi_master_apply_wait_for_consumed(master_id,handle[i][0]);
          `TOP.axi_master_rand_xact(master_id,slave_id,0,`SIM_READ,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_RND,test_option,handle[i][1]);
          `TOP.axi_master_apply_wait_for_consumed(master_id,handle[i][1]);
        end 
      end
      begin
        /** Test Shutdown thread for Write transactions */
        is_valid_wr = 0;
        callback_handle_wr = `SVT_CMD_NULL_HANDLE;
        mas_wr_xfer_cnt = 0;
        while(callback_handle_wr != `SVT_CMD_RESET_HANDLE) begin
          if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED\n",$time);
          `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
          `TOP.check_for_1(is_valid_wr, "master wait for ending write transfer", `ERROR_SEV);

          if (test_option == 1) begin
            `GET_DATA_PROP_W_CHECK("master",master_id,callback_handle_wr,"bresp",bresp,0,is_valid_wr)
            if (bresp != 3) $display("\n@%0d ERROR {%m} : Got BRESP=%0d, instead of DECERR(3)\n",$time,bresp);
          end

          mas_wr_xfer_cnt++;

          `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
          `TOP.check_for_1(is_valid_wr, "vip_callback_proceed :: master wait for starting write transfer", `ERROR_SEV);

          if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) write transaction completed from Master \n",$time,mas_wr_xfer_cnt);
          if(mas_wr_xfer_cnt == `NUM_OF_XACTS) begin
            $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last transaction completed from master write transfer (%0d)\n",$time,mas_wr_xfer_cnt);
            break; 
          end 
        end 
      end 
      begin
        /** Test Shutdown thread for Read transactions */
        is_valid_rd = 0;
        callback_handle_rd = `SVT_CMD_NULL_HANDLE;
        mas_rd_xfer_cnt = 0;
        while(callback_handle_rd != `SVT_CMD_RESET_HANDLE) begin
          if (test_debug)  $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED\n", $time);
          `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
          `TOP.check_for_1(is_valid_rd, "master wait for ending read transfer", `ERROR_SEV);

          if (test_option == 1) begin
            `GET_DATA_PROP_W_CHECK("master",master_id,callback_handle_rd,"rresp",rresp,0,is_valid_rd)
            if (rresp != 3) $display("\n@%0d ERROR {%m} : Got RRESP=%0d, instead of DECERR(3)\n",$time,rresp);
          end   

          `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
          `TOP.check_for_1(is_valid_rd, "vip_callback_proceed :: master wait for starting read transfer", `ERROR_SEV);

           if (`TOP.rlast_m_tb[master_id]) begin
             mas_rd_xfer_cnt++;
             if (test_debug)  $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) read transaction completed from Master \n",$time,mas_rd_xfer_cnt);
           end

          if(mas_rd_xfer_cnt == `NUM_OF_XACTS) begin
            $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last transaction completed from master read transfer (%0d)\n",$time,mas_rd_xfer_cnt);
            break; 
          end 
        end 
      end 
    join
  end
  
  if (test_option == 2)
    $display("\n ************** End Unalinged Transfer Test ...  *************\n");
  else if (test_option == 1 && addr_gap == 1)
    $display("\n ************** End Default Slave Test ...  *************\n");
end
endtask

/** Low Power interface Test **/
/** 
  * Randomly apply low powere requests and test if LP state
  * trasitions are correct no pending transcations are present 
  */
task automatic axi_low_power_test;
begin
  // Start running a few tests
  $display("\n ************** Begin Low Power Test ...  *************\n");
  fork
    begin : test_proc
      single_master_single_slave_test;
	    axi_idle = $random(seed) % 500;
	    repeat (axi_idle) @(posedge aclk);
      disable lp_proc; // Disable the low power block
      if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Disabling lp_proc DONE \n",$time);
    end
    begin : lp_proc
      while (1) begin
        repeat ({$random(seed)} % 1000) @(posedge aclk);
        #(1) csysreq = 0;
        repeat ({$random(seed)} % 100) @(posedge aclk);
        #(1) csysreq = 1;
      end
    end
  join
  /** Run one more test to ensure recovery to full power state */
  single_master_single_slave_test;
  $display("\n ************** End Low Power Test ...  *************\n");
end
endtask

/** Exclusive access Test */
task automatic exclusive_test;
  integer rd_handle[`AXI_NUM_MASTERS:0][`AXI_NUM_SLAVES:0][8:0][1:0];
  integer wr_handle[`AXI_NUM_MASTERS:0][`AXI_NUM_SLAVES:0][8:0][1:0];
  reg is_valid_wr[`AXI_NUM_MASTERS:0],is_valid_rd[`AXI_NUM_MASTERS:0];
  integer i,j,k;
  integer atomic_type,burst_length,burst_size,burst_type,prot_type,id,beat,cache_type;
  reg [63:0] wstrb,data;
  reg [`AXI_AW-1:0] addr;

  begin
    $display("\n ************** Begin Exclusive Access Tests ...  *************\n");

    for (i=1;i<=`AXI_NUM_MASTERS;i++)  // For all Masters
    begin    
      for (j=1;j<=`AXI_NUM_SLAVES;j++) // For all Slaves
      begin
        if(visible_slaves[i][j]) // Go ahead if the Slave is visible
        begin    
          k = $random(seed) % slv_num_regions[j];  // Randomly select one region in the Slave

          /** Generate exclusive READ transaction */
          if(`TOP.tz_secure_s[j] == 1)
            `TOP.axi_master_rand_xact(i,j,k,`SIM_READ,`SIM_EXCLUSIVE,`SIM_SECURE,`SIM_BURST_RND,0,rd_handle[i][j][k][0]);
          else
            `TOP.axi_master_rand_xact(i,j,k,`SIM_READ,`SIM_EXCLUSIVE,`SIM_SECURE_RND,`SIM_BURST_RND,0,rd_handle[i][j][k][0]);

          /** Get the burstlength */
          `GET_DATA_PROP_W_CHECK("master",i,rd_handle[i][j][k][0],"burst_length",burst_length,0,is_valid_rd[i])
          `GET_DATA_PROP_W_CHECK("master",i,rd_handle[i][j][k][0],"addr",addr,0,is_valid_rd[i])
          `GET_DATA_PROP_W_CHECK("master",i,rd_handle[i][j][k][0],"atomic_type",atomic_type,0,is_valid_rd[i])
          `GET_DATA_PROP_W_CHECK("master",i,rd_handle[i][j][k][0],"burst_size",burst_size,0,is_valid_rd[i])
          `GET_DATA_PROP_W_CHECK("master",i,rd_handle[i][j][k][0],"burst_type",burst_type,0,is_valid_rd[i])
          `GET_DATA_PROP_W_CHECK("master",i,rd_handle[i][j][k][0],"prot_type",prot_type,0,is_valid_rd[i])
          `GET_DATA_PROP_W_CHECK("master",i,rd_handle[i][j][k][0],"id",id,0,is_valid_rd[i])
          `GET_DATA_PROP_W_CHECK("master",i,rd_handle[i][j][k][0],"cache_type",cache_type,0,is_valid_rd[i])

          /** Apply the Exclusive Read command to VIP */
          `TOP.axi_master_apply_wait_for_consumed(i,rd_handle[i][j][k][0]);

          /** Wait for the Exclusive Read transaction to be ended */
          `TOP.vip_notify_wait_for("master",i, "monitor.NOTIFY_TX_XACT_ENDED",is_valid_rd[i]);

          /** Generate exclusive WRITE transaction */
          if(`TOP.tz_secure_s[j] == 1)
            `TOP.axi_master_rand_xact(i,j,k,`SIM_WRITE,`SIM_EXCLUSIVE,`SIM_SECURE,`SIM_BURST_RND,0,wr_handle[i][j][k][0]);
          else
            `TOP.axi_master_rand_xact(i,j,k,`SIM_WRITE,`SIM_EXCLUSIVE,`SIM_SECURE_RND,`SIM_BURST_RND,0,wr_handle[i][j][k][0]);

          /** Match the attributes to Exclusive Read */
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"burst_length",burst_length,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"addr",addr,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"atomic_type",atomic_type,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"burst_size",burst_size,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"burst_type",burst_type,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"prot_type",prot_type,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"id",id,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"cache_type",cache_type,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"wvalid_delay_size",burst_length,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"wstrb_size",burst_length,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"data_size",burst_length,0,is_valid_wr[i])
          `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"rresp_size",0,0,is_valid_wr[i])
          for (beat=0; beat<burst_length; beat++) begin 
            wstrb = (1<<(burst_size+1) - 1) & ({$random(seed),$random(seed)}); 
            `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"wstrb", wstrb, beat, is_valid_wr[i]) 
            data = (1<<(burst_size+1) - 1) & ({$random(seed),$random(seed)}); 
            `SET_DATA_PROP_W_CHECK("master",i,wr_handle[i][j][k][0],"data", data, beat, is_valid_wr[i]) 
          end 

          /** Apply the Exclusive Write command to VIP */
          `TOP.axi_master_apply_wait_for_consumed(i,wr_handle[i][j][k][0]);

          /** Wait for the Exclusive Write transaction to be ended */
          `TOP.vip_notify_wait_for("master",i, "monitor.NOTIFY_TX_XACT_ENDED",is_valid_wr[i]);
        end
      end  // End for all Slaves
      $display("\n@%0d [TB_INFO] {%m} : ********** Exclusive RD-WR completed from Master[%0d] to all visible slaves **********\n",$time,i);
    end  // End for all Masters
    $display("\n ************** End of Exclusive Access Tests ...  *************\n");
  end    
endtask

`ifdef AXI_QOS
/**
  * Randomly generate the qos regulator configuration
  * 1. Qos enable /Disable
  * 2. Slave ready dependency 
  * 3. Qos register value
  * 4. Transaction rate - 0 or 1/4 or 1/8 or 1/16
  * 5. Peak rate - 0 or 1/4 or 1/8 or 1/16
  * 6. Burstiness - 1 or 4 or 8 or 16
  */ 
task automatic randomly_gen_qos_cfg(output enable,output slv_rdy_dep,output [3:0] qos, output [15:0] xact_rate, output [15:0] peak_rate, output [7:0] burstiness);
reg [1:0] rand_sel;
begin
  enable = $random(seed); 
  slv_rdy_dep = $random(seed);
  qos = $random(seed);

  /** Randomly selects the transaction rate to 0 or 1/4 or 1/8 or 1/16 */
  rand_sel = $random(seed);
 
  `ifdef SNPS_INTERNAL_ON
  //Disable the regulator.Since our intention is to verify the arbiter,not the regulator.
  if (qos_arb_check_en) begin 
    rand_sel = 0;
    enable = 0; //disable the regulator
  end
  `endif

  case (rand_sel) 
    2'b00 : xact_rate = 16'h0;
    2'b01 : xact_rate = 16'h4000;
    2'b10 : xact_rate = 16'h2000;
    2'b11 : xact_rate = 16'h1000;
  endcase

  /** Randomly selects the peak rate to 0 or 1/4 or 1/8 or 1/16 */
  rand_sel = $random(seed);
  case (rand_sel) 
    2'b00 : peak_rate = 16'h0;
    2'b01 : peak_rate = 16'h4000;
    2'b10 : peak_rate = 16'h2000;
    2'b11 : peak_rate = 16'h1000;
  endcase

  /** Randomly selects the Burstiness to 1 or 4 or 8 or 16 */
  rand_sel = $random(seed);
  case (rand_sel) 
    2'b00 : burstiness = 8'h0;
    2'b01 : burstiness = 8'h3;
    2'b10 : burstiness = 8'h7;
    2'b11 : burstiness = 8'hf;
  endcase
end
endtask

/**
 * Programs QOS configuration into the Master registers, based on the master_num
 */
task automatic qos_programming;
  input integer master_num;
  reg [3:0] qos_value;
  reg qos_enable;
  reg slave_ready_dependency;
  reg [15:0] transaction_rate;
  reg [15:0] peak_rate;
  reg [7:0] burstiness;

  begin
    /** Generate the qos configuration for write channel */
    randomly_gen_qos_cfg(qos_enable,slave_ready_dependency,qos_value,transaction_rate,peak_rate,burstiness);
    `ifdef SNPS_INTERNAL_ON
    qos_awreg_en_from_reg_prog_m[master_num] = transaction_rate == 0 ? 0 : 1; 
    `endif
    wait (`TOP.apb_reg_prog_flag == 1'b0);
    $display("\n@%0d [TB_INFO] {%m} : Configuring QOS Write address channel regulator on Master %0d :\n",$time,master_num);
    $display("\n@%0d [TB_INFO] {%m} : Burstiness :%0h ,Transaction rate :%0h, Peak rate : %0h, Qos enable :%0h, Qos value :%0h\n",$time,burstiness,transaction_rate,peak_rate,qos_enable,qos_value);

    `TOP.apb_reg_prog_flag = 1'b1;
    program_qos_registers(master_num,1,{8'h0,burstiness,15'h0,qos_enable},{peak_rate,transaction_rate},qos_value,{31'h0,slave_ready_dependency});
    `TOP.apb_reg_prog_flag = 1'b0;
    
    /** Generate the qos configuration for read channel */
    randomly_gen_qos_cfg(qos_enable,slave_ready_dependency,qos_value,transaction_rate,peak_rate,burstiness);
    `ifdef SNPS_INTERNAL_ON
    qos_arreg_en_from_reg_prog_m[master_num] = transaction_rate == 0 ? 0 : 1;
    `endif
    wait (`TOP.apb_reg_prog_flag == 1'b0);
    $display("\n@%0d [TB_INFO] {%m} : Configuring QOS Read address channel regulator on Master %0d :\n",$time,master_num);
    $display("\n@%0d [TB_INFO] {%m} : Burstiness :%0h ,Transaction rate :%0h, Peak rate : %0h, Qos enable :%0h, Qos value :%0h\n",$time,burstiness,transaction_rate,peak_rate,qos_enable,qos_value);

    `TOP.apb_reg_prog_flag =1'b1;
    program_qos_registers(master_num,0,{8'h0,burstiness,15'h0,qos_enable},{peak_rate,transaction_rate},qos_value,{31'h0,slave_ready_dependency});
    `TOP.apb_reg_prog_flag = 1'b0;
  end
endtask
`endif //AXI_QOS

/**
  * Task used to fork-off random slave responses 
  */ 
task automatic slaves_rand_response;
  integer i;
  begin
    fork
    begin
      for (i= 1; i <= `AXI_NUM_SLAVES;i++)begin
        automatic integer k;
        k = i;
        fork        
          `TOP.axi_slave_send_rand_response(k);
        join_none
      end
    end
    join_none
  end
endtask

// ---------------------------------------------------------------------------------------------------------

`ifdef DW_AXI_TB_ENABLE_QOS_INT

task automatic test_max_id_limit (input uid_enable); 
  integer mst_wr_buffer[512:0];
  integer mst_rd_buffer[512:0];
  integer region_num;
  integer num_xact;
  integer selected_master,selected_slave;
  integer mst_wr_xact_sent,mst_rd_xact_sent;
  
  integer urid_rand_cnt,uwid_rand_cnt;
  reg run_test;

  reg [`AXI_SIDW-1:0]  awid_tb;
  reg [`AXI_SIDW-1:0]  arid_tb;
  `ifdef AXI_BICMD_SUPPORT
    reg [`AXI_SIDW-`AXI_MIDW-1:0] arid_upper;
    reg [`AXI_MIDW-1:0] arid_lower;
    reg [`AXI_SIDW-`AXI_MIDW-1:0] awid_upper;
    reg [`AXI_MIDW-1:0] awid_lower;
  `endif

  integer rcount,wcount;
  reg rd_completed, wr_completed;

  begin
    repeat(1) @(posedge aclk); 
    if(uid_enable == 0) begin
       if (test_debug) $display($time," [TB_DEBUG] - Test outstanding limit for Same Id's : Started \n");
       num_xact = 256 ;
     end 
    else if(uid_enable == 1) begin
      if (test_debug) $display($time,"[TB_DEBUG] Test Outstanding limit for Unique ID's : Started \n ");
      num_xact = 128;
    end
    run_test = 1;

    //Randomly select a Master/Slave based on visibility  
    selected_master = ({$random(seed)} % `AXI_NUM_MASTERS) + 1;
    selected_slave = ({$random (seed)} % `AXI_NUM_SLAVES) + 1;
    while (visible_slaves[selected_master][selected_slave] != 1)
    begin
      selected_master = ({$random(seed)} % `AXI_NUM_MASTERS) + 1;
      selected_slave = ({$random (seed)} % `AXI_NUM_SLAVES) + 1;
    end
    $display($time," [TB_INFO] - %m - Selected Master is %0d, Slave is %0d\n",selected_master,selected_slave);
  
    //Initialize the rd/wr num counters
    mst_wr_xact_sent = 0;
    mst_rd_xact_sent = 0; 
    rd_completed = 0;
    wr_completed = 0;

   if(run_test == 1) begin 
      if (test_debug) $display($time, " [TB_DEBUG] - %m - Configuring Slave Response, setting long_bvalid_delay(1) and long_rvalid_delay(1), so that response will be throttled by slave : Selected Slave:%0d",selected_slave);
      region_num = 0;
      // These global variable declared in test_DW_axi.v are used to program the Slave VIP delays
      long_bvalid_delay = 1;
      long_rvalid_delay = 1;
    
      // Initialize other local variables to 0
      uwid_rand_cnt = 0;
      urid_rand_cnt = 0;
      rcount = 0;
      wcount = 0;

      if (test_debug) $display($time, " [TB_DEBUG] - %m - Generating transaction From Master %0d to Slave %0d \n",selected_master, selected_slave);
      fork
        begin : wr_rd_generation_fork
          integer xfer_count;
          reg is_valid;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - In the Begining of the wr_rd_generation_fork \n");
          /** Initiate a Read/Write transactions */
          for (xfer_count=0; (xfer_count < 2*num_xact); xfer_count++) begin
            if ((xfer_count % 2) == 0) begin
              `TOP.axi_master_rand_xact(selected_master,selected_slave,region_num,`SIM_WRITE,`SIM_UNLOCK,`SIM_SECURE,`SIM_BURST_RND,0,mst_wr_buffer[xfer_count]);
              uwid_rand_cnt=uwid_rand_cnt+1;
    	        if (uwid_rand_cnt > (2**`AXI_MIDW-1 )) begin
    	          uwid_rand_cnt = 0;
              end
`ifdef AXI_BICMD_SUPPORT 
              if (selected_master <= `AXI_NUM_ICM) begin  //For ICM port, we should generate ID of width SIDW since it is ICM port
                if (wcount==0) begin
                  `GET_DATA_PROP_W_CHECK("master",selected_master,mst_wr_buffer[xfer_count], "id",awid_tb, 0,is_valid)
                  awid_upper = awid_tb[`AXI_SIDW-1:`AXI_MIDW];
                  wcount=1;
                end  
                if (uid_enable == 0)
                  awid_lower = selected_master%(1<<`AXI_MIDW);
                else
                  awid_lower = uwid_rand_cnt%(1<<`AXI_MIDW);

                awid_tb = {awid_upper,awid_lower};
              end //For System Master port, we should generate ID of width MIDW
              else begin
                if (uid_enable == 0)
                  awid_tb = selected_master%(1<<`AXI_MIDW);
                else
                  awid_tb = uwid_rand_cnt%(1<<`AXI_MIDW);
              end 
`else 
              if (uid_enable == 0)
                awid_tb = selected_master%(1<<`AXI_MIDW);
              else
                awid_tb = uwid_rand_cnt%(1<<`AXI_MIDW);
`endif
              `SET_DATA_PROP_W_CHECK("master",selected_master,mst_wr_buffer[xfer_count],"id", awid_tb, 0,is_valid)
              `TOP.axi_master_apply_wait_for_consumed(selected_master,mst_wr_buffer[xfer_count]);
    	        mst_wr_xact_sent = mst_wr_xact_sent + 1;
              if (test_debug) $display($time, " [TB_DEBUG] - %m - Generated WR_XACT with AID : %0d (mst_wr_xact_sent = %0d)\n",awid_tb, mst_wr_xact_sent);
            end 
            else begin
              `TOP.axi_master_rand_xact(selected_master,selected_slave,region_num,`SIM_READ,`SIM_UNLOCK,`SIM_SECURE,`SIM_BURST_RND,0,mst_rd_buffer[xfer_count]);
              urid_rand_cnt = urid_rand_cnt+1;
    	        if(urid_rand_cnt > (2**`AXI_MIDW-1 )) begin
    	          urid_rand_cnt = 0;
              end
`ifdef AXI_BICMD_SUPPORT 
              if (selected_master <= `AXI_NUM_ICM) begin  //For ICM port, we should generate ID of width SIDW since it is ICM port
                if (rcount==0) begin
                  `GET_DATA_PROP_W_CHECK("master",selected_master,mst_rd_buffer[xfer_count], "id",arid_tb, 0,is_valid)
                  arid_upper = arid_tb[`AXI_SIDW-1:`AXI_MIDW];
                  rcount=1;
                end  
                if (uid_enable == 0)
                  arid_lower = selected_master%(1<<`AXI_MIDW);
                else
                  arid_lower = urid_rand_cnt%(1<<`AXI_MIDW);

                arid_tb = {arid_upper,arid_lower};
              end //For System Master port, we should generate ID of width MIDW
              else begin
                if (uid_enable == 0)
                  arid_tb = selected_master%(1<<`AXI_MIDW);
                else
                  arid_tb = urid_rand_cnt%(1<<`AXI_MIDW);
              end    
`else
              if (uid_enable == 0)
                arid_tb = selected_master%(1<<`AXI_MIDW);
              else
                arid_tb = urid_rand_cnt%(1<<`AXI_MIDW);
`endif
              `SET_DATA_PROP_W_CHECK("master",selected_master,mst_rd_buffer[xfer_count],"id", arid_tb, 0,is_valid)
              `TOP.axi_master_apply_wait_for_consumed(selected_master,mst_rd_buffer[xfer_count]);
    	        mst_rd_xact_sent = mst_rd_xact_sent + 1;
              if (test_debug) $display($time, " [TB_DEBUG] - %m - Generated RD_XACT with AID : %0d (mst_rd_xact_sent = %0d)\n",arid_tb, mst_rd_xact_sent);
            end
          end  
          if (test_debug) $display($time, " [TB_DEBUG] - %m - At the End of the wr_rd_generation_fork -- mst_wr_xact_sent = %0d, mst_rd_xact_sent = %0d\n",mst_wr_xact_sent,mst_rd_xact_sent);
        end
        // ---------------------------------------------------------------------------------------------------------------------
        begin : wr_completion_fork
          reg is_valid_wr = 0;
          integer callback_handle_wr = `SVT_CMD_NULL_HANDLE;
          integer mas_wr_xfer_cnt = 0;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - In the Begining of the wr_completion_fork \n");
          while (callback_handle_wr != `SVT_CMD_RESET_HANDLE) begin
            if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED) for MasterID=%0d \n", $time,selected_master);
            `TOP.vip_callback_wait_for("master",selected_master, "monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
            `TOP.check_for_1(is_valid_wr, "master wait for ending transfer", `ERROR_SEV);
            mas_wr_xfer_cnt++;
            `TOP.vip_callback_proceed("master",selected_master,"monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
            `TOP.check_for_1(is_valid_wr, "vip_callback_proceed :: master wait for starting transfer", `ERROR_SEV);
            if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) write transaction completed from MasterID=%0d \n",$time,mas_wr_xfer_cnt,selected_master);
            if(mas_wr_xfer_cnt == num_xact ) begin
              $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last write transaction completed from MasterID=%0d for transfer (%0d)\n",$time,selected_master,mas_wr_xfer_cnt);
              break;
            end
          end
          wr_completed = 1;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - At the End of the wr_completion_fork \n");
        end : wr_completion_fork
        // ---------------------------------------------------------------------------------------------------------------------
        begin : rd_completion_fork
          reg is_valid_rd = 0;
          integer callback_handle_rd = `SVT_CMD_NULL_HANDLE;
          integer mas_rd_xfer_cnt = 0;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - In the Begining of the rd_completion_fork \n");
          while (callback_handle_rd != `SVT_CMD_RESET_HANDLE) begin
            if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED for MasterID=%0d \n", $time,selected_master);
            `TOP.vip_callback_wait_for("master",selected_master, "monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
            `TOP.check_for_1(is_valid_rd, "master wait for ending transfer", `ERROR_SEV);
            `TOP.vip_callback_proceed("master",selected_master,"monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
            `TOP.check_for_1(is_valid_rd, "vip_callback_proceed :: master wait for starting transfer", `ERROR_SEV);
            if (`TOP.rlast_m_tb[selected_master]) begin
              mas_rd_xfer_cnt++;
              if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) read transaction completed from MasterID=%0d \n",$time,mas_rd_xfer_cnt,selected_master);
            end
            if(mas_rd_xfer_cnt == num_xact ) begin
              $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last read transaction completed from MasterID=%0d for transfer (%0d)\n",$time,selected_master,mas_rd_xfer_cnt);
              break;
            end
          end
          rd_completed = 1;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - At the End of the rd_completion_fork \n");
        end : rd_completion_fork
        // ---------------------------------------------------------------------------------------------------------------------
        //begin : timer_fork
        // #500_0000;
        // $display($time, " ERROR : RWCA/UID Test TIMEOUT (Input argument uid_enable = %0d)\n",uid_enable);
        //end : timer_fork
        // ---------------------------------------------------------------------------------------------------------------------
        begin : finish_fork
         wait (wr_completed && rd_completed);
         disable wr_rd_generation_fork;
         disable wr_completion_fork;
         disable rd_completion_fork;
         //disable timer_fork;
        end : finish_fork
        // ---------------------------------------------------------------------------------------------------------------------
      join
    
      if (test_debug) $display($time, " [TB_DEBUG] - %m - test_max_rwca_limit : Complete");
      // set them back so that other tests doesn't get long delays
      long_bvalid_delay = 0;
      long_rvalid_delay = 0;
    
   end//if(run_test..
  end//begin-task
endtask  //test_max_rwca_limit

`endif

// ---------------------------------------------------------------------------------------------------------

`endif

task automatic test_max_outstanding_uid (input uid_enable); 
  integer mst_wr_buffer[2048:0];
  integer mst_rd_buffer[2048:0];
  integer region_num;

  //*Total number of request generated in test*/
  integer num_xact;

  //*Indicate master number and slave number*/
  integer selected_master,selected_slave;

  //*Counter which track current wr/rd request number*/
  integer mst_wr_xact_sent,mst_rd_xact_sent;
  
  //*Random ID for write and read transaction
  /* Value are in incrementle order in uid test case*/
  integer urid_rand_cnt,uwid_rand_cnt;

  reg run_test;

  reg [`AXI_SIDW-1:0]  awid_tb;
  reg [`AXI_SIDW-1:0]  arid_tb;
  `ifdef AXI_BICMD_SUPPORT
    reg [`AXI_SIDW-`AXI_MIDW-1:0] arid_upper;
    reg [`AXI_MIDW-1:0] arid_lower;
    reg [`AXI_SIDW-`AXI_MIDW-1:0] awid_upper;
    reg [`AXI_MIDW-1:0] awid_lower;
  `endif

  integer rcount,wcount;
  /*Variable set when all req completes and used to disable fork */
  reg rd_completed, wr_completed;

  begin
    repeat(1) @(posedge aclk); 
    if(uid_enable == 0) begin
       if (test_debug) $display($time," [TB_DEBUG] - Test outstanding limit for Same Id's : Started \n");
       num_xact = 512 ;
       rca_wca_test = 1;
     end 
    else if(uid_enable == 1) begin
      if (test_debug) $display($time,"[TB_DEBUG] Test Outstanding limit for Unique ID's : Started \n ");
      num_xact = 700;
      arida_awida_test = 1;
    end
    outstanding_check_en = 1;
    fawc_farc_test = 1;
    run_test = 1;

    //Randomly select a Master/Slave based on visibility  
    selected_master = ({$random(seed)} % `AXI_NUM_MASTERS) + 1;
    selected_slave = ({$random (seed)} % `AXI_NUM_SLAVES) + 1;
    while (visible_slaves[selected_master][selected_slave] != 1)
    begin
      selected_master = ({$random(seed)} % `AXI_NUM_MASTERS) + 1;
      selected_slave = ({$random (seed)} % `AXI_NUM_SLAVES) + 1;
    end
    $display($time," [TB_INFO] - %m - Selected Master is %0d, Slave is %0d\n",selected_master,selected_slave);
  
    //Initialize the rd/wr num counters
    mst_wr_xact_sent = 0;
    mst_rd_xact_sent = 0; 
    rd_completed = 0;
    wr_completed = 0;

   if(run_test == 1) begin 
      if (test_debug) $display($time, " [TB_DEBUG] - %m - Configuring Slave Response, setting very_long_bvalid_delay(1) and long_rvalid_delay(1), so that response will be throttled by slave : Selected Slave:%0d",selected_slave);
      region_num = 0;
      // These global variable declared in test_DW_axi.v are used to program the Slave VIP delays
      very_long_bvalid_delay = 1;
      very_long_rvalid_delay = 1;
      zero_addr_ready_delay = 1;
      zero_addr_valid_delay = 1;
      if(uid_enable == 0) begin
        bvalid_long_delay = wca_param_value[selected_master] + 10;
        rvalid_long_delay = rca_param_value[selected_master] + 10;
      end else begin
        bvalid_long_delay = uwida_param_value[selected_master] + 10;
        rvalid_long_delay = urida_param_value[selected_master] + 10;
      end
      // Initialize other local variables to 0
      uwid_rand_cnt = ({$random(seed)} % (2**`AXI_MIDW-1));
      urid_rand_cnt = ({$random(seed)} % (2**`AXI_MIDW-1));
      rcount = 0;
      wcount = 0;

      if (test_debug) $display($time, " [TB_DEBUG] - %m - Generating transaction From Master %0d to Slave %0d \n",selected_master, selected_slave);
      fork
        begin : wr_rd_generation_fork
          integer xfer_count;
          reg is_valid;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - In the Begining of the wr_rd_generation_fork \n");
          /** Initiate a Read/Write transactions */
          for (xfer_count=0; (xfer_count < 2*num_xact); xfer_count++) begin
            if ((xfer_count % 2) == 0) begin
              `TOP.axi_master_rand_xact(selected_master,selected_slave,region_num,`SIM_WRITE,`SIM_UNLOCK,`SIM_SECURE,`SIM_BURST_RND,0,mst_wr_buffer[xfer_count]);
              uwid_rand_cnt=uwid_rand_cnt+1;
    	        if (uwid_rand_cnt > (2**`AXI_MIDW-1 )) begin
    	          uwid_rand_cnt = 0;
              end
`ifdef AXI_BICMD_SUPPORT 
              if (selected_master <= `AXI_NUM_ICM) begin  //For ICM port, we should generate ID of width SIDW since it is ICM port
                if (wcount==0) begin
                  `GET_DATA_PROP_W_CHECK("master",selected_master,mst_wr_buffer[xfer_count], "id",awid_tb, 0,is_valid)
                  awid_upper = awid_tb[`AXI_SIDW-1:`AXI_MIDW];
                  wcount=1;
                end  
                if (uid_enable == 0)
                  awid_lower = selected_master%(1<<`AXI_MIDW);
                else
                  awid_lower = uwid_rand_cnt%(1<<`AXI_MIDW);

                awid_tb = {awid_upper,awid_lower};
              end //For System Master port, we should generate ID of width MIDW
              else begin
                if (uid_enable == 0)
                  awid_tb = selected_master%(1<<`AXI_MIDW);
                else
                  awid_tb = uwid_rand_cnt%(1<<`AXI_MIDW);
              end 
`else 
              if (uid_enable == 0)
                awid_tb = selected_master%(1<<`AXI_MIDW);
              else
                awid_tb = uwid_rand_cnt%(1<<`AXI_MIDW);
`endif
              `SET_DATA_PROP_W_CHECK("master",selected_master,mst_wr_buffer[xfer_count],"id", awid_tb, 0,is_valid)
              `TOP.axi_master_apply_wait_for_consumed(selected_master,mst_wr_buffer[xfer_count]);
    	        mst_wr_xact_sent = mst_wr_xact_sent + 1;
              if (test_debug) $display($time, " [TB_DEBUG] - %m - Generated WR_XACT with AID : %0d (mst_wr_xact_sent = %0d)\n",awid_tb, mst_wr_xact_sent);
            end 
            else begin
              `TOP.axi_master_rand_xact(selected_master,selected_slave,region_num,`SIM_READ,`SIM_UNLOCK,`SIM_SECURE,`SIM_BURST_RND,0,mst_rd_buffer[xfer_count]);
              urid_rand_cnt = urid_rand_cnt+1;
    	        if(urid_rand_cnt > (2**`AXI_MIDW-1 )) begin
    	          urid_rand_cnt = 0;
              end
`ifdef AXI_BICMD_SUPPORT 
              if (selected_master <= `AXI_NUM_ICM) begin  //For ICM port, we should generate ID of width SIDW since it is ICM port
                if (rcount==0) begin
                  `GET_DATA_PROP_W_CHECK("master",selected_master,mst_rd_buffer[xfer_count], "id",arid_tb, 0,is_valid)
                  arid_upper = arid_tb[`AXI_SIDW-1:`AXI_MIDW];
                  rcount=1;
                end  
                if (uid_enable == 0)
                  arid_lower = selected_master%(1<<`AXI_MIDW);
                else
                  arid_lower = urid_rand_cnt%(1<<`AXI_MIDW);

                arid_tb = {arid_upper,arid_lower};
              end //For System Master port, we should generate ID of width MIDW
              else begin
                if (uid_enable == 0)
                  arid_tb = selected_master%(1<<`AXI_MIDW);
                else
                  arid_tb = urid_rand_cnt%(1<<`AXI_MIDW);
              end    
`else
              if (uid_enable == 0)
                arid_tb = selected_master%(1<<`AXI_MIDW);
              else
                arid_tb = urid_rand_cnt%(1<<`AXI_MIDW);
`endif
              `SET_DATA_PROP_W_CHECK("master",selected_master,mst_rd_buffer[xfer_count],"id", arid_tb, 0,is_valid)
              `TOP.axi_master_apply_wait_for_consumed(selected_master,mst_rd_buffer[xfer_count]);
    	        mst_rd_xact_sent = mst_rd_xact_sent + 1;
              if (test_debug) $display($time, " [TB_DEBUG] - %m - Generated RD_XACT with AID : %0d (mst_rd_xact_sent = %0d)\n",arid_tb, mst_rd_xact_sent);
            end
          end  
          if (test_debug) $display($time, " [TB_DEBUG] - %m - At the End of the wr_rd_generation_fork -- mst_wr_xact_sent = %0d, mst_rd_xact_sent = %0d\n",mst_wr_xact_sent,mst_rd_xact_sent);
        end
        // ---------------------------------------------------------------------------------------------------------------------
        begin : wr_completion_fork
          reg is_valid_wr = 0;
          integer callback_handle_wr = `SVT_CMD_NULL_HANDLE;
          integer mas_wr_xfer_cnt = 0;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - In the Begining of the wr_completion_fork \n");
          while (callback_handle_wr != `SVT_CMD_RESET_HANDLE) begin
            if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED) for MasterID=%0d \n", $time,selected_master);
            `TOP.vip_callback_wait_for("master",selected_master, "monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
            `TOP.check_for_1(is_valid_wr, "master wait for ending transfer", `ERROR_SEV);
            mas_wr_xfer_cnt++;
            `TOP.vip_callback_proceed("master",selected_master,"monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
            `TOP.check_for_1(is_valid_wr, "vip_callback_proceed :: master wait for starting transfer", `ERROR_SEV);
            if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) write transaction completed from MasterID=%0d \n",$time,mas_wr_xfer_cnt,selected_master);
            if(mas_wr_xfer_cnt == num_xact ) begin
              $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last write transaction completed from MasterID=%0d for transfer (%0d)\n",$time,selected_master,mas_wr_xfer_cnt);
              break;
            end
          end
          wr_completed = 1;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - At the End of the wr_completion_fork \n");
        end : wr_completion_fork
        // ---------------------------------------------------------------------------------------------------------------------
        begin : rd_completion_fork
          reg is_valid_rd = 0;
          integer callback_handle_rd = `SVT_CMD_NULL_HANDLE;
          integer mas_rd_xfer_cnt = 0;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - In the Begining of the rd_completion_fork \n");
          while (callback_handle_rd != `SVT_CMD_RESET_HANDLE) begin
            if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED for MasterID=%0d \n", $time,selected_master);
            `TOP.vip_callback_wait_for("master",selected_master, "monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
            `TOP.check_for_1(is_valid_rd, "master wait for ending transfer", `ERROR_SEV);
            `TOP.vip_callback_proceed("master",selected_master,"monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
            `TOP.check_for_1(is_valid_rd, "vip_callback_proceed :: master wait for starting transfer", `ERROR_SEV);
            if (`TOP.rlast_m_tb[selected_master]) begin
              mas_rd_xfer_cnt++;
              if (test_debug) $display("@%0d [TB_DEBUG] {%m} : Got the Notification for (%0d) read transaction completed from MasterID=%0d \n",$time,mas_rd_xfer_cnt,selected_master);
            end
            if(mas_rd_xfer_cnt == num_xact ) begin
              $display("\n@%0d [TB_INFO] {%m} : Got the Notification for last read transaction completed from MasterID=%0d for transfer (%0d)\n",$time,selected_master,mas_rd_xfer_cnt);
              break;
            end
          end
          rd_completed = 1;
          if (test_debug) $display($time, " [TB_DEBUG] - %m - At the End of the rd_completion_fork \n");
        end : rd_completion_fork
        // ---------------------------------------------------------------------------------------------------------------------
        //begin : timer_fork
        // #500_0000;
        // $display($time, " ERROR : RWCA/UID Test TIMEOUT (Input argument uid_enable = %0d)\n",uid_enable);
        //end : timer_fork
        // ---------------------------------------------------------------------------------------------------------------------
        begin : finish_fork
         wait (wr_completed && rd_completed);
         disable wr_rd_generation_fork;
         disable wr_completion_fork;
         disable rd_completion_fork;
         //disable timer_fork;
        end : finish_fork
        // ---------------------------------------------------------------------------------------------------------------------
      join
    
      if (test_debug) $display($time, " [TB_DEBUG] - %m - test_max_outstanding_uid : Complete");
      // set them back so that other tests doesn't get long delays
      very_long_bvalid_delay = 0;
      very_long_rvalid_delay = 0;
      zero_addr_ready_delay = 0;
      zero_addr_valid_delay = 0;
      arida_awida_test  = 0;
      rca_wca_test  = 0;
      outstanding_check_en = 0;
      fawc_farc_test = 0;
  
   end//if(run_test..
  end//begin-task
endtask  //test_max_outstanding_uid

/** Low Power interface Test for STAR 9000792946*/
/** 
  * Exit from low power by initiating a single write burst aligned with address 
  * (AWVALID, WLAST and WVALID asserted at the same clock edge)
  */
task automatic axi_low_power_test_star9000792946;
begin
  integer         handle;
  integer         xact_type;
  integer         loop_cnt;
  integer         callback_handle_wr,callback_handle_rd;
  reg             is_valid_wr,is_valid_rd,is_valid;
  integer         master_id,slave_id;
  
  $display("\n ************** Low Power Test for STAR 9000792946 started *************\n");

  for(loop_cnt=0; loop_cnt<1; loop_cnt++) begin
    //Do any random transfer
    single_master_single_slave_test;
    
    //wait for the DUT to become idle
    wait(cactive == 0);
  	repeat (1) @(posedge aclk);
    #(1) csysreq <= 0;
  	
    axi_idle = 25 + {$random(seed)} % 25 ;
  	repeat (axi_idle) @(posedge aclk);
    
    //Initiate a write burst of single transfer from any random master
    //with AWVALID, WLAST and WVALID asserted at the same clock edge
    master_id = ({$random(seed)} % `AXI_NUM_MASTERS) + 1;
    slave_id = ({$random(seed)} % `AXI_NUM_SLAVES) + 1;
    while (visible_slaves[master_id][slave_id] != 1)
    begin
      master_id = ({$random()} % `AXI_NUM_MASTERS) + 1;
      slave_id = ({$random()} % `AXI_NUM_SLAVES) + 1;
    end
    $display("\n@%0d [TB_INFO] {%m} : Selected Master ID is %0d, Slave ID is %0d\n",$time,master_id,slave_id);

    //xact_type = {$random(seed)} % 2;
    xact_type = 1;

    fork 
    begin
      /** Initiate a Read/Write transaction */
       `TOP.axi_master_rand_xact(master_id,slave_id,0,xact_type,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_SINGLE,0,handle);
       `GET_DATA_PROP_W_CHECK("master",master_id,handle,"xact_type",xact_type,0,is_valid)
       `TOP.axi_master_apply_wait_for_consumed(master_id,handle);
    end
  
    begin
      /** Test Shutdown thread for Write transactions */
      is_valid_wr = 0;
      callback_handle_wr = `SVT_CMD_NULL_HANDLE;
      while(callback_handle_wr != `SVT_CMD_RESET_HANDLE && xact_type) begin
        if (test_debug) 
          $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED\n",$time);
        `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
        `TOP.check_for_1(is_valid_wr, "master wait for ending write transfer", `ERROR_SEV);
        `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
        `TOP.check_for_1(is_valid_wr, "vip_callback_proceed :: master wait for starting write transfer", `ERROR_SEV);
  
        $display("\n@%0d [TB_INFO] : Got the Notification for Write transaction completed from master\n",$time);
        break; 
      end 
    end 
    begin
      /** Test Shutdown thread for Read transactions*/
      is_valid_rd = 0;
      callback_handle_rd = `SVT_CMD_NULL_HANDLE;
      while(callback_handle_rd != `SVT_CMD_RESET_HANDLE && !xact_type) begin
        if (test_debug)
          $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED\n", $time);
        `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
        `TOP.check_for_1(is_valid_rd, "master wait for ending read transfer", `ERROR_SEV);
        `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
        `TOP.check_for_1(is_valid_rd, "vip_callback_proceed :: master wait for starting read transfer", `ERROR_SEV);
  
        $display("\n@%0d [TB_INFO] : Got the Notification for Read transaction completed from master\n",$time);
        break; 
      end 
    end 
    join
  	
    repeat (1) @(posedge aclk);
    #(1) csysreq <= 1;
  end
  $display("\n ************** Low Power Test for STAR 9000792946 ended *************\n");
end
endtask

task automatic axi_bresp_before_addr_test;
begin
  integer         handle;
  integer         xact_type;
  integer         loop_cnt;
  integer         callback_handle_wr,callback_handle_rd;
  reg             is_valid_wr,is_valid_rd,is_valid;
  integer         master_id,slave_id;
  
  $display("\n ************** Directed Test for P80002107-2475 *************\n");

  for(loop_cnt=0; loop_cnt<1; loop_cnt++) begin
    
    axi_idle = 25 + {$random(seed)} % 25 ;
  	repeat (axi_idle) @(posedge aclk);
    
    //Initiate a write burst of single transfer from any random master
    //with AWVALID, WLAST and WVALID asserted at the same clock edge
    master_id = ({$random(seed)} % `AXI_NUM_MASTERS) + 1;
    slave_id = ({$random(seed)} % `AXI_NUM_SLAVES) + 1;
    while (visible_slaves[master_id][slave_id] != 1)
    begin
      master_id = ({$random()} % `AXI_NUM_MASTERS) + 1;
      slave_id = ({$random()} % `AXI_NUM_SLAVES) + 1;
    end
    $display("\n@%0d [TB_INFO] {%m} : Selected Master ID is %0d, Slave ID is %0d\n",$time,master_id,slave_id);

    //xact_type = {$random(seed)} % 2;
    bvalid_before_addr_test = 1;

    xact_type = 1;

    fork 
    begin
      /** Initiate a Read/Write transaction */
       `TOP.axi_master_rand_xact(master_id,slave_id,0,xact_type,`SIM_UNLOCK,`SIM_SECURE_RND,`SIM_BURST_SINGLE,0,handle);
       `GET_DATA_PROP_W_CHECK("master",master_id,handle,"xact_type",xact_type,0,is_valid)
       `TOP.axi_master_apply_wait_for_consumed(master_id,handle);
    end
  
    begin
      /** Test Shutdown thread for Write transactions */
      is_valid_wr = 0;
      callback_handle_wr = `SVT_CMD_NULL_HANDLE;
      while(callback_handle_wr != `SVT_CMD_RESET_HANDLE && xact_type) begin
        if (test_debug) 
          $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED\n",$time);
        `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
        `TOP.check_for_1(is_valid_wr, "master wait for ending write transfer", `ERROR_SEV);
        `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_WRITE_RESP_PHASE_ENDED",callback_handle_wr, is_valid_wr);
        `TOP.check_for_1(is_valid_wr, "vip_callback_proceed :: master wait for starting write transfer", `ERROR_SEV);
  
        $display("\n@%0d [TB_INFO] : Got the Notification for Write transaction completed from master\n",$time);
        break; 
      end 
    end 
    begin
      /** Test Shutdown thread for Read transactions*/
      is_valid_rd = 0;
      callback_handle_rd = `SVT_CMD_NULL_HANDLE;
      while(callback_handle_rd != `SVT_CMD_RESET_HANDLE && !xact_type) begin
        if (test_debug)
          $display("@%0d [TB_DEBUG] {%m} : Calling test_top.master.cmd_callback_wait_for(monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED\n", $time);
        `TOP.vip_callback_wait_for("master",master_id, "monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
        `TOP.check_for_1(is_valid_rd, "master wait for ending read transfer", `ERROR_SEV);
        `TOP.vip_callback_proceed("master",master_id,"monitor.NOTIFY_CB_READ_DATA_PHASE_ENDED",callback_handle_rd, is_valid_rd);
        `TOP.check_for_1(is_valid_rd, "vip_callback_proceed :: master wait for starting read transfer", `ERROR_SEV);
  
        $display("\n@%0d [TB_INFO] : Got the Notification for Read transaction completed from master\n",$time);
        break; 
      end 
    end 
    join
  	
  end
  $display("\n ************** Directed Test for P80002107-2475 *************\n");
end
endtask


