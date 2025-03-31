`ifdef AXI_VIP
  assign axi_mdpu_if.common_aclk = clk;
  assign axi_mdpu_if.master_if[0].aresetn = axi_reset_if.reset;
  assign axi_mdpu_if.master_if[1].aresetn = axi_reset_if.reset;
  assign axi_mdpu_if.master_if[2].aresetn = axi_reset_if.reset;

  assign axi_mdpu_if.slave_if[0].aresetn  = axi_reset_if.reset;
  assign axi_mdpu_if.slave_if[1].aresetn  = axi_reset_if.reset;
  assign axi_mdpu_if.slave_if[2].aresetn  = axi_reset_if.reset;

  assign axi_mdpu_if.master_if[0].awprot  = 0;
  assign axi_mdpu_if.master_if[0].arprot  = 0;
  assign axi_mdpu_if.master_if[0].acprot  = 0;
  assign axi_mdpu_if.master_if[0].awlock  = 0;
  assign axi_mdpu_if.master_if[0].arlock  = 0;
  assign axi_mdpu_if.master_if[0].awcache = 0;
  assign axi_mdpu_if.master_if[0].arcache = 0;

  assign axi_mdpu_if.slave_if[0].awprot   = 0;
  assign axi_mdpu_if.slave_if[0].arprot   = 0;
  assign axi_mdpu_if.slave_if[0].acprot   = 0;
  assign axi_mdpu_if.slave_if[0].awlock   = 0;
  assign axi_mdpu_if.slave_if[0].arlock   = 0;
  assign axi_mdpu_if.slave_if[0].arcache  = 0;
  assign axi_mdpu_if.slave_if[0].awcache  = 0;
`endif

//`ifdef DWPU_DPU_CONNECTION
//  `define DPU_SLV_PATH `DPU_1_SLV
//`else
//  `define DPU_SLV_PATH `DPU_0_SLV
//`endif
assign axi_mdpu_if.master_if[0].araddr   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_araddr_i   ;
assign axi_mdpu_if.master_if[0].arburst  = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arburst_i  ;
assign axi_mdpu_if.master_if[0].arid     = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arid_i     ;   
assign axi_mdpu_if.master_if[0].arlen    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arlen_i    ;  
assign axi_mdpu_if.master_if[0].arsize   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arsize_i   ; 
assign axi_mdpu_if.master_if[0].arvalid  = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arvalid_i  ; 
assign axi_mdpu_if.master_if[0].arready =  `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arready_o   ; 

assign axi_mdpu_if.master_if[0].awaddr   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awaddr_i   ;
assign axi_mdpu_if.master_if[0].awburst  = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awburst_i  ; 
assign axi_mdpu_if.master_if[0].awid     = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awid_i     ;    
assign axi_mdpu_if.master_if[0].awlen    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awlen_i    ;   
assign axi_mdpu_if.master_if[0].awsize   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awsize_i   ;  
assign axi_mdpu_if.master_if[0].awvalid  = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awvalid_i  ; 
assign axi_mdpu_if.master_if[0].awready  = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awready_o  ; 
   
assign axi_mdpu_if.master_if[0].bid      = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_bid_o      ; 
assign axi_mdpu_if.master_if[0].bresp    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_bresp_o    ;
assign axi_mdpu_if.master_if[0].bvalid   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_bvalid_o   ;
assign axi_mdpu_if.master_if[0].bready   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_bready_i   ;

assign axi_mdpu_if.master_if[0].rdata    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rdata_o    ;
assign axi_mdpu_if.master_if[0].rid      = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rid_o      ;
assign axi_mdpu_if.master_if[0].rlast    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rlast_o    ;
assign axi_mdpu_if.master_if[0].rresp    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rresp_o    ;
assign  axi_mdpu_if.master_if[0].rvalid  = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rvalid_o   ;
assign axi_mdpu_if.master_if[0].rready   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rready_i   ;

assign axi_mdpu_if.master_if[0].wdata    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wdata_i    ;
assign axi_mdpu_if.master_if[0].wlast    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wlast_i    ;
assign axi_mdpu_if.master_if[0].wstrb    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wstrb_i    ;
assign axi_mdpu_if.master_if[0].wvalid   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wvalid_i   ;
assign axi_mdpu_if.master_if[0].wready   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wready_o   ;

assign axi_mdpu_if.master_if[1].tdata    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_iau_axis_s_data_i ;
assign axi_mdpu_if.master_if[1].tlast    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_iau_axis_s_last_i ;
assign axi_mdpu_if.master_if[1].tvalid   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_iau_axis_s_valid_i;
assign axi_mdpu_if.master_if[1].tready   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_iau_axis_s_ready_o;
                                          
assign axi_mdpu_if.master_if[2].tdata    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_ifd1_axis_s_data_i ;
assign axi_mdpu_if.master_if[2].tlast    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_ifd1_axis_s_last_i ;
assign axi_mdpu_if.master_if[2].tvalid   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_ifd1_axis_s_valid_i;
assign axi_mdpu_if.master_if[2].tready   = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_ifd1_axis_s_ready_o;

assign axi_mdpu_if.slave_if[1].tdata     = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_odr_axis_m_data_o ;                        
assign axi_mdpu_if.slave_if[1].tlast     = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_odr_axis_m_last_o ;
assign axi_mdpu_if.slave_if[1].tvalid    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_odr_axis_m_valid_o;
assign axi_mdpu_if.slave_if[1].tready    = `DPU_0_SLV.u_ai_core_iau_dpu.i_dpu.dpu_odr_axis_m_ready_i;
 
assign dpu_tok_agt_if.reset_n      = axi_reset_if.reset;
assign dpu_tok_agt_if.tok_cons_rdy = `DPU_0_SLV.dpu_tok_cons_rdy;
assign dpu_tok_agt_if.tok_prod_vld = `DPU_0_SLV.dpu_tok_prod_vld;
assign dpu_tok_agt_if.tok_cons_vld = `DPU_0_SLV.dpu_tok_cons_vld;
assign dpu_tok_agt_if.tok_prod_rdy = `DPU_0_SLV.dpu_tok_prod_rdy;                                                                        
 
uvm_config_db#(virtual dpu_if)::set(null, "uvm_test_top.env.m_dpu_env.dpu_agt", "vif", if_dpu);
uvm_config_db#(virtual iid_if)::set(null, "uvm_test_top.env.m_dpu_env", "iid_if_i", iid_if_i);

//dwpu
`ifdef AXI_VIP
  assign axi_ddpu_if.common_aclk = clk;
  assign axi_ddpu_if.master_if[0].aresetn = axi_reset_if.reset;
  assign axi_ddpu_if.master_if[1].aresetn = axi_reset_if.reset;
  assign axi_ddpu_if.master_if[2].aresetn = axi_reset_if.reset;

  assign axi_ddpu_if.slave_if[0].aresetn  = axi_reset_if.reset;
  assign axi_ddpu_if.slave_if[1].aresetn  = axi_reset_if.reset;
  assign axi_ddpu_if.slave_if[2].aresetn  = axi_reset_if.reset;

  assign axi_ddpu_if.master_if[0].awprot  = 0;
  assign axi_ddpu_if.master_if[0].arprot  = 0;
  assign axi_ddpu_if.master_if[0].acprot  = 0;
  assign axi_ddpu_if.master_if[0].awlock  = 0;
  assign axi_ddpu_if.master_if[0].arlock  = 0;
  assign axi_ddpu_if.master_if[0].awcache = 0;
  assign axi_ddpu_if.master_if[0].arcache = 0;

  assign axi_ddpu_if.slave_if[0].awprot   = 0;
  assign axi_ddpu_if.slave_if[0].arprot   = 0;
  assign axi_ddpu_if.slave_if[0].acprot   = 0;
  assign axi_ddpu_if.slave_if[0].awlock   = 0;
  assign axi_ddpu_if.slave_if[0].arlock   = 0;
  assign axi_ddpu_if.slave_if[0].arcache  = 0;
  assign axi_ddpu_if.slave_if[0].awcache  = 0;
`endif

//`ifdef DWPU_DPU_CONNECTION
//  `define DPU_SLV_PATH `DPU_1_SLV
//`else
//  `define DPU_SLV_PATH `DPU_0_SLV
//`endif
assign axi_ddpu_if.master_if[0].araddr   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_araddr_i   ;
assign axi_ddpu_if.master_if[0].arburst  = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arburst_i  ;
assign axi_ddpu_if.master_if[0].arid     = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arid_i     ;   
assign axi_ddpu_if.master_if[0].arlen    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arlen_i    ;  
assign axi_ddpu_if.master_if[0].arsize   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arsize_i   ; 
assign axi_ddpu_if.master_if[0].arvalid  = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arvalid_i  ; 
assign axi_ddpu_if.master_if[0].arready =  `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_arready_o   ; 

assign axi_ddpu_if.master_if[0].awaddr   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awaddr_i   ;
assign axi_ddpu_if.master_if[0].awburst  = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awburst_i  ; 
assign axi_ddpu_if.master_if[0].awid     = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awid_i     ;    
assign axi_ddpu_if.master_if[0].awlen    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awlen_i    ;   
assign axi_ddpu_if.master_if[0].awsize   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awsize_i   ;  
assign axi_ddpu_if.master_if[0].awvalid  = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awvalid_i  ; 
assign axi_ddpu_if.master_if[0].awready  = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_awready_o  ; 
   
assign axi_ddpu_if.master_if[0].bid      = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_bid_o      ; 
assign axi_ddpu_if.master_if[0].bresp    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_bresp_o    ;
assign axi_ddpu_if.master_if[0].bvalid   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_bvalid_o   ;
assign axi_ddpu_if.master_if[0].bready   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_bready_i   ;

assign axi_ddpu_if.master_if[0].rdata    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rdata_o    ;
assign axi_ddpu_if.master_if[0].rid      = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rid_o      ;
assign axi_ddpu_if.master_if[0].rlast    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rlast_o    ;
assign axi_ddpu_if.master_if[0].rresp    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rresp_o    ;
assign  axi_ddpu_if.master_if[0].rvalid  = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rvalid_o   ;
assign axi_ddpu_if.master_if[0].rready   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_rready_i   ;

assign axi_ddpu_if.master_if[0].wdata    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wdata_i    ;
assign axi_ddpu_if.master_if[0].wlast    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wlast_i    ;
assign axi_ddpu_if.master_if[0].wstrb    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wstrb_i    ;
assign axi_ddpu_if.master_if[0].wvalid   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wvalid_i   ;
assign axi_ddpu_if.master_if[0].wready   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_cfg_axi_s_wready_o   ;

assign axi_ddpu_if.master_if[1].tdata    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_iau_axis_s_data_i ;
assign axi_ddpu_if.master_if[1].tlast    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_iau_axis_s_last_i ;
assign axi_ddpu_if.master_if[1].tvalid   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_iau_axis_s_valid_i;
assign axi_ddpu_if.master_if[1].tready   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_iau_axis_s_ready_o;
                                                                                    
assign axi_ddpu_if.master_if[2].tdata    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_ifd1_axis_s_data_i ;
assign axi_ddpu_if.master_if[2].tlast    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_ifd1_axis_s_last_i ;
assign axi_ddpu_if.master_if[2].tvalid   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_ifd1_axis_s_valid_i;
assign axi_ddpu_if.master_if[2].tready   = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_ifd1_axis_s_ready_o;
                                                             
assign axi_ddpu_if.slave_if[1].tdata     = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_odr_axis_m_data_o ;                        
assign axi_ddpu_if.slave_if[1].tlast     = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_odr_axis_m_last_o ;
assign axi_ddpu_if.slave_if[1].tvalid    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_odr_axis_m_valid_o;
assign axi_ddpu_if.slave_if[1].tready    = `DPU_1_SLV.u_ai_core_iau_dpu.i_dpu.dpu_odr_axis_m_ready_i;
 
//assign dpu_tok_agt_if.reset_n      = axi_reset_if.reset;
//assign dpu_tok_agt_if.tok_cons_rdy = `DPU_1_SLV.dpu_tok_cons_rdy;
//assign dpu_tok_agt_if.tok_prod_vld = `DPU_1_SLV.dpu_tok_prod_vld;
//assign dpu_tok_agt_if.tok_cons_vld = `DPU_1_SLV.dpu_tok_cons_vld;
//assign dpu_tok_agt_if.tok_prod_rdy = `DPU_1_SLV.dpu_tok_prod_rdy;                                                                        
 
uvm_config_db#(virtual dpu_if)::set(null, "uvm_test_top.env.d_dpu_env.dpu_agt", "vif", if_dpu);
uvm_config_db#(virtual iid_if)::set(null, "uvm_test_top.env.d_dpu_env", "iid_if_i", iid_if_i);

