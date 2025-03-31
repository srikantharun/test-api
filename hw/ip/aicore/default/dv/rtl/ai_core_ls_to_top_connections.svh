 `ifdef AXI_VIP
  assign axi_ls_if.common_aclk = clk;
  assign axi_ls_if.master_if[0].aresetn = axi_reset_if.reset;
  assign axi_ls_if.master_if[1].aresetn = axi_reset_if.reset;
  assign axi_ls_if.master_if[2].aresetn = axi_reset_if.reset;
  assign axi_ls_if.master_if[3].aresetn = axi_reset_if.reset;

  assign axi_ls_if.slave_if[0].aresetn  = axi_reset_if.reset;
  assign axi_ls_if.slave_if[1].aresetn  = axi_reset_if.reset;
  assign axi_ls_if.slave_if[2].aresetn  = axi_reset_if.reset;
  assign axi_ls_if.slave_if[3].aresetn  = axi_reset_if.reset;
  assign axi_ls_if.slave_if[4].aresetn  = axi_reset_if.reset;
  assign axi_ls_if.slave_if[5].aresetn  = axi_reset_if.reset;
  assign axi_ls_if.slave_if[6].aresetn  = axi_reset_if.reset;

 `ifdef AXI_VIP_CONN_CFG
  assign  axi_ls_if.master_if[0].awvalid   =  `LS_LP_SLV.cfg_axi_s_awvalid ;
  assign  axi_ls_if.master_if[0].awaddr    =  `LS_LP_SLV.cfg_axi_s_awaddr  ;
  assign  axi_ls_if.master_if[0].awid      =  `LS_LP_SLV.cfg_axi_s_awid    ;
  assign  axi_ls_if.master_if[0].awlen     =  `LS_LP_SLV.cfg_axi_s_awlen   ;
  assign  axi_ls_if.master_if[0].awsize    =  `LS_LP_SLV.cfg_axi_s_awsize  ;
  assign  axi_ls_if.master_if[0].awburst   =  `LS_LP_SLV.cfg_axi_s_awburst ;
  assign  axi_ls_if.master_if[0].awlock    =  `LS_LP_SLV.cfg_axi_s_awlock  ;
  assign  axi_ls_if.master_if[0].awcache   =  `LS_LP_SLV.cfg_axi_s_awcache ;
  assign  axi_ls_if.master_if[0].awprot    =  `LS_LP_SLV.cfg_axi_s_awprot  ;

  assign  axi_ls_if.master_if[0].awready   =  `LS_LP_SLV.cfg_axi_s_awready ;

  assign  axi_ls_if.master_if[0].wvalid    =  `LS_LP_SLV.cfg_axi_s_wvalid  ;
  assign  axi_ls_if.master_if[0].wlast     =  `LS_LP_SLV.cfg_axi_s_wlast   ; 
  assign  axi_ls_if.master_if[0].wdata     =  `LS_LP_SLV.cfg_axi_s_wdata   ; 
  assign  axi_ls_if.master_if[0].wstrb     =  `LS_LP_SLV.cfg_axi_s_wstrb   ; 
  assign  axi_ls_if.master_if[0].wready    =  `LS_LP_SLV.cfg_axi_s_wready  ;

  assign  axi_ls_if.master_if[0].bvalid    =  `LS_LP_SLV.cfg_axi_s_bvalid  ;
  assign  axi_ls_if.master_if[0].bid       =  `LS_LP_SLV.cfg_axi_s_bid     ;
  assign  axi_ls_if.master_if[0].bresp     =  `LS_LP_SLV.cfg_axi_s_bresp   ;

  assign  axi_ls_if.master_if[0].bready    =  `LS_LP_SLV.cfg_axi_s_bready   ;
  assign  axi_ls_if.master_if[0].arvalid   =  `LS_LP_SLV.cfg_axi_s_arvalid  ;
  assign  axi_ls_if.master_if[0].araddr    =  `LS_LP_SLV.cfg_axi_s_araddr   ;
  assign  axi_ls_if.master_if[0].arid      =  `LS_LP_SLV.cfg_axi_s_arid     ;
  assign  axi_ls_if.master_if[0].arlen     =  `LS_LP_SLV.cfg_axi_s_arlen    ;
  assign  axi_ls_if.master_if[0].arsize    =  `LS_LP_SLV.cfg_axi_s_arsize   ;
  assign  axi_ls_if.master_if[0].arburst   =  `LS_LP_SLV.cfg_axi_s_arburst  ;
  assign  axi_ls_if.master_if[0].arlock    =  `LS_LP_SLV.cfg_axi_s_arlock   ;
  assign  axi_ls_if.master_if[0].arcache   =  `LS_LP_SLV.cfg_axi_s_arcache  ;
  assign  axi_ls_if.master_if[0].arprot    =  `LS_LP_SLV.cfg_axi_s_arprot   ;

  assign axi_ls_if.master_if[0].arready    = `LS_LP_SLV.cfg_axi_s_arready;
  assign axi_ls_if.master_if[0].rvalid     = `LS_LP_SLV.cfg_axi_s_rvalid ;
  assign axi_ls_if.master_if[0].rlast      = `LS_LP_SLV.cfg_axi_s_rlast  ;
  assign axi_ls_if.master_if[0].rid        = `LS_LP_SLV.cfg_axi_s_rid    ;
  assign axi_ls_if.master_if[0].rdata      = `LS_LP_SLV.cfg_axi_s_rdata  ;
  assign axi_ls_if.master_if[0].rresp      = `LS_LP_SLV.cfg_axi_s_rresp  ;
  assign axi_ls_if.master_if[0].rready     = `LS_LP_SLV.cfg_axi_s_rready ;
`endif

`ifdef AXI_VIP_CONN_M
  assign axi_ls_if.master_if[1].awvalid  = `LS_LP_SLV.hp_axi_s_awvalid ;  
  assign axi_ls_if.master_if[1].awaddr   = `LS_LP_SLV.hp_axi_s_awaddr  ;   
  assign axi_ls_if.master_if[1].awid     = `LS_LP_SLV.hp_axi_s_awid    ;   
  assign axi_ls_if.master_if[1].awlen    = `LS_LP_SLV.hp_axi_s_awlen   ;   
  assign axi_ls_if.master_if[1].awsize   = `LS_LP_SLV.hp_axi_s_awsize  ;   
  assign axi_ls_if.master_if[1].awburst  = `LS_LP_SLV.hp_axi_s_awburst ;  
  assign axi_ls_if.master_if[1].awlock   = `LS_LP_SLV.hp_axi_s_awlock  ;   
  assign axi_ls_if.master_if[1].awcache  = `LS_LP_SLV.hp_axi_s_awcache ;  
  assign axi_ls_if.master_if[1].awprot   = `LS_LP_SLV.hp_axi_s_awprot  ;   
  assign axi_ls_if.master_if[1].awready  = `LS_LP_SLV.hp_axi_s_awready ;  

  assign axi_ls_if.master_if[1].wvalid   = `LS_LP_SLV.hp_axi_s_wvalid  ;   
  assign axi_ls_if.master_if[1].wlast    = `LS_LP_SLV.hp_axi_s_wlast   ;   
  assign axi_ls_if.master_if[1].wdata    = `LS_LP_SLV.hp_axi_s_wdata   ;   
  assign axi_ls_if.master_if[1].wstrb    = `LS_LP_SLV.hp_axi_s_wstrb   ;   

  assign axi_ls_if.master_if[1].wready   = `LS_LP_SLV.hp_axi_s_wready  ;
  assign axi_ls_if.master_if[1].bvalid   = `LS_LP_SLV.hp_axi_s_bvalid  ;
  assign axi_ls_if.master_if[1].bid      = `LS_LP_SLV.hp_axi_s_bid    ;
  assign axi_ls_if.master_if[1].bresp    = `LS_LP_SLV.hp_axi_s_bresp   ;

  assign  axi_ls_if.master_if[1].bready  = `LS_LP_SLV.hp_axi_s_bready  ;     
  assign  axi_ls_if.master_if[1].arvalid = `LS_LP_SLV.hp_axi_s_arvalid ;    
  assign  axi_ls_if.master_if[1].araddr  = `LS_LP_SLV.hp_axi_s_araddr  ;     
  assign  axi_ls_if.master_if[1].arid    = `LS_LP_SLV.hp_axi_s_arid    ;  
  assign  axi_ls_if.master_if[1].arlen   = `LS_LP_SLV.hp_axi_s_arlen   ;  
  assign  axi_ls_if.master_if[1].arsize  = `LS_LP_SLV.hp_axi_s_arsize  ;     
  assign  axi_ls_if.master_if[1].arburst = `LS_LP_SLV.hp_axi_s_arburst ;    
  assign  axi_ls_if.master_if[1].arlock  = `LS_LP_SLV.hp_axi_s_arlock  ;     
  assign  axi_ls_if.master_if[1].arcache = `LS_LP_SLV.hp_axi_s_arcache ;    
  assign  axi_ls_if.master_if[1].arprot  = `LS_LP_SLV.hp_axi_s_arprot  ;     

  assign axi_ls_if.master_if[1].arready  = `LS_LP_SLV.hp_axi_s_arready  ;
  assign axi_ls_if.master_if[1].rvalid   = `LS_LP_SLV.hp_axi_s_rvalid   ;
  assign axi_ls_if.master_if[1].rlast    = `LS_LP_SLV.hp_axi_s_rlast    ;
  assign axi_ls_if.master_if[1].rid      = `LS_LP_SLV.hp_axi_s_rid      ;
  assign axi_ls_if.master_if[1].rdata    = `LS_LP_SLV.hp_axi_s_rdata    ;
  assign axi_ls_if.master_if[1].rresp    = `LS_LP_SLV.hp_axi_s_rresp    ;
  assign axi_ls_if.master_if[1].rready   = `LS_LP_SLV.hp_axi_s_rready   ;
`endif
  //------------------------------------------------------
  // AXIS: LS Slaves -> VIP Master Interfaces
  //------------------------------------------------------
  // MVM ODR
  assign axi_ls_if.master_if[2].tvalid  = `LS_LP_SLV.mvm_odr_axis_s_tvalid          ; // Input
  assign axi_ls_if.master_if[2].tready  = `LS_LP_SLV.mvm_odr_axis_s_tready          ; // Output
  assign axi_ls_if.master_if[2].tdata   = `LS_LP_SLV.mvm_odr_axis_s_tdata           ;  // Input
  assign axi_ls_if.master_if[2].tlast   = `LS_LP_SLV.mvm_odr_axis_s_tlast           ;  // Input
  // DWPU ODR
  assign axi_ls_if.master_if[3].tvalid = `LS_LP_SLV.dwpu_odr_axis_s_tvalid ;     // Input
  assign axi_ls_if.master_if[3].tready = `LS_LP_SLV.dwpu_odr_axis_s_tready ;     // Output
  assign axi_ls_if.master_if[3].tdata  = `LS_LP_SLV.dwpu_odr_axis_s_tdata  ;     // Input
  assign axi_ls_if.master_if[3].tlast  = `LS_LP_SLV.dwpu_odr_axis_s_tlast  ;     // Input

  //slave0
  `ifdef AXI_VIP_CONN_S
  // Slave DUT
  assign axi_ls_if.slave_if[0].awvalid = `LS_LP_SLV.hp_axi_m_awvalid   ;
  assign axi_ls_if.slave_if[0].awaddr  = `LS_LP_SLV.hp_axi_m_awaddr    ;
  assign axi_ls_if.slave_if[0].awid    = `LS_LP_SLV.hp_axi_m_awid      ;
  assign axi_ls_if.slave_if[0].awlen   = `LS_LP_SLV.hp_axi_m_awlen     ;
  assign axi_ls_if.slave_if[0].awsize  = `LS_LP_SLV.hp_axi_m_awsize    ;
  assign axi_ls_if.slave_if[0].awburst = `LS_LP_SLV.hp_axi_m_awburst   ;
  assign axi_ls_if.slave_if[0].awlock  = `LS_LP_SLV.hp_axi_m_awlock    ;
  assign axi_ls_if.slave_if[0].awcache = `LS_LP_SLV.hp_axi_m_awcache   ;
  assign axi_ls_if.slave_if[0].awprot  = `LS_LP_SLV.hp_axi_m_awprot    ;
  assign axi_ls_if.slave_if[0].awready = `LS_LP_SLV.hp_axi_m_awready   ; // Input

  assign axi_ls_if.slave_if[0].wvalid  = `LS_LP_SLV.hp_axi_m_wvalid    ;
  assign axi_ls_if.slave_if[0].wlast   = `LS_LP_SLV.hp_axi_m_wlast     ;
  assign axi_ls_if.slave_if[0].wdata   = `LS_LP_SLV.hp_axi_m_wdata     ;
  assign axi_ls_if.slave_if[0].wstrb   = `LS_LP_SLV.hp_axi_m_wstrb     ;
  assign axi_ls_if.slave_if[0].wready  =  `LS_LP_SLV.hp_axi_m_wready   ; // Input
                                                                    
  assign  axi_ls_if.slave_if[0].bvalid = `LS_LP_SLV.hp_axi_m_bvalid    ;
  assign  axi_ls_if.slave_if[0].bid    = `LS_LP_SLV.hp_axi_m_bid       ;
  assign  axi_ls_if.slave_if[0].bresp  = `LS_LP_SLV.hp_axi_m_bresp     ;
  assign  axi_ls_if.slave_if[0].bready = `LS_LP_SLV.hp_axi_m_bready    ;          // Output

  assign axi_ls_if.slave_if[0].arvalid = `LS_LP_SLV.hp_axi_m_arvalid   ;
  assign axi_ls_if.slave_if[0].araddr  = `LS_LP_SLV.hp_axi_m_araddr    ;
  assign axi_ls_if.slave_if[0].arid    = `LS_LP_SLV.hp_axi_m_arid      ;
  assign axi_ls_if.slave_if[0].arlen   = `LS_LP_SLV.hp_axi_m_arlen     ;
  assign axi_ls_if.slave_if[0].arsize  = `LS_LP_SLV.hp_axi_m_arsize    ;
  assign axi_ls_if.slave_if[0].arburst = `LS_LP_SLV.hp_axi_m_arburst   ;
  assign axi_ls_if.slave_if[0].arlock  = `LS_LP_SLV.hp_axi_m_arlock    ;
  assign axi_ls_if.slave_if[0].arcache = `LS_LP_SLV.hp_axi_m_arcache   ;
  assign axi_ls_if.slave_if[0].arprot  = `LS_LP_SLV.hp_axi_m_arprot    ;
  assign axi_ls_if.slave_if[0].arready = `LS_LP_SLV.hp_axi_m_arready   ; // Input
                                                                                  
  assign  axi_ls_if.slave_if[0].rvalid = `LS_LP_SLV.hp_axi_m_rvalid    ;               
  assign  axi_ls_if.slave_if[0].rlast  = `LS_LP_SLV.hp_axi_m_rlast     ;               
  assign  axi_ls_if.slave_if[0].rid    = `LS_LP_SLV.hp_axi_m_rid       ;               
  assign  axi_ls_if.slave_if[0].rdata  = `LS_LP_SLV.hp_axi_m_rdata     ;               
  assign  axi_ls_if.slave_if[0].rresp  = `LS_LP_SLV.hp_axi_m_rresp     ;               
  assign  axi_ls_if.slave_if[0].rready = `LS_LP_SLV.hp_axi_m_rready    ;
`endif

//------------------------------------------------------
  // AXIS: LS Masters -> VIP Slave Interfaces
  //------------------------------------------------------
  // MVM IFD0
  assign axi_ls_if.slave_if[1].tvalid = `LS_LP_SLV.mvm_ifd0_axis_m_tvalid;
  assign axi_ls_if.slave_if[1].tready = `LS_LP_SLV.mvm_ifd0_axis_m_tready           ; //input from DUT
  assign axi_ls_if.slave_if[1].tdata  = `LS_LP_SLV.mvm_ifd0_axis_m_tdata ;
  assign axi_ls_if.slave_if[1].tlast  = `LS_LP_SLV.mvm_ifd0_axis_m_tlast ;

  // MVM IFD1
  assign axi_ls_if.slave_if[2].tvalid = `LS_LP_SLV.mvm_ifd1_axis_m_tvalid;
  assign axi_ls_if.slave_if[2].tready = `LS_LP_SLV.mvm_ifd1_axis_m_tready; //input from DUT
  assign axi_ls_if.slave_if[2].tdata  = `LS_LP_SLV.mvm_ifd1_axis_m_tdata ;
  assign axi_ls_if.slave_if[2].tlast  = `LS_LP_SLV.mvm_ifd1_axis_m_tlast ;

  // MVM IFDW
  assign axi_ls_if.slave_if[3].tvalid = `LS_LP_SLV.mvm_ifdw_axis_m_tvalid;
  assign axi_ls_if.slave_if[3].tready = `LS_LP_SLV.mvm_ifdw_axis_m_tready; //input from DUT
  assign axi_ls_if.slave_if[3].tdata  = `LS_LP_SLV.mvm_ifdw_axis_m_tdata ;
  assign axi_ls_if.slave_if[3].tlast  = `LS_LP_SLV.mvm_ifdw_axis_m_tlast ;

  // DW IFD0
  assign axi_ls_if.slave_if[4].tvalid = `LS_LP_SLV.dwpu_ifd0_axis_m_tvalid;
  assign axi_ls_if.slave_if[4].tready = `LS_LP_SLV.dwpu_ifd0_axis_m_tready; //input from DUT
  assign axi_ls_if.slave_if[4].tdata  = `LS_LP_SLV.dwpu_ifd0_axis_m_tdata ;
  assign axi_ls_if.slave_if[4].tlast  = `LS_LP_SLV.dwpu_ifd0_axis_m_tlast ;

  // DW IFD1
  assign axi_ls_if.slave_if[5].tvalid = `LS_LP_SLV.dwpu_ifd1_axis_m_tvalid;
  assign axi_ls_if.slave_if[5].tready = `LS_LP_SLV.dwpu_ifd1_axis_m_tready; //input from DUT
  assign axi_ls_if.slave_if[5].tdata  = `LS_LP_SLV.dwpu_ifd1_axis_m_tdata ;
  assign axi_ls_if.slave_if[5].tlast  = `LS_LP_SLV.dwpu_ifd1_axis_m_tlast ;

`endif //AXI_VIP
 

assign if_ai_core_ls.reset_an_i                   = `LS_LP_SLV.rst_n;
assign if_ai_core_ls.cid                          = `LS_LP_SLV.cid;
assign if_ai_core_ls.va_base                      = `LS_LP_SLV.va_base;
assign if_ai_core_ls.l1_cg_enable                 = `LS_LP_SLV.l1_cg_enable;
assign if_ai_core_ls.ifd_odr_cg_enable            = `LS_LP_SLV.ifd_odr_cg_enable;
assign if_ai_core_ls.l1_sw_cfg_fabric_sel         = `LS_LP_SLV.l1_sw_cfg_fabric_sel;
assign if_ai_core_ls.l1_mem_ls                    = `LS_LP_SLV.l1_mem_ls;
assign if_ai_core_ls.l1_mem_ds                    = `LS_LP_SLV.l1_mem_ds;
assign if_ai_core_ls.l1_mem_sd                    = `LS_LP_SLV.l1_mem_sd;
assign if_ai_core_ls.l1_mem_rop                   = `LS_LP_SLV.l1_mem_rop;
assign if_ai_core_ls.l1_mem_daisy_chain_bypass_sd = `LS_LP_SLV.l1_mem_daisy_chain_bypass_sd;
assign if_ai_core_ls.l1_mem_daisy_chain_bypass_ds = `LS_LP_SLV.l1_mem_daisy_chain_bypass_ds;
assign if_ai_core_ls.ai_core_ls_obs               = `LS_LP_SLV.ai_core_ls_obs;
assign if_ai_core_ls.l1_lc_fabric_dlock           = `LS_LP_SLV.l1_lc_fabric_dlock;
assign if_ai_core_ls.sram_sw_test1                = `LS_LP_SLV.sram_sw_test1;
assign if_ai_core_ls.sram_sw_test_rnm             = `LS_LP_SLV.sram_sw_test_rnm;
assign if_ai_core_ls.sram_sw_rme                  = `LS_LP_SLV.sram_sw_rme;
assign if_ai_core_ls.sram_sw_rm                   = `LS_LP_SLV.sram_sw_rm;
assign if_ai_core_ls.sram_sw_wa                   = `LS_LP_SLV.sram_sw_wa;
assign if_ai_core_ls.sram_sw_wpulse               = `LS_LP_SLV.sram_sw_wpulse;
assign if_ai_core_ls.sram_sw_fiso                 = `LS_LP_SLV.sram_sw_fiso;
assign if_ai_core_ls.ls_cg_en                     = `LS_LP_SLV.ls_cg_en;
assign if_ai_core_ls.irq_out                      = `LS_LP_SLV.irq_out;
