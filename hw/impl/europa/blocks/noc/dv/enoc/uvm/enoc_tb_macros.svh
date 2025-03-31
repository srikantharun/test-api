// *** (C) Copyright Axelera AI 2024        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //
// *** Desrp : TB Macros used for           *** //
// *** declartion & connecting the RTL      *** //

`define NUM_AXI_INITIATORS  35
`define NUM_AXI_TARGETS     34
`define NUM_APB4_TARGETS    34
`define NUM_APB3_TARGETS    9 
`define DUT noc_top

// =============================================================================================================
// macros to create & connect the signals of Common Clocks
// =============================================================================================================
`define create_and_bind_clk(subip_name, intf) \
  bit                 ``subip_name``_clk; \
  assign ``subip_name``_clk         = intf.aclk; 
  
// =============================================================================================================
// macros to create & connect the signals of RESET
// =============================================================================================================
`define create_and_bind_rst(subip_name, intf) \
  bit                 ``subip_name``_rst_n; \
  assign ``subip_name``_rst_n    = intf.aresetn;

// =============================================================================================================
// macros to create & connect the signals of Always-ON RESET
// =============================================================================================================
`define create_and_bind_aorst(subip_name, intf) \
  bit                 ``subip_name``_aon_rst_n; \
  assign ``subip_name``_aon_rst_n    = intf.aresetn;

// =============================================================================================================
// macros to create & connect the OCP intf signals 
// =============================================================================================================
`define create_and_bind_ocp(subip_name, intf) \
  bit [7:0]          i_``subip_name``_init_tok_ocpl_s_maddr; \
  bit                i_``subip_name``_init_tok_ocpl_s_mcmd; \
  bit [7:0]          i_``subip_name``_init_tok_ocpl_s_mdata; \
  bit                o_``subip_name``_init_tok_ocpl_s_scmdaccept; \
  bit [7:0]          o_``subip_name``_targ_tok_ocpl_m_maddr; \
  bit                o_``subip_name``_targ_tok_ocpl_m_mcmd; \
  bit [7:0]          o_``subip_name``_targ_tok_ocpl_m_mdata; \
  bit                i_``subip_name``_targ_tok_ocpl_m_scmdaccept; \
  assign i_``subip_name``_init_tok_ocpl_s_maddr       = intf.i_``subip_name``_init_tok_ocpl_s_maddr     ; \ 
  assign i_``subip_name``_init_tok_ocpl_s_mcmd        = intf.i_``subip_name``_init_tok_ocpl_s_mcmd      ; \ 
  assign i_``subip_name``_init_tok_ocpl_s_mdata       = intf.i_``subip_name``_init_tok_ocpl_s_mdata     ; \ 
  assign o_``subip_name``_init_tok_ocpl_s_scmdaccept  = intf.o_``subip_name``_init_tok_ocpl_s_scmdaccept; \ 
  assign intf.o_``subip_name``_targ_tok_ocpl_m_maddr       = o_``subip_name``_targ_tok_ocpl_m_maddr     ; \ 
  assign intf.o_``subip_name``_targ_tok_ocpl_m_mcmd        = o_``subip_name``_targ_tok_ocpl_m_mcmd      ; \ 
  assign intf.o_``subip_name``_targ_tok_ocpl_m_mdata       = o_``subip_name``_targ_tok_ocpl_m_mdata     ; \ 
  assign intf.i_``subip_name``_targ_tok_ocpl_m_scmdaccept  = i_``subip_name``_targ_tok_ocpl_m_scmdaccept; 

// =============================================================================================================
// macros that create the signals of AXI and assign them to the VIPs interface
// =============================================================================================================
`define create_and_bind_axi_read_mst(w_name, addr_w, data_w, id_w, len_w, intf) \
  bit  [ 3:0]        i_``w_name``_axi_s_arqos; \
  bit  [ addr_w-1:0] i_``w_name``_axi_s_araddr; \
  bit  [  1:0]       i_``w_name``_axi_s_arburst; \
  bit  [  3:0]       i_``w_name``_axi_s_arcache; \
  bit  [id_w-1:0]    i_``w_name``_axi_s_arid; \
  bit  [len_w-1:0]   i_``w_name``_axi_s_arlen; \
  bit                i_``w_name``_axi_s_arlock; \
  bit  [  2:0]       i_``w_name``_axi_s_arprot; \
  bit  [  2:0]       i_``w_name``_axi_s_arsize; \
  bit                i_``w_name``_axi_s_arvalid; \
  bit                o_``w_name``_axi_s_arready; \
  bit  [data_w-1:0]  o_``w_name``_axi_s_rdata; \
  bit  [id_w-1:0]    o_``w_name``_axi_s_rid; \
  bit                o_``w_name``_axi_s_rlast; \
  bit  [  1:0]       o_``w_name``_axi_s_rresp; \
  bit                o_``w_name``_axi_s_rvalid; \
  bit                i_``w_name``_axi_s_rready; \
  assign i_``w_name``_axi_s_araddr    = intf.araddr; \
  assign i_``w_name``_axi_s_arburst   = intf.arburst; \
  assign i_``w_name``_axi_s_arcache   = intf.arcache; \
  assign i_``w_name``_axi_s_arid      = intf.arid; \
  assign i_``w_name``_axi_s_arlen     = intf.arlen; \
  assign i_``w_name``_axi_s_arlock    = intf.arlock; \
  assign i_``w_name``_axi_s_arprot    = intf.arprot; \
  assign i_``w_name``_axi_s_arsize    = intf.arsize; \
  assign i_``w_name``_axi_s_arvalid   = intf.arvalid; \
  assign intf.arready                 = o_``w_name``_axi_s_arready; \
  assign intf.rdata                   = o_``w_name``_axi_s_rdata; \
  assign intf.rid                     = o_``w_name``_axi_s_rid; \
  assign intf.rlast                   = o_``w_name``_axi_s_rlast; \
  assign intf.rresp                   = o_``w_name``_axi_s_rresp; \
  assign intf.rvalid                  = o_``w_name``_axi_s_rvalid; \
  assign i_``w_name``_axi_s_rready  = intf.rready; 
  
// =============================================================================================================
// macros that create the signals of AXI and assign them to the VIPs interface
// =============================================================================================================
`define create_and_bind_axi_read_slv(w_name, addr_w, data_w, id_w, len_w, intf) \
  bit  [ 3:0]        o_``w_name``_axi_m_arqos; \
  bit  [ addr_w-1:0] o_``w_name``_axi_m_araddr; \
  bit  [  1:0]       o_``w_name``_axi_m_arburst; \
  bit  [  3:0]       o_``w_name``_axi_m_arcache; \
  bit  [id_w-1:0]    o_``w_name``_axi_m_arid; \
  bit  [len_w-1:0]   o_``w_name``_axi_m_arlen; \
  bit                o_``w_name``_axi_m_arlock; \
  bit  [  2:0]       o_``w_name``_axi_m_arprot; \
  bit  [  2:0]       o_``w_name``_axi_m_arsize; \
  bit                o_``w_name``_axi_m_arvalid; \
  bit                i_``w_name``_axi_m_arready; \
  bit  [data_w-1:0]  i_``w_name``_axi_m_rdata; \
  bit  [id_w-1:0]    i_``w_name``_axi_m_rid; \
  bit                i_``w_name``_axi_m_rlast; \
  bit  [  1:0]       i_``w_name``_axi_m_rresp; \
  bit                i_``w_name``_axi_m_rvalid; \
  bit                o_``w_name``_axi_m_rready; \
  assign intf.araddr  = o_``w_name``_axi_m_araddr; \
  assign intf.arburst = o_``w_name``_axi_m_arburst; \
  assign intf.arcache = o_``w_name``_axi_m_arcache; \
  assign intf.arid    = o_``w_name``_axi_m_arid; \
  assign intf.arlen   = o_``w_name``_axi_m_arlen; \
  assign intf.arlock  = o_``w_name``_axi_m_arlock; \
  assign intf.arprot  = o_``w_name``_axi_m_arprot; \
  assign intf.arsize  = o_``w_name``_axi_m_arsize; \
  assign intf.arvalid = o_``w_name``_axi_m_arvalid; \
  assign i_``w_name``_axi_m_arready = intf.arready; \
  assign i_``w_name``_axi_m_rdata = intf.rdata; \
  assign i_``w_name``_axi_m_rid = intf.rid; \
  assign i_``w_name``_axi_m_rlast = intf.rlast; \
  assign i_``w_name``_axi_m_rresp = intf.rresp; \
  assign i_``w_name``_axi_m_rvalid = intf.rvalid; \
  assign intf.rready = o_``w_name``_axi_m_rready; 

`define create_and_bind_axi_write_mst(w_name, addr_w, data_w, id_w, len_w, intf) \
  bit  [ 3:0]         i_``w_name``_axi_s_awqos; \
  bit  [addr_w-1:0]   i_``w_name``_axi_s_awaddr; \
  bit  [  1:0]        i_``w_name``_axi_s_awburst; \
  bit  [  3:0]        i_``w_name``_axi_s_awcache; \
  bit  [id_w-1:0]     i_``w_name``_axi_s_awid; \
  bit  [len_w-1:0]    i_``w_name``_axi_s_awlen; \
  bit                 i_``w_name``_axi_s_awlock; \
  bit  [  2:0]        i_``w_name``_axi_s_awprot; \
  bit  [  2:0]        i_``w_name``_axi_s_awsize; \
  bit                 i_``w_name``_axi_s_awvalid; \
  bit                 o_``w_name``_axi_s_awready; \
  bit                 i_``w_name``_axi_s_bready; \
  bit  [id_w-1:0]     o_``w_name``_axi_s_bid; \
  bit  [  1:0]        o_``w_name``_axi_s_bresp; \
  bit                 o_``w_name``_axi_s_bvalid; \
  bit  [data_w-1:0]   i_``w_name``_axi_s_wdata; \
  bit                 i_``w_name``_axi_s_wlast; \
  bit  [data_w/8-1:0] i_``w_name``_axi_s_wstrb; \
  bit                 i_``w_name``_axi_s_wvalid; \
  bit                 o_``w_name``_axi_s_wready; \
  assign i_``w_name``_axi_s_awaddr = intf.awaddr; \
  assign i_``w_name``_axi_s_awburst = intf.awburst; \
  assign i_``w_name``_axi_s_awcache = intf.awcache; \
  assign i_``w_name``_axi_s_awid = intf.awid; \
  assign i_``w_name``_axi_s_awlen = intf.awlen; \
  assign i_``w_name``_axi_s_awlock = intf.awlock; \
  assign i_``w_name``_axi_s_awprot = intf.awprot; \
  assign i_``w_name``_axi_s_awsize = intf.awsize; \
  assign i_``w_name``_axi_s_awvalid = intf.awvalid; \
  assign intf.awready   = o_``w_name``_axi_s_awready; \
  assign i_``w_name``_axi_s_bready = intf.bready; \
  assign intf.bid       = o_``w_name``_axi_s_bid; \
  assign intf.bresp     = o_``w_name``_axi_s_bresp; \
  assign intf.bvalid    = o_``w_name``_axi_s_bvalid; \
  assign i_``w_name``_axi_s_wdata = intf.wdata; \
  assign i_``w_name``_axi_s_wlast = intf.wlast; \
  assign i_``w_name``_axi_s_wstrb = intf.wstrb; \
  assign i_``w_name``_axi_s_wvalid = intf.wvalid; \
  assign intf.wready    = o_``w_name``_axi_s_wready;

`define create_and_bind_axi_write_slv(w_name, addr_w, data_w, id_w, len_w, intf) \
  bit  [ 3:0]         o_``w_name``_axi_m_awqos; \
  bit  [addr_w-1:0]   o_``w_name``_axi_m_awaddr; \
  bit  [  1:0]        o_``w_name``_axi_m_awburst; \
  bit  [  3:0]        o_``w_name``_axi_m_awcache; \
  bit  [id_w-1:0]     o_``w_name``_axi_m_awid; \
  bit  [len_w-1:0]    o_``w_name``_axi_m_awlen; \
  bit                 o_``w_name``_axi_m_awlock; \
  bit  [  2:0]        o_``w_name``_axi_m_awprot; \
  bit  [  2:0]        o_``w_name``_axi_m_awsize; \
  bit                 o_``w_name``_axi_m_awvalid; \
  bit                 i_``w_name``_axi_m_awready; \
  bit                 o_``w_name``_axi_m_bready; \
  bit  [id_w-1:0]     i_``w_name``_axi_m_bid; \
  bit  [  1:0]        i_``w_name``_axi_m_bresp; \
  bit                 i_``w_name``_axi_m_bvalid; \
  bit  [data_w-1:0]   o_``w_name``_axi_m_wdata; \
  bit                 o_``w_name``_axi_m_wlast; \
  bit  [data_w/8-1:0] o_``w_name``_axi_m_wstrb; \
  bit                 o_``w_name``_axi_m_wvalid; \
  bit                 i_``w_name``_axi_m_wready; \
  assign  intf.awaddr  = o_``w_name``_axi_m_awaddr; \
  assign  intf.awburst = o_``w_name``_axi_m_awburst; \
  assign  intf.awcache = o_``w_name``_axi_m_awcache; \
  assign  intf.awid    = o_``w_name``_axi_m_awid; \
  assign  intf.awlen   = o_``w_name``_axi_m_awlen; \
  assign  intf.awlock  = o_``w_name``_axi_m_awlock; \
  assign  intf.awprot  = o_``w_name``_axi_m_awprot; \
  assign  intf.awsize  = o_``w_name``_axi_m_awsize; \
  assign  intf.awvalid = o_``w_name``_axi_m_awvalid; \
  assign  i_``w_name``_axi_m_awready = intf.awready; \
  assign  intf.bready = o_``w_name``_axi_m_bready; \
  assign  i_``w_name``_axi_m_bid = intf.bid; \
  assign  i_``w_name``_axi_m_bresp = intf.bresp; \
  assign  i_``w_name``_axi_m_bvalid = intf.bvalid; \
  assign  intf.wdata  = o_``w_name``_axi_m_wdata; \
  assign  intf.wlast  = o_``w_name``_axi_m_wlast; \
  assign  intf.wstrb  = o_``w_name``_axi_m_wstrb; \
  assign  intf.wvalid = o_``w_name``_axi_m_wvalid; \
  assign  i_``w_name``_axi_m_wready = intf.wready;

`define create_and_bind_axi_mst(w_name, addr_w, data_w, id_w, len_w, intf) \
`create_and_bind_axi_write_mst(w_name, addr_w, data_w, id_w, len_w, intf) \
`create_and_bind_axi_read_mst(w_name, addr_w, data_w, id_w, len_w, intf)

`define create_and_bind_axi_slv(w_name, addr_w, data_w, id_w, len_w, intf) \
`create_and_bind_axi_write_slv(w_name, addr_w, data_w, id_w, len_w, intf) \
`create_and_bind_axi_read_slv(w_name, addr_w, data_w, id_w, len_w, intf)


// =============================================================================================================
// macros that create the signals of APB and assign them to the VIPs interface
// =============================================================================================================
//there are only targets (slaves) on triton_noc
`define create_and_bind_apb3(w_name, addr_w, data_w, intf) \
bit  [ addr_w-1:0] o_``w_name``_paddr; \
bit                o_``w_name``_penable; \
bit  [ data_w-1:0] i_``w_name``_prdata; \
bit                i_``w_name``_pready; \
bit                o_``w_name``_psel; \
bit                i_``w_name``_pslverr; \
bit  [ data_w-1:0] o_``w_name``_pwdata; \
bit                o_``w_name``_pwrite; \
assign intf.paddr   = o_``w_name``_paddr; \
assign intf.penable = o_``w_name``_penable; \
assign intf.psel    = o_``w_name``_psel; \
assign intf.pwdata  = o_``w_name``_pwdata; \
assign intf.pwrite  = o_``w_name``_pwrite; \
assign i_``w_name``_prdata  = intf.prdata; \
assign i_``w_name``_pready  = intf.pready; \
assign i_``w_name``_pslverr = intf.pslverr; 


//create apb v4 signals
`define create_and_bind_apb4(w_name, addr_w, data_w, intf) \
`create_and_bind_apb3(w_name, addr_w, data_w, intf) \
bit [data_w/8-1:0] o_``w_name``_pstrb; \
bit          [2:0] o_``w_name``_pprot; \
assign intf.pprot = o_``w_name``_pprot; \
assign intf.pstrb = o_``w_name``_pstrb;

//`define conn_matrix_init_targ_addr_chk(req_addr, targ_sa, targ_ea) \
//if((req_addr >= targ_sa) && (req_addr <= targ_ea)) \


// MISC Decalrations //

  typedef enum {  e_aic_0_init_lt,      //LT_master[0] 
                  e_aic_1_init_lt,      //LT_master[1] 
                  e_aic_2_init_lt,      //LT_master[2] 
                  e_aic_3_init_lt,      //LT_master[3] 
                  e_aic_4_init_lt,      //LT_master[4] 
                  e_aic_5_init_lt,      //LT_master[5] 
                  e_aic_6_init_lt,      //LT_master[6] 
                  e_aic_7_init_lt,      //LT_master[7] 
                  e_sdma_0_init_lt,     //LT_master[8] 
                  e_sdma_1_init_lt,     //LT_master[9] 
                  e_pve_0_init_lt,      //LT_master[10] 
                  e_pve_1_init_lt,      //LT_master[11] 
                  e_apu_init_lt,        //LT_master[12] 
                  e_soc_mgmt_init_lt,   //LT_master[13] 
                  e_soc_periph_init_lt, //LT_master[14]
                  e_dcd_dec_0_init_mt,  //MT_master[15] 
                  e_dcd_dec_1_init_mt,  //MT_master[16] 
                  e_dcd_dec_2_init_mt,  //MT_master[17] 
                  e_dcd_mcu_init_lt,    //MT_master[18] 
                  e_apu_init_mt,        //MT_master[19] 
                  e_pcie_init_mt,       //MT_master[20]
                  e_aic_0_init_ht,      //HT_master[21] 
                  e_aic_1_init_ht,      //HT_master[22] 
                  e_aic_2_init_ht,      //HT_master[23] 
                  e_aic_3_init_ht,      //HT_master[24] 
                  e_aic_4_init_ht,      //HT_master[25] 
                  e_aic_5_init_ht,      //HT_master[26] 
                  e_aic_6_init_ht,      //HT_master[27] 
                  e_aic_7_init_ht,      //HT_master[28] 
                  e_sdma_0_init_ht_0,   //HT_master[29] 
                  e_sdma_0_init_ht_1,   //HT_master[30] 
                  e_sdma_1_init_ht_0,   //HT_master[31] 
                  e_sdma_1_init_ht_1,   //HT_master[32] 
                  e_pve_0_init_ht,      //HT_master[33] 
                  e_pve_1_init_ht       //HT_master[35] 
  } enoc_inits_e;

  typedef enum {  e_aic_0_targ_lt,        //LT_axi_slave[0] 
                  e_aic_1_targ_lt,        //LT_axi_slave[1] 
                  e_aic_2_targ_lt,        //LT_axi_slave[2] 
                  e_aic_3_targ_lt,        //LT_axi_slave[3] 
                  e_aic_4_targ_lt,        //LT_axi_slave[4] 
                  e_aic_5_targ_lt,        //LT_axi_slave[5] 
                  e_aic_6_targ_lt,        //LT_axi_slave[6] 
                  e_aic_7_targ_lt,        //LT_axi_slave[7] 
                  e_sdma_0_targ_lt,       //LT_axi_slave[8]     
                  e_sdma_1_targ_lt,       //LT_axi_slave[9]    
                  e_pve_0_targ_lt,        //LT_axi_slave[10] 
                  e_pve_1_targ_lt,        //LT_axi_slave[11] 
                  e_apu_targ_lt,          //LT_axi_slave[12] 
                  e_soc_mgmt_targ_lt,     //LT_axi_slave[13] 
                  e_soc_periph_targ_lt,   //LT_axi_slave[14] 
                  e_sys_spm_targ_lt,      //LT_axi_slave[15] 
                  e_pcie_targ_cfg_dbi,    //LT_axi_slave[16] 
                  e_lpddr_graph_0_targ_ht,//MT_axi_slave[17] 
                  e_lpddr_graph_1_targ_ht,//MT_axi_slave[18] 
                  e_lpddr_graph_2_targ_ht,//MT_axi_slave[19] 
                  e_lpddr_graph_3_targ_ht,//MT_axi_slave[20] 
                  e_pcie_targ_mt,         //MT_axi_slave[21] 
                  e_l2_0_targ_ht,         //HT_axi_slave[22] 
                  e_l2_1_targ_ht,         //HT_axi_slave[23] 
                  e_l2_2_targ_ht,         //HT_axi_slave[24] 
                  e_l2_3_targ_ht,         //HT_axi_slave[25] 
                  e_l2_4_targ_ht,         //HT_axi_slave[26] 
                  e_l2_5_targ_ht,         //HT_axi_slave[27] 
                  e_l2_6_targ_ht,         //HT_axi_slave[28] 
                  e_l2_7_targ_ht,         //HT_axi_slave[29] 
                  e_lpddr_ppp_0_targ_mt,  //HT_axi_slave[30] 
                  e_lpddr_ppp_1_targ_mt,  //HT_axi_slave[31] 
                  e_lpddr_ppp_2_targ_mt,  //HT_axi_slave[32] 
                  e_lpddr_ppp_3_targ_mt   //HT_axi_slave[33] //TODO: NOC_INT is AXI not APB, mv from apm_enums
  } enoc_axi_targs_e;

  typedef enum {  e_lpddr_graph_0_targ_cfg,     //apb3_slave[0] 
                  e_lpddr_graph_1_targ_cfg,     //apb3_slave[1] 
                  e_lpddr_graph_2_targ_cfg,     //apb3_slave[2] 
                  e_lpddr_graph_3_targ_cfg,     //apb3_slave[3] 
                  e_lpddr_ppp_0_targ_cfg,       //apb3_slave[4] 
                  e_lpddr_ppp_1_targ_cfg,       //apb3_slave[5] 
                  e_lpddr_ppp_2_targ_cfg,       //apb3_slave[6] 
                  e_lpddr_ppp_3_targ_cfg,       //apb3_slave[7] 
                  e_pcie_targ_cfg,              //apb3_slave[8] 
                  e_aic_0_targ_syscfg,          //apb4_slave[9] 
                  e_aic_1_targ_syscfg,          //apb4_slave[10] 
                  e_aic_2_targ_syscfg,          //apb4_slave[11] 
                  e_aic_3_targ_syscfg,          //apb4_slave[12] 
                  e_aic_4_targ_syscfg,          //apb4_slave[13] 
                  e_aic_5_targ_syscfg,          //apb4_slave[14] 
                  e_aic_6_targ_syscfg,          //apb4_slave[15] 
                  e_aic_7_targ_syscfg,          //apb4_slave[16] 
                  e_l2_0_targ_syscfg,           //apb4_slave[17] 
                  e_l2_1_targ_syscfg,           //apb4_slave[18] 
                  e_l2_2_targ_syscfg,           //apb4_slave[19] 
                  e_l2_3_targ_syscfg,           //apb4_slave[20] 
                  e_l2_4_targ_syscfg,           //apb4_slave[21] 
                  e_l2_5_targ_syscfg,           //apb4_slave[22] 
                  e_l2_6_targ_syscfg,           //apb4_slave[23] 
                  e_l2_7_targ_syscfg,           //apb4_slave[24]
                  e_lpddr_graph_0_targ_syscfg,  //apb4_slave[25] 
                  e_lpddr_graph_1_targ_syscfg,  //apb4_slave[26] 
                  e_lpddr_graph_2_targ_syscfg,  //apb4_slave[27] 
                  e_lpddr_graph_3_targ_syscfg,  //apb4_slave[28] 
                  e_lpddr_ppp_0_targ_syscfg,    //apb4_slave[29] 
                  e_lpddr_ppp_1_targ_syscfg,    //apb4_slave[30] 
                  e_lpddr_ppp_2_targ_syscfg,    //apb4_slave[31] 
                  e_lpddr_ppp_3_targ_syscfg,    //apb4_slave[32] 
                  e_pve_0_syscfg_lt,            //apb4_slave[33] 
                  e_pve_1_syscfg_lt,            //apb4_slave[34] 
                  e_pcie_targ_syscfg,           //apb4_slave[35] 
                  e_dcd_targ_syscfg,            //apb4_slave[36] 
                  e_apu_targ_syscfg,            //apb4_slave[37] 
                  e_soc_mgmt_targ_syscfg,       //apb4_slave[38] 
                  e_soc_periph_targ_syscfg,     //apb4_slave[39] 
                  e_sys_spm_targ_syscfg,        //apb4_slave[40] 
                  e_dcd_targ_cfg,               //apb4_slave[41] 
                  ddr_wpll_targ_syscfg          //apb4_slave[42] 
  } enoc_apb_targs_e;               

  typedef enum {  cc_l2_0_targ_ht,               //HT_axi_slave[0]  
                  cc_l2_1_targ_ht,               //HT_axi_slave[1]  
                  cc_l2_2_targ_ht,               //HT_axi_slave[2]  
                  cc_l2_3_targ_ht,               //HT_axi_slave[3]  
                  cc_l2_4_targ_ht,               //HT_axi_slave[4]  
                  cc_l2_5_targ_ht,               //HT_axi_slave[5]  
                  cc_l2_6_targ_ht,               //HT_axi_slave[6]  
                  cc_l2_7_targ_ht,               //HT_axi_slave[7]  
                  cc_lpddr_graph_0_targ_mt,      //MT_axi_slave[8]  
                  cc_lpddr_graph_1_targ_mt,      //MT_axi_slave[9]  
                  cc_lpddr_graph_2_targ_mt,      //MT_axi_slave[10] 
                  cc_lpddr_graph_3_targ_mt,      //MT_axi_slave[11] 
                  cc_lpddr_ppp_0_targ_ht,        //HT_axi_slave[12] 
                  cc_lpddr_ppp_1_targ_ht,        //HT_axi_slave[13] 
                  cc_lpddr_ppp_2_targ_ht,        //HT_axi_slave[14] 
                  cc_lpddr_ppp_3_targ_ht,        //HT_axi_slave[15] 
                  cc_pcie_targ_mt,               //MT_axi_slave[16] 
                  cc_aic_0_targ_lt,              //LT_axi_slave[17]
                  cc_aic_1_targ_lt,              //LT_axi_slave[18]
                  cc_aic_2_targ_lt,              //LT_axi_slave[19]
                  cc_aic_3_targ_lt,              //LT_axi_slave[20]
                  cc_aic_4_targ_lt,              //LT_axi_slave[21]
                  cc_aic_5_targ_lt,              //LT_axi_slave[22]
                  cc_aic_6_targ_lt,              //LT_axi_slave[23]
                  cc_aic_7_targ_lt,              //LT_axi_slave[24]
                  cc_sdma_0_targ_lt,             //LT_axi_slave[25]    
                  cc_sdma_1_targ_lt,             //LT_axi_slave[26]   
                  cc_pve_0_targ_lt,              //LT_axi_slave[27] 
                  cc_pve_1_targ_lt,              //LT_axi_slave[28] 
                  cc_apu_targ_lt,                //LT_axi_slave[29] 
                  cc_dcd_targ_cfg,                 //apb4_slave[30] 
                  cc_soc_mgmt_targ_lt,           //LT_axi_slave[31] 
                  cc_soc_periph_targ_lt,         //LT_axi_slave[32] 
                  cc_sys_spm_targ_lt,            //LT_axi_slave[33] 
                  cc_lpddr_graph_0_targ_cfg,       //apb3_slave[34] 
                  cc_lpddr_graph_1_targ_cfg,       //apb3_slave[35] 
                  cc_lpddr_graph_2_targ_cfg,       //apb3_slave[36] 
                  cc_lpddr_graph_3_targ_cfg,       //apb3_slave[37] 
                  cc_lpddr_ppp_0_targ_cfg,         //apb3_slave[38] 
                  cc_lpddr_ppp_1_targ_cfg,         //apb3_slave[39] 
                  cc_lpddr_ppp_2_targ_cfg,         //apb3_slave[40] 
                  cc_lpddr_ppp_3_targ_cfg,         //apb3_slave[41] 
                  cc_pcie_targ_cfg,                //apb3_slave[42] 
                  cc_aic_0_targ_syscfg,            //apb4_slave[43] 
                  cc_aic_1_targ_syscfg,            //apb4_slave[44] 
                  cc_aic_2_targ_syscfg,            //apb4_slave[45] 
                  cc_aic_3_targ_syscfg,            //apb4_slave[46] 
                  cc_aic_4_targ_syscfg,            //apb4_slave[47] 
                  cc_aic_5_targ_syscfg,            //apb4_slave[48] 
                  cc_aic_6_targ_syscfg,            //apb4_slave[49] 
                  cc_aic_7_targ_syscfg,            //apb4_slave[50] 
                  cc_l2_0_targ_syscfg,             //apb4_slave[51] 
                  cc_l2_1_targ_syscfg,             //apb4_slave[52] 
                  cc_l2_2_targ_syscfg,             //apb4_slave[53] 
                  cc_l2_3_targ_syscfg,             //apb4_slave[54] 
                  cc_l2_4_targ_syscfg,             //apb4_slave[55] 
                  cc_l2_5_targ_syscfg,             //apb4_slave[56] 
                  cc_l2_6_targ_syscfg,             //apb4_slave[57] 
                  cc_l2_7_targ_syscfg,             //apb4_slave[58]
                  cc_lpddr_graph_0_targ_syscfg,    //apb4_slave[59] 
                  cc_lpddr_graph_1_targ_syscfg,    //apb4_slave[60] 
                  cc_lpddr_graph_2_targ_syscfg,    //apb4_slave[61] 
                  cc_lpddr_graph_3_targ_syscfg,    //apb4_slave[62] 
                  cc_lpddr_ppp_0_targ_syscfg,      //apb4_slave[63] 
                  cc_lpddr_ppp_1_targ_syscfg,      //apb4_slave[64] 
                  cc_lpddr_ppp_2_targ_syscfg,      //apb4_slave[65] 
                  cc_lpddr_ppp_3_targ_syscfg,      //apb4_slave[66] 
                  cc_pcie_targ_syscfg,             //apb4_slave[67] 
                  cc_pve_0_syscfg_lt,              //apb4_slave[68] 
                  cc_pve_1_syscfg_lt,              //apb4_slave[69] 
                  cc_apu_targ_syscfg,              //apb4_slave[70] 
                  cc_dcd_targ_syscfg,              //apb4_slave[71] 
                  cc_soc_mgmt_targ_syscfg,         //apb4_slave[72] 
                  cc_soc_periph_targ_syscfg,       //apb4_slave[73] 
                  cc_sys_spm_targ_syscfg,          //apb4_slave[74] 
                  cc_sdma_0_targ_syscfg,           //apb4_slave[75] 
                  cc_sdma_1_targ_syscfg,           //apb4_slave[76] 
                  cc_pcie_targ_cfg_dbi,            //LT_AXI_SLAVE[77] 
                  cc_noc_csr_targ_int              //axi_slave[78] 
  } enoc_all_targs_e;

  typedef int unsigned uint32_t;

  //TODO: define custom parameters for each Initiator&Target
  `define AXI_LP_ADDR_WIDTH              40
  `define AXI_LP_DATA_WIDTH              64
  `define AXI_HP_ADDR_WIDTH              40
  `define AXI_HP_DATA_WIDTH              512
  `define AXI_TRANSACTION_BURST_SIZE_8   0
  `define AXI_TRANSACTION_BURST_SIZE_16  1
  `define AXI_TRANSACTION_BURST_SIZE_32  2
  `define AXI_TRANSACTION_BURST_SIZE_64  3
  `define AXI_TRANSACTION_BURST_SIZE_128 4
  `define AXI_TRANSACTION_BURST_SIZE_256 5
  `define AXI_TRANSACTION_BURST_SIZE_512 6
  `define AXI_TRANSACTION_BURST_FIXED    0
  `define AXI_TRANSACTION_BURST_INCR     1
  `define AXI_TRANSACTION_BURST_WRAP     2
  `define AXI_OKAY_RESPONSE              0
  `define AXI_EXOKAY_RESPONSE            1
  `define AXI_SLVERR_RESPONSE            2
  `define AXI_DECERR_RESPONSE            3
  `define AXI_MAX_DELAY                 16

  //TODO: define custom parameters for each Initiator&Target
  `define P_APB_ADDR_WIDTH                  64
  `define P_APB_DATA_WIDTH                  32
  `define P_APB_BE_WIDTH                    (`SVT_APB_MAX_DATA_WIDTH / 8)
  `define P_MST_TO_SLV_CNTRL_WIDTH          `P_APB_DATA_WIDTH + `P_APB_ADDR_WIDTH + `P_APB_BE_WIDTH + 1
  `define P_SLV_TO_MST_CNTRL_WIDTH          `P_APB_DATA_WIDTH + 1

  `define P_APB_TRANSACTION_MAX    2048
  `define P_APB_READY_TIMEOUT_MAX  8
  `define P_MST_RST_ACKN_BIT       uint32_t'(0)
   
  `define HP_STRB_WIDTH   64 
  `define MP_STRB_WIDTH   16 
  `define LP_STRB_WIDTH   8 
  
  `define MIN_DELAY 500
  `define MED_DELAY 2500
  `define MAX_DELAY 5000
 
  // ****************************************************************************
  // defines for Europa's TARGET's Start & End ADDRs
  // ****************************************************************************
  `define APU_TARG_SA                           40'h00000000
  `define APU_TARG_EA                           40'h01FFFFFF
  `define SOC_MGMT_TARG_SA                      40'h02000000
  `define SOC_MGMT_TARG_EA                      40'h02FFFFFF
  `define SOC_PERIPH_TARG_SA                    40'h03000000
  `define SOC_PERIPH_TARG_EA                    40'h03FFFFFF
  `define PCIE_DBI_TARG_SA                      40'h04000000
  `define PCIE_DBI_TARG_EA                      40'h043FFFFF
  `define NOC_INT_TARG_SA                       40'h04500000
  `define NOC_INT_TARG_EA                       40'h0451FFFF
  `define SDMA_0_TARG_SA                        40'h06000000
  `define SDMA_0_TARG_EA                        40'h0607FFFF
  `define SDMA_1_TARG_SA                        40'h06080000
  `define SDMA_1_TARG_EA                        40'h060FFFFF
  `define SYS_SPM_TARG_SA                       40'h07000000
  `define SYS_SPM_TARG_EA                       40'h077FFFFF
  `define L2_MODULE_0_TARG_SA                   40'h08000000
  `define L2_MODULE_0_TARG_EA                   40'h08FFFFFF
  `define L2_MODULE_1_TARG_SA                   40'h09000000
  `define L2_MODULE_1_TARG_EA                   40'h09FFFFFF
  `define L2_MODULE_2_TARG_SA                   40'h0A000000
  `define L2_MODULE_2_TARG_EA                   40'h0AFFFFFF
  `define L2_MODULE_3_TARG_SA                   40'h0B000000
  `define L2_MODULE_3_TARG_EA                   40'h0BFFFFFF
  `define L2_MODULE_4_TARG_SA                   40'h0C000000
  `define L2_MODULE_4_TARG_EA                   40'h0CFFFFFF
  `define L2_MODULE_5_TARG_SA                   40'h0D000000
  `define L2_MODULE_5_TARG_EA                   40'h0DFFFFFF
  `define L2_MODULE_6_TARG_SA                   40'h0E000000
  `define L2_MODULE_6_TARG_EA                   40'h0EFFFFFF
  `define L2_MODULE_7_TARG_SA                   40'h0F000000
  `define L2_MODULE_7_TARG_EA                   40'h0FFFFFFF
  `define AICORE_0_TARG_SA                      40'h10000000
  `define AICORE_0_TARG_EA                      40'h1FFFFFFF
  `define AICORE_1_TARG_SA                      40'h20000000
  `define AICORE_1_TARG_EA                      40'h2FFFFFFF
  `define AICORE_2_TARG_SA                      40'h30000000
  `define AICORE_2_TARG_EA                      40'h3FFFFFFF
  `define AICORE_3_TARG_SA                      40'h40000000
  `define AICORE_3_TARG_EA                      40'h4FFFFFFF
  `define AICORE_4_TARG_SA                      40'h50000000
  `define AICORE_4_TARG_EA                      40'h5FFFFFFF
  `define AICORE_5_TARG_SA                      40'h60000000
  `define AICORE_5_TARG_EA                      40'h6FFFFFFF
  `define AICORE_6_TARG_SA                      40'h70000000
  `define AICORE_6_TARG_EA                      40'h7FFFFFFF
  `define AICORE_7_TARG_SA                      40'h80000000
  `define AICORE_7_TARG_EA                      40'h8FFFFFFF
  `define PVE_0_TARG_SA                         40'h90000000
  `define PVE_0_TARG_EA                         40'h9FFFFFFF
  `define PVE_1_TARG_SA                         40'hA0000000
  `define PVE_1_TARG_EA                         40'hAFFFFFFF
  `define DDR_0_GRAPH_TARG_SA                   40'h2000000000
  `define DDR_0_GRAPH_TARG_EA                   40'h27FFFFFFFF
  `define DDR_1_PPP_TARG_SA                     40'h2800000000
  `define DDR_1_PPP_TARG_EA                     40'h2FFFFFFFFF
  `define PCIE_HOST_MT_TARG_SA                  40'h3000000000
  `define PCIE_HOST_MT_TARG_EA                  40'h3FFFFFFFFF
  `define DCD_CFG_TARG_SA                       40'hB0000000
  `define DCD_CFG_TARG_EA                       40'hB00FFFFF
  `define DDR_0_CTRL_GRAPH_0_CFG_TARG_SA        40'h100000000
  `define DDR_0_CTRL_GRAPH_0_CFG_TARG_EA        40'h1FFFFFFFF
  `define DDR_1_CTRL_GRAPH_1_CFG_TARG_SA        40'h200000000
  `define DDR_1_CTRL_GRAPH_1_CFG_TARG_EA        40'h2FFFFFFFF
  `define DDR_2_CTRL_GRAPH_2_CFG_TARG_SA        40'h300000000
  `define DDR_2_CTRL_GRAPH_2_CFG_TARG_EA        40'h3FFFFFFFF
  `define DDR_3_CTRL_GRAPH_3_CFG_TARG_SA        40'h400000000
  `define DDR_3_CTRL_GRAPH_3_CFG_TARG_EA        40'h4FFFFFFFF
  `define DDR_4_CTRL_PPP_0_CFG_TARG_SA          40'h500000000
  `define DDR_4_CTRL_PPP_0_CFG_TARG_EA          40'h5FFFFFFFF
  `define DDR_5_CTRL_PPP_1_CFG_TARG_SA          40'h600000000
  `define DDR_5_CTRL_PPP_1_CFG_TARG_EA          40'h6FFFFFFFF
  `define DDR_6_CTRL_PPP_2_CFG_TARG_SA          40'h700000000
  `define DDR_6_CTRL_PPP_2_CFG_TARG_EA          40'h7FFFFFFFF
  `define DDR_7_CTRL_PPP_3_CFG_TARG_SA          40'h800000000
  `define DDR_7_CTRL_PPP_3_CFG_TARG_EA          40'h8FFFFFFFF
  `define PCIE_CFG_TARG_SA                      40'h04400000
  `define PCIE_CFG_TARG_EA                      40'h044FFFFF
  `define SYS_CFG_AICORE_0_AO_CSR_TARG_SA       40'h05000000
  `define SYS_CFG_AICORE_0_AO_CSR_TARG_EA       40'h0500FFFF
  `define SYS_CFG_AICORE_1_AO_CSR_TARG_SA       40'h05010000
  `define SYS_CFG_AICORE_1_AO_CSR_TARG_EA       40'h0501FFFF
  `define SYS_CFG_AICORE_2_AO_CSR_TARG_SA       40'h05020000
  `define SYS_CFG_AICORE_2_AO_CSR_TARG_EA       40'h0502FFFF
  `define SYS_CFG_AICORE_3_AO_CSR_TARG_SA       40'h05030000
  `define SYS_CFG_AICORE_3_AO_CSR_TARG_EA       40'h0503FFFF
  `define SYS_CFG_AICORE_4_AO_CSR_TARG_SA       40'h05040000
  `define SYS_CFG_AICORE_4_AO_CSR_TARG_EA       40'h0504FFFF
  `define SYS_CFG_AICORE_5_AO_CSR_TARG_SA       40'h05050000
  `define SYS_CFG_AICORE_5_AO_CSR_TARG_EA       40'h0505FFFF
  `define SYS_CFG_AICORE_6_AO_CSR_TARG_SA       40'h05060000
  `define SYS_CFG_AICORE_6_AO_CSR_TARG_EA       40'h0506FFFF
  `define SYS_CFG_AICORE_7_AO_CSR_TARG_SA       40'h05070000
  `define SYS_CFG_AICORE_7_AO_CSR_TARG_EA       40'h0507FFFF
  `define SYS_CFG_L2_MODULE_0_AO_CSR_TARG_SA    40'h05080000
  `define SYS_CFG_L2_MODULE_0_AO_CSR_TARG_EA    40'h0508FFFF
  `define SYS_CFG_L2_MODULE_1_AO_CSR_TARG_SA    40'h05090000
  `define SYS_CFG_L2_MODULE_1_AO_CSR_TARG_EA    40'h0509FFFF
  `define SYS_CFG_L2_MODULE_2_AO_CSR_TARG_SA    40'h050A0000
  `define SYS_CFG_L2_MODULE_2_AO_CSR_TARG_EA    40'h050AFFFF
  `define SYS_CFG_L2_MODULE_3_AO_CSR_TARG_SA    40'h050B0000
  `define SYS_CFG_L2_MODULE_3_AO_CSR_TARG_EA    40'h050BFFFF
  `define SYS_CFG_L2_MODULE_4_AO_CSR_TARG_SA    40'h050C0000
  `define SYS_CFG_L2_MODULE_4_AO_CSR_TARG_EA    40'h050CFFFF
  `define SYS_CFG_L2_MODULE_5_AO_CSR_TARG_SA    40'h050D0000
  `define SYS_CFG_L2_MODULE_5_AO_CSR_TARG_EA    40'h050DFFFF
  `define SYS_CFG_L2_MODULE_6_AO_CSR_TARG_SA    40'h050E0000
  `define SYS_CFG_L2_MODULE_6_AO_CSR_TARG_EA    40'h050EFFFF
  `define SYS_CFG_L2_MODULE_7_AO_CSR_TARG_SA    40'h050F0000
  `define SYS_CFG_L2_MODULE_7_AO_CSR_TARG_EA    40'h050FFFFF
  `define SYS_CFG_DDR_0_GRAPH_0_AO_CSR_TARG_SA  40'h05100000
  `define SYS_CFG_DDR_0_GRAPH_0_AO_CSR_TARG_EA  40'h0510FFFF
  `define SYS_CFG_DDR_1_GRAPH_1_AO_CSR_TARG_SA  40'h05110000
  `define SYS_CFG_DDR_1_GRAPH_1_AO_CSR_TARG_EA  40'h0511FFFF
  `define SYS_CFG_DDR_2_GRAPH_2_AO_CSR_TARG_SA  40'h05120000
  `define SYS_CFG_DDR_2_GRAPH_2_AO_CSR_TARG_EA  40'h0512FFFF
  `define SYS_CFG_DDR_3_GRAPH_3_AO_CSR_TARG_SA  40'h05130000
  `define SYS_CFG_DDR_3_GRAPH_3_AO_CSR_TARG_EA  40'h0513FFFF
  `define SYS_CFG_DDR_4_PPP_0_AO_CSR_TARG_SA    40'h05140000
  `define SYS_CFG_DDR_4_PPP_0_AO_CSR_TARG_EA    40'h0514FFFF
  `define SYS_CFG_DDR_5_PPP_1_AO_CSR_TARG_SA    40'h05150000
  `define SYS_CFG_DDR_5_PPP_1_AO_CSR_TARG_EA    40'h0515FFFF
  `define SYS_CFG_DDR_6_PPP_2_AO_CSR_TARG_SA    40'h05160000
  `define SYS_CFG_DDR_6_PPP_2_AO_CSR_TARG_EA    40'h0516FFFF
  `define SYS_CFG_DDR_7_PPP_3_AO_CSR_TARG_SA    40'h05170000
  `define SYS_CFG_DDR_7_PPP_3_AO_CSR_TARG_EA    40'h0517FFFF
  `define SYS_CFG_SYS_SPM_AO_CSR_TARG_SA        40'h05180000
  `define SYS_CFG_SYS_SPM_AO_CSR_TARG_EA        40'h0518FFFF
  `define SYS_CFG_APU_AO_CSR_TARG_SA            40'h05190000
  `define SYS_CFG_APU_AO_CSR_TARG_EA            40'h0519FFFF
  `define SYS_CFG_DDR_WEST_PLL_AO_CSR_TARG_SA   40'h051A0000
  `define SYS_CFG_DDR_WEST_PLL_AO_CSR_TARG_EA   40'h051AFFFF
  `define SYS_CFG_SOC_PERIPH_AO_CSR_TARG_SA     40'h051B0000
  `define SYS_CFG_SOC_PERIPH_AO_CSR_TARG_EA     40'h051BFFFF
  `define SYS_CFG_SDMA_0_AO_CSR_TARG_SA         40'h051C0000
  `define SYS_CFG_SDMA_0_AO_CSR_TARG_EA         40'h051CFFFF
  `define SYS_CFG_SDMA_1_AO_CSR_TARG_SA         40'h051D0000
  `define SYS_CFG_SDMA_1_AO_CSR_TARG_EA         40'h051DFFFF
  `define SYS_CFG_PCIE_AO_CSR_TARG_SA           40'h051E0000
  `define SYS_CFG_PCIE_AO_CSR_TARG_EA           40'h051EFFFF
  `define SYS_CFG_DECODER_AO_CSR_TARG_SA        40'h051F0000
  `define SYS_CFG_DECODER_AO_CSR_TARG_EA        40'h051FFFFF
  `define SYS_CFG_PVE_0_AO_CSR_TARG_SA          40'h05200000
  `define SYS_CFG_PVE_0_AO_CSR_TARG_EA          40'h0520FFFF
  `define SYS_CFG_PVE_1_AO_CSR_TARG_SA          40'h05210000
  `define SYS_CFG_PVE_1_AO_CSR_TARG_EA          40'h0521FFFF
  `define SYS_CFG_SOC_MGMT_CLOCK_GEN_TARG_SA    40'h05300000
  `define SYS_CFG_SOC_MGMT_CLOCK_GEN_TARG_EA    40'h0530FFFF
  `define SYS_CFG_SOC_MGMT_RESET_GEN_TARG_SA    40'h05310000
  `define SYS_CFG_SOC_MGMT_RESET_GEN_TARG_EA    40'h0531FFFF
  `define SYS_CFG_SOC_MGMT_NOC_AO_CSR_TARG_SA   40'h05320000
  `define SYS_CFG_SOC_MGMT_NOC_AO_CSR_TARG_EA   40'h0532FFFF
  `define SYS_CFG_SOC_MGMT_AO_CSR_TARG_SA       40'h05330000
  `define SYS_CFG_SOC_MGMT_AO_CSR_TARG_EA       40'h0534FFFF
  `define SYS_CFG_RESERVED_0_TARG_SA            40'h05220000
  `define SYS_CFG_RESERVED_0_TARG_EA            40'h052FFFFF
  `define SYS_CFG_RESERVED_1_TARG_SA            40'h05350000
  `define SYS_CFG_RESERVED_1_TARG_EA            40'h05FFFFFF
  `define RESERVED_0_TARG_SA                    40'h06100000
  `define RESERVED_0_TARG_EA                    40'h06FFFFFF
  `define RESERVED_1_TARG_SA                    40'h07800000
  `define RESERVED_1_TARG_EA                    40'h07FFFFFF
  `define RESERVED_2_TARG_SA                    40'hB0100000
  `define RESERVED_2_TARG_EA                    40'hBFFFFFFF
  `define RESERVED_3_TARG_SA                    40'hC0000000
  `define RESERVED_3_TARG_EA                    40'hFFFFFFFF
  `define RESERVED_4_TARG_SA                    40'h900000000
  `define RESERVED_4_TARG_EA                    40'h1FFFFFFFFF
  `define RESERVED_5_TARG_SA                    40'h4000000000
  `define RESERVED_5_TARG_EA                    40'hFFFFFFFFFF
  
  // ****************************************************************************
  // Enumerated Types
  // ****************************************************************************
  typedef enum bit [3:0] {
    BURST_SIZE_8BIT    = `AXI_TRANSACTION_BURST_SIZE_8,
    BURST_SIZE_16BIT   = `AXI_TRANSACTION_BURST_SIZE_16,
    BURST_SIZE_32BIT   = `AXI_TRANSACTION_BURST_SIZE_32,
    BURST_SIZE_64BIT   = `AXI_TRANSACTION_BURST_SIZE_64,
    BURST_SIZE_128BIT  = `AXI_TRANSACTION_BURST_SIZE_128,
    BURST_SIZE_256BIT  = `AXI_TRANSACTION_BURST_SIZE_256,
    BURST_SIZE_512BIT  = `AXI_TRANSACTION_BURST_SIZE_512
  } burst_size_t;

  typedef enum bit[1:0]{
    FIXED = `AXI_TRANSACTION_BURST_FIXED,
    INCR  = `AXI_TRANSACTION_BURST_INCR,
    WRAP  = `AXI_TRANSACTION_BURST_WRAP
  } burst_type_t;

  typedef enum bit[5:0]{
    BURST_LENGTH_1  = 1,
    BURST_LENGTH_2  = 2,
    BURST_LENGTH_4  = 4,
    BURST_LENGTH_8  = 8,
    BURST_LENGTH_16 = 16
  } burst_length_t;

  typedef enum bit [1:0] {
    OKAY    = `AXI_OKAY_RESPONSE,
    EXOKAY  = `AXI_EXOKAY_RESPONSE,
    SLVERR  = `AXI_SLVERR_RESPONSE,
    DECERR  = `AXI_DECERR_RESPONSE
  } resp_type_t;



`define uvm_numbered_analysis_imp_decl(SFX) \
class uvm_analysis_imp``SFX #(type T=int, type IMP=int) \
  extends uvm_port_base #(uvm_tlm_if_base #(T,T)); \
  int imp_id = -1; \
  `UVM_IMP_COMMON(`UVM_TLM_ANALYSIS_MASK,`"uvm_analysis_imp``SFX`",IMP) \
  function void write( input T t); \
    if (imp_id < 0) begin \
      uvm_top.uvm_report_fatal(get_type_name(), "imp_id has not been initialized!", UVM_NONE, `uvm_file, `uvm_line); \
    end \
    m_imp.write``SFX( t, imp_id); \
  endfunction \
  \
endclass    

