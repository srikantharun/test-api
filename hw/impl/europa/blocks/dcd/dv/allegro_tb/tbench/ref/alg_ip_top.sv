



module alg_ip_top #(
  parameter REMOVE_ID  = 1,
  parameter USE_HW_FAULT = 1,
  parameter USE_HW_VIP = 1 ) (

  input  logic         sys_clk          , 
  input  logic         sys_rstn         ,
  
  input  logic         mcu_clk          , 
  input  logic         mcu_rstn         ,
  
  input  logic         debug_clk        ,
  input  logic         debug_sys_rst    ,
  input  logic         debug_rst        ,
  input  logic         debug_capture    ,
  input  logic [7:0]   debug_reg_en     ,
  input  logic         debug_shift      ,
  input  logic         debug_tdi        ,
  output logic         debug_tdo        ,
  input  logic         debug_update     ,
  
  input  logic         l2c_clk          , 
  input  logic         l2c_rstn         ,
  output logic [356:0] l2c_tx           ,
  input  logic [356:0] l2c_rx           ,
  
  input  logic         prstn            ,
  output logic         prstn_out        ,
  input  logic         pclk             , 
  output logic         pclk_out         ,
  input  logic [31:0]  paddr            ,
  input  logic         penable          ,
  output logic [31:0]  prdata           ,
  output logic         pready           ,
  input  logic         psel             ,
  output logic         pslverr          ,
  input  logic [31:0]  pwdata           ,
  input  logic         pwrite           ,
  output logic         pintreq          ,
  
  input  logic         aclk             , 
  input  logic         aclk_nobuf       , 
  input  logic         arstn            ,
  output logic [63:0]  araddr0          ,
  output logic [1:0]   arburst0         ,
  output logic [4:0]   arid0            ,
  output logic [7:0]   arlen0           ,
  input  logic         arready0         ,
  output logic [2:0]   arsize0          ,
  output logic         arvalid0         ,
  output logic [63:0]  awaddr0          ,
  output logic [1:0]   awburst0         ,
  output logic [4:0]   awid0            ,
  output logic [7:0]   awlen0           ,
  input  logic         awready0         ,
  output logic [2:0]   awsize0          ,
  output logic         awvalid0         ,
  output logic         bready0          ,
  input  logic         bvalid0          ,
  input  logic         bresp0           ,
  input  logic [4:0]   bid0             ,
  input  logic [128-1:0] rdata0           ,
  input  logic [4:0]   rid0             ,
  input  logic         rlast0           ,
  output logic         rready0          ,
  input  logic         rvalid0          ,
  input  logic         rresp0           ,
  output logic [128-1:0] wdata0           ,
  output logic [(128/8)-1:0]  wstrb0           ,
  output logic         wlast0           ,
  input  logic         wready0          ,
  output logic         wvalid0          ,
  output logic [63:0]  araddr1          ,
  output logic [1:0]   arburst1         ,
  output logic [4:0]   arid1            ,
  output logic [7:0]   arlen1           ,
  input  logic         arready1         ,
  output logic [2:0]   arsize1          ,
  output logic         arvalid1         ,
  output logic [63:0]  awaddr1          ,
  output logic [1:0]   awburst1         ,
  output logic [4:0]   awid1            ,
  output logic [7:0]   awlen1           ,
  input  logic         awready1         ,
  output logic [2:0]   awsize1          ,
  output logic         awvalid1         ,
  output logic         bready1          ,
  input  logic         bvalid1          ,
  input  logic         bresp1           ,
  input  logic [4:0]   bid1             ,
  input  logic [128-1:0] rdata1           ,
  input  logic [4:0]   rid1             ,
  input  logic         rlast1           ,
  output logic         rready1          ,
  input  logic         rvalid1          ,
  input  logic         rresp1           ,
  output logic [128-1:0] wdata1           ,
  output logic [(128/8)-1:0]  wstrb1           ,
  output logic         wlast1           ,
  input  logic         wready1          ,
  output logic         wvalid1          ,
  output logic [63:0]  araddr3          ,
  output logic [1:0]   arburst3         ,
  output logic [4:0]   arid3            ,
  output logic [7:0]   arlen3           ,
  input  logic         arready3         ,
  output logic [2:0]   arsize3          ,
  output logic         arvalid3         ,
  output logic [63:0]  awaddr3          ,
  output logic [1:0]   awburst3         ,
  output logic [4:0]   awid3            ,
  output logic [7:0]   awlen3           ,
  input  logic         awready3         ,
  output logic [2:0]   awsize3          ,
  output logic         awvalid3         ,
  output logic         bready3          ,
  input  logic         bvalid3          ,
  input  logic         bresp3           ,
  input  logic [4:0]   bid3             ,
  input  logic [128-1:0] rdata3           ,
  input  logic [4:0]   rid3             ,
  input  logic         rlast3           ,
  output logic         rready3          ,
  input  logic         rvalid3          ,
  input  logic         rresp3           ,
  output logic [128-1:0] wdata3           ,
  output logic [(128/8)-1:0]  wstrb3           ,
  output logic         wlast3           ,
  input  logic         wready3          ,
  output logic         wvalid3          ,
  output logic [63:0]  araddr4          ,
  output logic [1:0]   arburst4         ,
  output logic [4:0]   arid4            ,
  output logic [7:0]   arlen4           ,
  input  logic         arready4         ,
  output logic [2:0]   arsize4          ,
  output logic         arvalid4         ,
  output logic [63:0]  awaddr4          ,
  output logic [1:0]   awburst4         ,
  output logic [4:0]   awid4            ,
  output logic [7:0]   awlen4           ,
  input  logic         awready4         ,
  output logic [2:0]   awsize4          ,
  output logic         awvalid4         ,
  output logic         bready4          ,
  input  logic         bvalid4          ,
  input  logic         bresp4           ,
  input  logic [4:0]   bid4             ,
  input  logic [128-1:0] rdata4           ,
  input  logic [4:0]   rid4             ,
  input  logic         rlast4           ,
  output logic         rready4          ,
  input  logic         rvalid4          ,
  input  logic         rresp4           ,
  output logic [128-1:0] wdata4           ,
  output logic [(128/8)-1:0]  wstrb4           ,
  output logic         wlast4           ,
  input  logic         wready4          ,
  output logic         wvalid4          ,
  
  output logic [63:0]  araddr2          ,
  output logic [1:0]   arburst2         ,
  output logic [4:0]   arid2            ,
  output logic [7:0]   arlen2           ,
  input  logic         arready2         ,
  output logic [2:0]   arsize2          ,
  output logic         arvalid2         ,
  output logic [63:0]  awaddr2          ,
  output logic [1:0]   awburst2         ,
  output logic [4:0]   awid2            ,
  output logic [7:0]   awlen2           ,
  input  logic         awready2         ,
  output logic [2:0]   awsize2          ,
  output logic         awvalid2         ,
  output logic         bready2          ,
  input  logic         bvalid2          ,
  input  logic         bresp2           ,
  input  logic [4:0]   bid2             ,
  input  logic [128-1:0] rdata2,
  input  logic [4:0]   rid2             ,
  input  logic         rlast2           ,
  output logic         rready2          ,
  input  logic         rvalid2          ,
  input  logic         rresp2           ,
  output logic [128-1:0] wdata2,
  output logic         wlast2           ,
  output logic [(128/8)-1:0] wstrb2,
  input  logic         wready2          ,
  output logic         wvalid2          ,
  
  output logic [63:0]  m_axi_dc_araddr  ,
  output logic [1:0]   m_axi_dc_arburst ,
  output logic [3:0]   m_axi_dc_arcache ,
  output logic         m_axi_dc_arid    ,
  output logic [7:0]   m_axi_dc_arlen   ,
  output logic         m_axi_dc_arlock  ,
  output logic [2:0]   m_axi_dc_arprot  ,
  output logic [3:0]   m_axi_dc_arqos   ,
  input  logic         m_axi_dc_arready ,
  output logic [2:0]   m_axi_dc_arsize  ,
  output logic         m_axi_dc_arvalid ,
  output logic [63:0]  m_axi_dc_awaddr  ,
  output logic [1:0]   m_axi_dc_awburst ,
  output logic [3:0]   m_axi_dc_awcache ,
  output logic         m_axi_dc_awid    ,
  output logic [7:0]   m_axi_dc_awlen   ,
  output logic         m_axi_dc_awlock  ,
  output logic [2:0]   m_axi_dc_awprot  ,
  output logic [3:0]   m_axi_dc_awqos   ,
  input  logic         m_axi_dc_awready ,
  output logic [2:0]   m_axi_dc_awsize  ,
  output logic         m_axi_dc_awvalid ,
  input  logic         m_axi_dc_bid     ,
  output logic         m_axi_dc_bready  ,
  input  logic [1:0]   m_axi_dc_bresp   ,
  input  logic         m_axi_dc_bvalid  ,
  input  logic [31:0]  m_axi_dc_rdata   ,
  input  logic         m_axi_dc_rid     ,
  input  logic         m_axi_dc_rlast   ,
  output logic         m_axi_dc_rready  ,
  input  logic [1:0]   m_axi_dc_rresp   ,
  input  logic         m_axi_dc_rvalid  ,
  output logic [31:0]  m_axi_dc_wdata   ,
  output logic         m_axi_dc_wlast   ,
  input  logic         m_axi_dc_wready  ,
  output logic [3:0]   m_axi_dc_wstrb   ,
  output logic         m_axi_dc_wvalid  ,
  
  output logic [63:0]  m_axi_ic_araddr  ,
  output logic [1:0]   m_axi_ic_arburst ,
  output logic [3:0]   m_axi_ic_arcache ,
  output logic         m_axi_ic_arid    ,
  output logic [7:0]   m_axi_ic_arlen   ,
  output logic         m_axi_ic_arlock  ,
  output logic [2:0]   m_axi_ic_arprot  ,
  output logic [3:0]   m_axi_ic_arqos   ,
  input  logic         m_axi_ic_arready ,
  output logic [2:0]   m_axi_ic_arsize  ,
  output logic         m_axi_ic_arvalid ,
  output logic [63:0]  m_axi_ic_awaddr  ,
  output logic [1:0]   m_axi_ic_awburst ,
  output logic [3:0]   m_axi_ic_awcache ,
  output logic         m_axi_ic_awid    ,
  output logic [7:0]   m_axi_ic_awlen   ,
  output logic         m_axi_ic_awlock  ,
  output logic [2:0]   m_axi_ic_awprot  ,
  output logic [3:0]   m_axi_ic_awqos   ,
  input  logic         m_axi_ic_awready ,
  output logic [2:0]   m_axi_ic_awsize  ,
  output logic         m_axi_ic_awvalid ,
  input  logic         m_axi_ic_bid     ,
  output logic         m_axi_ic_bready  ,
  input  logic [1:0]   m_axi_ic_bresp   ,
  input  logic         m_axi_ic_bvalid  ,
  input  logic [31:0]  m_axi_ic_rdata   ,
  input  logic         m_axi_ic_rid     ,
  input  logic         m_axi_ic_rlast   ,
  output logic         m_axi_ic_rready  ,
  input  logic [1:0]   m_axi_ic_rresp   ,
  input  logic         m_axi_ic_rvalid  ,
  output logic [31:0]  m_axi_ic_wdata   ,
  output logic         m_axi_ic_wlast   ,
  input  logic         m_axi_ic_wready  ,
  output logic [3:0]   m_axi_ic_wstrb   ,
  output logic         m_axi_ic_wvalid
);




  
  logic [21:0]  ip_paddr_begin;
  logic [21:0]  ip_paddr_end;
  logic [21:0]  ip_paddr_mask;
  logic [21:0]  ip_paddr;
  logic         ip_penable;
  logic [31:0]  ip_prdata;
  logic         ip_pready;
  logic         ip_psel;
  logic         ip_pslverr;
  logic [31:0]  ip_pwdata;
  logic         ip_pwrite;
  logic         ip_pintreq;
  logic [31:0]  ip_pintbus;
  logic [31:0]  ip_ctrl_read;
  logic [31:0]  ip_ctrl_write;
  logic [21:0]  i_paddr;
  logic         i_penable;
  logic [31:0]  i_prdata;
  logic         i_pready;
  logic         i_psel;
  logic [31:0]  i_pwdata;
  logic         i_pwrite;
  
  logic [21:0]  vip0_paddr_begin;
  logic [21:0]  vip0_paddr_end;
  logic [21:0]  vip0_paddr_mask;
  logic [21:0]  vip0_paddr;
  logic         vip0_penable;
  logic [31:0]  vip0_prdata;
  logic         vip0_pready;
  logic         vip0_psel;
  logic         vip0_pslverr;
  logic [31:0]  vip0_pwdata;
  logic         vip0_pwrite;
  logic         vip0_pintreq;
  
  logic [21:0]  vip1_paddr_begin;
  logic [21:0]  vip1_paddr_end;
  logic [21:0]  vip1_paddr_mask;
  logic [21:0]  vip1_paddr;
  logic         vip1_penable;
  logic [31:0]  vip1_prdata;
  logic         vip1_pready;
  logic         vip1_psel;
  logic         vip1_pslverr;
  logic [31:0]  vip1_pwdata;
  logic         vip1_pwrite;
  logic         vip1_pintreq;
  
  logic [21:0]  vip2_paddr_begin;
  logic [21:0]  vip2_paddr_end;
  logic [21:0]  vip2_paddr_mask;
  logic [21:0]  vip2_paddr;
  logic         vip2_penable;
  logic [31:0]  vip2_prdata;
  logic         vip2_pready;
  logic         vip2_psel;
  logic         vip2_pslverr;
  logic [31:0]  vip2_pwdata;
  logic         vip2_pwrite;
  logic         vip2_pintreq;
  
  logic [21:0]  vip3_paddr_begin;
  logic [21:0]  vip3_paddr_end;
  logic [21:0]  vip3_paddr_mask;
  logic [21:0]  vip3_paddr;
  logic         vip3_penable;
  logic [31:0]  vip3_prdata;
  logic         vip3_pready;
  logic         vip3_psel;
  logic         vip3_pslverr;
  logic [31:0]  vip3_pwdata;
  logic         vip3_pwrite;
  logic         vip3_pintreq;
  
  logic [21:0]  vip4_paddr_begin;
  logic [21:0]  vip4_paddr_end;
  logic [21:0]  vip4_paddr_mask;
  logic [21:0]  vip4_paddr;
  logic         vip4_penable;
  logic [31:0]  vip4_prdata;
  logic         vip4_pready;
  logic         vip4_psel;
  logic         vip4_pslverr;
  logic [31:0]  vip4_pwdata;
  logic         vip4_pwrite;
  logic         vip4_pintreq;
  
  logic [63:0]  ii_awaddr0;
  logic [1:0]   ii_awburst0;
  logic [4:0]   ii_awid0;
  logic [7:0]   ii_awlen0;
  logic         ii_awready0;
  logic [2:0]   ii_awsize0;
  logic         ii_awvalid0;
  logic         ii_bready0;
  logic         ii_bvalid0;
  logic         ii_bresp0;
  logic [4:0]   ii_bid0;
  logic [128-1:0] ii_wdata0;
  logic [(128/8)-1:0]  ii_wstrb0;
  logic         ii_wlast0;
  logic         ii_wready0;
  logic         ii_wvalid0;
  
  logic [63:0]  araddr_mcu          ;
  logic [1:0]   arburst_mcu         ;
  logic [4:0]   arid_mcu            ;
  logic [7:0]   arlen_mcu           ;
  logic         arready_mcu         ;
  logic [2:0]   arsize_mcu          ;
  logic         arvalid_mcu         ;
  logic [63:0]  awaddr_mcu          ;
  logic [1:0]   awburst_mcu         ;
  logic [4:0]   awid_mcu            ;
  logic [7:0]   awlen_mcu           ;
  logic         awready_mcu         ;
  logic [2:0]   awsize_mcu          ;
  logic         awvalid_mcu         ;
  logic         bready_mcu          ;
  logic         bvalid_mcu          ;
  logic [1:0]   bresp_mcu           ;
  logic [4:0]   bid_mcu             ;
  logic [128-1:0] rdata_mcu;
  logic [4:0]   rid_mcu             ;
  logic         rlast_mcu           ;
  logic         rready_mcu          ;
  logic         rvalid_mcu          ;
  logic [1:0]   rresp_mcu           ;
  logic [128-1:0] wdata_mcu;
  logic         wlast_mcu           ;
  logic [(128/8)-1:0] wstrb_mcu;
  logic         wready_mcu          ;
  logic         wvalid_mcu          ;
  
  logic [63:0]  i_araddr0;
  logic [1:0]   i_arburst0;
  logic [4:0]   i_arid0;
  logic [7:0]   i_arlen0;
  logic         i_arready0;
  logic [2:0]   i_arsize0;
  logic         i_arvalid0;
  logic [63:0]  i_awaddr0;
  logic [1:0]   i_awburst0;
  logic [4:0]   i_awid0;
  logic [7:0]   i_awlen0;
  logic         i_awready0;
  logic [2:0]   i_awsize0;
  logic         i_awvalid0;
  logic         i_bready0;
  logic         i_bvalid0;
  logic [1:0]   i_bresp0;
  logic [4:0]   i_bid0;
  logic [128-1:0] i_rdata0;
  logic [4:0]   i_rid0;
  logic         i_rlast0;
  logic         i_rready0;
  logic         i_rvalid0;
  logic [1:0]   i_rresp0;
  logic [128-1:0] i_wdata0;
  logic [(128/8)-1:0]  i_wstrb0;
  logic         i_wlast0;
  logic         i_wready0;
  logic         i_wvalid0;
  
  logic [63:0]  i_araddr1;
  logic [1:0]   i_arburst1;
  logic [4:0]   i_arid1;
  logic [7:0]   i_arlen1;
  logic         i_arready1;
  logic [2:0]   i_arsize1;
  logic         i_arvalid1;
  logic [63:0]  i_awaddr1;
  logic [1:0]   i_awburst1;
  logic [4:0]   i_awid1;
  logic [7:0]   i_awlen1;
  logic         i_awready1;
  logic [2:0]   i_awsize1;
  logic         i_awvalid1;
  logic         i_bready1;
  logic         i_bvalid1;
  logic [1:0]   i_bresp1;
  logic [4:0]   i_bid1;
  logic [128-1:0] i_rdata1;
  logic [4:0]   i_rid1;
  logic         i_rlast1;
  logic         i_rready1;
  logic         i_rvalid1;
  logic [1:0]   i_rresp1;
  logic [128-1:0] i_wdata1;
  logic [(128/8)-1:0]  i_wstrb1;
  logic         i_wlast1;
  logic         i_wready1;
  logic         i_wvalid1;
  
  logic [63:0]  i_araddr3;
  logic [1:0]   i_arburst3;
  logic [4:0]   i_arid3;
  logic [7:0]   i_arlen3;
  logic         i_arready3;
  logic [2:0]   i_arsize3;
  logic         i_arvalid3;
  logic [63:0]  i_awaddr3;
  logic [1:0]   i_awburst3;
  logic [4:0]   i_awid3;
  logic [7:0]   i_awlen3;
  logic         i_awready3;
  logic [2:0]   i_awsize3;
  logic         i_awvalid3;
  logic         i_bready3;
  logic         i_bvalid3;
  logic [1:0]   i_bresp3;
  logic [4:0]   i_bid3;
  logic [128-1:0] i_rdata3;
  logic [4:0]   i_rid3;
  logic         i_rlast3;
  logic         i_rready3;
  logic         i_rvalid3;
  logic [1:0]   i_rresp3;
  logic [128-1:0] i_wdata3;
  logic [(128/8)-1:0]  i_wstrb3;
  logic         i_wlast3;
  logic         i_wready3;
  logic         i_wvalid3;
  
  logic [63:0]  i_araddr4;
  logic [1:0]   i_arburst4;
  logic [4:0]   i_arid4;
  logic [7:0]   i_arlen4;
  logic         i_arready4;
  logic [2:0]   i_arsize4;
  logic         i_arvalid4;
  logic [63:0]  i_awaddr4;
  logic [1:0]   i_awburst4;
  logic [4:0]   i_awid4;
  logic [7:0]   i_awlen4;
  logic         i_awready4;
  logic [2:0]   i_awsize4;
  logic         i_awvalid4;
  logic         i_bready4;
  logic         i_bvalid4;
  logic [1:0]   i_bresp4;
  logic [4:0]   i_bid4;
  logic [128-1:0] i_rdata4;
  logic [4:0]   i_rid4;
  logic         i_rlast4;
  logic         i_rready4;
  logic         i_rvalid4;
  logic [1:0]   i_rresp4;
  logic [128-1:0] i_wdata4;
  logic [(128/8)-1:0]  i_wstrb4;
  logic         i_wlast4;
  logic         i_wready4;
  logic         i_wvalid4;
  
  logic [63:0]  i_araddr2;
  logic [1:0]   i_arburst2;
  logic [4:0]   i_arid2;
  logic [7:0]   i_arlen2;
  logic         i_arready2;
  logic [2:0]   i_arsize2;
  logic         i_arvalid2;
  logic [63:0]  i_awaddr2;
  logic [1:0]   i_awburst2;
  logic [4:0]   i_awid2;
  logic [7:0]   i_awlen2;
  logic         i_awready2;
  logic [2:0]   i_awsize2;
  logic         i_awvalid2;
  logic         i_bready2;
  logic         i_bvalid2;
  logic [1:0]   i_bresp2;
  logic [4:0]   i_bid2;
  logic [128-1:0] i_rdata2;
  logic [4:0]   i_rid2;
  logic         i_rlast2;
  logic         i_rready2;
  logic         i_rvalid2;
  logic [1:0]   i_rresp2;
  logic [128-1:0] i_wdata2;
  logic [(128/8)-1:0]  i_wstrb2;
  logic         i_wlast2;
  logic         i_wready2;
  logic         i_wvalid2;
  
  logic local_ip_clk;
  logic local_ip_rstn;
  logic local_ip_pclk;
  logic local_ip_prstn;
  logic local_ip_aclk;
  logic local_ip_arstn;
  logic local_ip_mclk;
  logic local_ip_mrstn;
  logic mcu_int_next;
  logic mcu_ack_next;
  logic mcu_int_prev;
  logic mcu_ack_prev;
  
  logic         axi_pc_asserted0;
  logic [96:0]  axi_pc_status0  ;
  logic         axi_pc_asserted1;
  logic [96:0]  axi_pc_status1  ;
  logic         axi_pc_asserted2;
  logic [96:0]  axi_pc_status2  ;
  logic         axi_pc_asserted3;
  logic [96:0]  axi_pc_status3  ;





  
  assign local_ip_clk         = sys_clk;    
  assign local_ip_rstn        = sys_rstn;
  assign local_ip_mclk        = mcu_clk;    
  assign local_ip_mrstn       = mcu_rstn;
assign local_ip_aclk        = aclk_nobuf;
assign local_ip_arstn       = arstn;
assign local_ip_pclk        = aclk_nobuf;
assign local_ip_prstn       = arstn;
assign pclk_out             = local_ip_pclk;
assign prstn_out            = local_ip_prstn;
assign l2c_tx = '0;



  alg_amba_vip_apbdemux #(
    .ADDR_WIDTH (22),
    .NUM_SLAVES (6)
  ) I_APB_DEMUX_IP (
    
    .clk             (local_ip_pclk),
    .rstn            (local_ip_prstn),
    
    .psel            (psel   ),
    .penable         (penable),
    .pwrite          (pwrite ),
    .pwdata          (pwdata ),
    .paddr           (paddr[21:0]),
    .prdata          (prdata ),
    .pready          (pready ),
    .pintreq         (pintreq),
    .pslverr         (pslverr),
    
    
    .slv_address_begin({ ip_paddr_begin, vip0_paddr_begin, vip1_paddr_begin, vip2_paddr_begin, vip3_paddr_begin, vip4_paddr_begin  }),
    .slv_address_end  ({ ip_paddr_end  , vip0_paddr_end  , vip1_paddr_end  , vip2_paddr_end  , vip3_paddr_end  , vip4_paddr_end    }),
    .slv_address_mask ({ ip_paddr_mask , vip0_paddr_mask , vip1_paddr_mask , vip2_paddr_mask , vip3_paddr_mask , vip4_paddr_mask   }),
    .slv_psel         ({ ip_psel       , vip0_psel       , vip1_psel       , vip2_psel       , vip3_psel       , vip4_psel         }),
    .slv_penable      ({ ip_penable    , vip0_penable    , vip1_penable    , vip2_penable    , vip3_penable    , vip4_penable      }),
    .slv_pwrite       ({ ip_pwrite     , vip0_pwrite     , vip1_pwrite     , vip2_pwrite     , vip3_pwrite     , vip4_pwrite       }),
    .slv_pwdata       ({ ip_pwdata     , vip0_pwdata     , vip1_pwdata     , vip2_pwdata     , vip3_pwdata     , vip4_pwdata       }),
    .slv_paddr        ({ ip_paddr      , vip0_paddr      , vip1_paddr      , vip2_paddr      , vip3_paddr      , vip4_paddr        }),
    .slv_prdata       ({ ip_prdata     , vip0_prdata     , vip1_prdata     , vip2_prdata     , vip3_prdata     , vip4_prdata       }),
    .slv_pready       ({ ip_pready     , vip0_pready     , vip1_pready     , vip2_pready     , vip3_pready     , vip4_pready       }),
    .slv_pintreq      ({ ip_pintreq    , vip0_pintreq    , vip1_pintreq    , vip2_pintreq    , vip3_pintreq    , vip4_pintreq      }),
    .slv_pslverr      ({ ip_pslverr    , vip0_pslverr    , vip1_pslverr    , vip2_pslverr    , vip3_pslverr    , vip4_pslverr      })
  );
  assign ip_paddr_begin   = {2'h0, 4'h8, 16'h0000};
  assign ip_paddr_end     = {2'h0, 4'hF, 16'hFFFF};
  assign ip_paddr_mask    = 22'h3FFFFF;
  assign ip_pslverr = '0;
  
  assign vip0_paddr_begin = {2'h2, 4'h0, 16'h0000};
  assign vip0_paddr_end   = {2'h2, 4'h0, 16'hFFFF};
  assign vip0_paddr_mask  = 22'h3FFFFF;
  
  assign vip1_paddr_begin = {2'h2, 4'h1, 16'h0000};
  assign vip1_paddr_end   = {2'h2, 4'h1, 16'hFFFF};
  assign vip1_paddr_mask  = 22'h3FFFFF;
  
  assign vip2_paddr_begin = {2'h2, 4'h2, 16'h0000};
  assign vip2_paddr_end   = {2'h2, 4'h2, 16'hFFFF};
  assign vip2_paddr_mask  = 22'h3FFFFF;
  
  assign vip3_paddr_begin = {2'h2, 4'h3, 16'h0000};
  assign vip3_paddr_end   = {2'h2, 4'h3, 16'hFFFF};
  assign vip3_paddr_mask  = 22'h3FFFFF;
  
  assign vip4_paddr_begin = {2'h2, 4'h4, 16'h0000};
  assign vip4_paddr_end   = {2'h2, 4'h4, 16'hFFFF};
  assign vip4_paddr_mask  = 22'h3FFFFF;

  
  assign axi_pc_asserted0 = '0;
  assign axi_pc_status0   = '0;
  assign axi_pc_asserted1 = '0;
  assign axi_pc_status1   = '0;
  assign axi_pc_asserted2 = '0;
  assign axi_pc_status2   = '0;
  assign axi_pc_asserted3 = '0;
  assign axi_pc_status3   = '0;



//`ifndef USE_NCSIM
//  `uselib dir=work_alg_dec_ip
//`endif
  alg_vcu_dec_top I_TOP (
      .clk            (local_ip_clk   ),
      .rstn           (local_ip_rstn  ),
      .araddr0        (i_araddr0),
      .arburst0       (i_arburst0),
      .arid0          (i_arid0),
      .arlen0         (i_arlen0),
      .arready0       (i_arready0),
      .arsize0        (i_arsize0),
      .arprot0        (),
      .arvalid0       (i_arvalid0),
      .awaddr0        (i_awaddr0),
      .awburst0       (i_awburst0),
      .awid0          (i_awid0),
      .awlen0         (i_awlen0),
      .awready0       (i_awready0),
      .awsize0        (i_awsize0),
      .awprot0        (),
      .awvalid0       (i_awvalid0),
      .bready0        (i_bready0),
      .bvalid0        (i_bvalid0),
      .bresp0         (i_bresp0),
      .bid0           (i_bid0),
      .rdata0         (i_rdata0),
      .rid0           (i_rid0),
      .rlast0         (i_rlast0),
      .rready0        (i_rready0),
      .rvalid0        (i_rvalid0),
      .rresp0         (i_rresp0),
      .wdata0         (i_wdata0),
      .wstrb0         (i_wstrb0),
      .wlast0         (i_wlast0),
      .wready0        (i_wready0),
      .wvalid0        (i_wvalid0),
      .araddr1        (i_araddr1),
      .arburst1       (i_arburst1),
      .arid1          (i_arid1),
      .arlen1         (i_arlen1),
      .arready1       (i_arready1),
      .arsize1        (i_arsize1),
      .arprot1        (),
      .arvalid1       (i_arvalid1),
      .awaddr1        (i_awaddr1),
      .awburst1       (i_awburst1),
      .awid1          (i_awid1),
      .awlen1         (i_awlen1),
      .awready1       (i_awready1),
      .awsize1        (i_awsize1),
      .awprot1        (),
      .awvalid1       (i_awvalid1),
      .bready1        (i_bready1),
      .bvalid1        (i_bvalid1),
      .bresp1         (i_bresp1),
      .bid1           (i_bid1),
      .rdata1         (i_rdata1),
      .rid1           (i_rid1),
      .rlast1         (i_rlast1),
      .rready1        (i_rready1),
      .rvalid1        (i_rvalid1),
      .rresp1         (i_rresp1),
      .wdata1         (i_wdata1),
      .wstrb1         (i_wstrb1),
      .wlast1         (i_wlast1),
      .wready1        (i_wready1),
      .wvalid1        (i_wvalid1),
      .araddr2        (i_araddr3),
      .arburst2       (i_arburst3),
      .arid2          (i_arid3),
      .arlen2         (i_arlen3),
      .arready2       (i_arready3),
      .arsize2        (i_arsize3),
      .arprot2        (),
      .arvalid2       (i_arvalid3),
      .awaddr2        (i_awaddr3),
      .awburst2       (i_awburst3),
      .awid2          (i_awid3),
      .awlen2         (i_awlen3),
      .awready2       (i_awready3),
      .awsize2        (i_awsize3),
      .awprot2        (),
      .awvalid2       (i_awvalid3),
      .bready2        (i_bready3),
      .bvalid2        (i_bvalid3),
      .bresp2         (i_bresp3),
      .bid2           (i_bid3),
      .rdata2         (i_rdata3),
      .rid2           (i_rid3),
      .rlast2         (i_rlast3),
      .rready2        (i_rready3),
      .rvalid2        (i_rvalid3),
      .rresp2         (i_rresp3),
      .wdata2         (i_wdata3),
      .wstrb2         (i_wstrb3),
      .wlast2         (i_wlast3),
      .wready2        (i_wready3),
      .wvalid2        (i_wvalid3),
      .mclk           (local_ip_mclk),
      .mrstn          (local_ip_mrstn),
      .mcu_int_next   (mcu_int_next),
      .mcu_ack_next   (mcu_ack_next),
      .mcu_int_prev   (mcu_int_prev),
      .mcu_ack_prev   (mcu_ack_prev),
      .jtag_clk       (debug_clk),
      .jtag_ms        (debug_update),
      .jtag_di        (debug_tdi),
      .jtag_do        (debug_tdo),
      .araddr_mcu     (araddr_mcu),
      .arburst_mcu    (arburst_mcu),
      .arid_mcu       (arid_mcu),
      .arlen_mcu      (arlen_mcu),
      .arready_mcu    (arready_mcu),
      .arsize_mcu     (arsize_mcu),
      .arprot_mcu     (),
      .arvalid_mcu    (arvalid_mcu),
      .awaddr_mcu     (awaddr_mcu),
      .awburst_mcu    (awburst_mcu),
      .awid_mcu       (awid_mcu),
      .awlen_mcu      (awlen_mcu),
      .awready_mcu    (awready_mcu),
      .awsize_mcu     (awsize_mcu),
      .awprot_mcu     (),
      .awvalid_mcu    (awvalid_mcu),
      .bready_mcu     (bready_mcu),
      .bvalid_mcu     (bvalid_mcu),
      .bresp_mcu      (bresp_mcu),
      .bid_mcu        (bid_mcu),
      .rdata_mcu      (rdata_mcu),
      .rid_mcu        (rid_mcu),
      .rlast_mcu      (rlast_mcu),
      .rready_mcu     (rready_mcu),
      .rvalid_mcu     (rvalid_mcu),
      .rresp_mcu      (rresp_mcu),
      .wdata_mcu      (wdata_mcu),
      .wstrb_mcu      (wstrb_mcu),
      .wlast_mcu      (wlast_mcu),
      .wready_mcu     (wready_mcu),
      .wvalid_mcu     (wvalid_mcu),
      .psel           (i_psel       ),
      .penable        (i_penable    ),
      .pwrite         (i_pwrite     ),
      .pwdata         (i_pwdata     ),
      .paddr          (i_paddr[19:0]),
      .prdata         (i_prdata     ),
      .pready         (i_pready     ),
      .pintbus        (ip_pintbus    ),
      .pintreq        (ip_pintreq    )
    );
//    `uselib



  assign ii_awid0    = i_awid0    ;
  assign ii_awaddr0  = i_awaddr0  ;
  assign ii_awlen0   = i_awlen0   ;
  assign ii_awsize0  = i_awsize0  ;
  assign ii_awburst0 = i_awburst0 ;
  assign ii_awvalid0 = i_awvalid0 ;
  assign i_awready0  = ii_awready0;
  assign ii_wdata0   = i_wdata0   ;
  assign ii_wstrb0   = i_wstrb0   ;
  assign ii_wlast0   = i_wlast0   ;
  assign ii_wvalid0  = i_wvalid0  ;
  assign i_wready0   = ii_wready0 ;
  assign ii_bready0  = i_bready0  ;
  assign i_bvalid0   = ii_bvalid0 ;
  assign i_bresp0    = {ii_bresp0,1'b0}  ;
  assign i_bid0      = ii_bid0    ;

  assign i_psel    = ip_psel;
  assign i_penable = ip_penable;
  assign i_pwrite  = ip_pwrite;
  assign i_pwdata  = ip_pwdata;
  assign i_paddr   = ip_paddr;
  assign ip_prdata = i_prdata;
  assign ip_pready = i_pready;





  logic [7:0] mcu_counter;
  logic [7:0] mcu_target;
  logic       mcu_ack;
  logic [255:0] mcu_fifo;
  always_ff @(posedge local_ip_mclk or negedge local_ip_mrstn)
  begin
    if ( !local_ip_mrstn ) begin
      mcu_counter     <= '0;
      mcu_target      <= '0;
      mcu_ack         <= '0;
      mcu_int_prev    <= '0;
      mcu_fifo        <= '0;
    end else begin

      if ( !mcu_int_next && mcu_ack )
        mcu_target      <= mcu_target + 1;

      if ( mcu_int_next )
        mcu_counter     <= mcu_counter + 1;
      else
        mcu_counter     <= '0;

      if(mcu_int_next && ((mcu_target == 0 && mcu_counter == mcu_target) ||
                          (mcu_counter == mcu_target - 1 && mcu_target != 0)))
        mcu_ack        <= '1;
      else
        if ( !mcu_int_next && mcu_ack )
          mcu_ack        <= '0;

      mcu_fifo[0]     <= !mcu_int_next && mcu_ack;
      mcu_fifo[255:1] <= mcu_fifo[254:0];
      if(mcu_fifo[255])
        mcu_int_prev    <= '1;
      else
        if(mcu_ack_prev)
          mcu_int_prev    <= '0;
    end
  end
  assign mcu_ack_next = (mcu_target==0)?mcu_int_next:mcu_ack;





assign ip_ctrl_read = '0;



    alg_amba_vip_wrapper #(
      .DATA_WIDTH      (128),
      .ID              (1),
      .APB_RESYNC      (1)
    ) I_AXI_VIP_0 (
      .pclk                    (local_ip_pclk      ),
      .presetn                 (local_ip_prstn     ),
      .psel                    (vip0_psel          ),
      .penable                 (vip0_penable       ),
      .pwrite                  (vip0_pwrite        ),
      .pwdata                  (vip0_pwdata        ),
      .paddr                   (vip0_paddr[15:0]   ),
      .prdata                  (vip0_prdata        ),
      .pready                  (vip0_pready        ),
      .pintreq                 (vip0_pintreq       ),
      .pslverr                 (vip0_pslverr       ),
      .ip_ctrl_write           (ip_ctrl_write      ),
      .ip_ctrl_read            (ip_ctrl_read       ),
      .axi_pc_asserted         (axi_pc_asserted0   ),
      .axi_pc_status           (axi_pc_status0     ),
      .aclk                    (local_ip_aclk      ),
      .aresetn                 (local_ip_arstn     ),
      .axi_awid                (awid0              ),
      .axi_awaddr              (awaddr0            ),
      .axi_awlen               (awlen0             ),
      .axi_awsize              (awsize0            ),
      .axi_awburst             (awburst0           ),
      .axi_awvalid             (awvalid0           ),
      .axi_awready             (awready0           ),
      .axi_wdata               (wdata0             ),
      .axi_wstrb               (wstrb0             ),
      .axi_wlast               (wlast0             ),
      .axi_wvalid              (wvalid0            ),
      .axi_wready              (wready0            ),
      .axi_bready              (bready0            ),
      .axi_bvalid              (bvalid0            ),
      .axi_bresp               (bresp0             ),
      .axi_bid                 (bid0               ),
      .axi_arid                (arid0              ),
      .axi_araddr              (araddr0            ),
      .axi_arlen               (arlen0             ),
      .axi_arsize              (arsize0            ),
      .axi_arburst             (arburst0           ),
      .axi_arvalid             (arvalid0           ),
      .axi_arready             (arready0           ),
      .axi_rid                 (rid0               ),
      .axi_rdata               (rdata0             ),
      .axi_rlast               (rlast0             ),
      .axi_rvalid              (rvalid0            ),
      .axi_rresp               (rresp0             ),
      .axi_rready              (rready0            ),
      .ip_awid                 (ii_awid0           ),
      .ip_awaddr               (ii_awaddr0         ),
      .ip_awlen                (ii_awlen0          ),
      .ip_awsize               (ii_awsize0         ),
      .ip_awburst              (ii_awburst0        ),
      .ip_awvalid              (ii_awvalid0        ),
      .ip_awready              (ii_awready0        ),
      .ip_wdata                (ii_wdata0          ),
      .ip_wstrb                (ii_wstrb0          ),
      .ip_wlast                (ii_wlast0          ),
      .ip_wvalid               (ii_wvalid0         ),
      .ip_wready               (ii_wready0         ),
      .ip_bready               (ii_bready0         ),
      .ip_bvalid               (ii_bvalid0         ),
      .ip_bresp                (ii_bresp0          ),
      .ip_bid                  (ii_bid0            ),
      .ip_arid                 (i_arid0            ),
      .ip_araddr               (i_araddr0          ),
      .ip_arlen                (i_arlen0           ),
      .ip_arsize               (i_arsize0          ),
      .ip_arburst              (i_arburst0         ),
      .ip_arvalid              (i_arvalid0         ),
      .ip_arready              (i_arready0         ),
      .ip_rid                  (i_rid0             ),
      .ip_rdata                (i_rdata0           ),
      .ip_rlast                (i_rlast0           ),
      .ip_rvalid               (i_rvalid0          ),
      .ip_rresp                (i_rresp0[1]        ),
      .ip_rready               (i_rready0          )
    );
    assign i_rresp0[0]  = '0;


    alg_amba_vip_wrapper #(
      .DATA_WIDTH      (128),
      .ID              (2),
      .APB_RESYNC      (1)
    ) I_AXI_VIP_1 (
      .pclk                    (local_ip_pclk      ),
      .presetn                 (local_ip_prstn     ),
      .psel                    (vip1_psel          ),
      .penable                 (vip1_penable       ),
      .pwrite                  (vip1_pwrite        ),
      .pwdata                  (vip1_pwdata        ),
      .paddr                   (vip1_paddr[15:0]   ),
      .prdata                  (vip1_prdata        ),
      .pready                  (vip1_pready        ),
      .pintreq                 (vip1_pintreq       ),
      .pslverr                 (vip1_pslverr       ),
      .ip_ctrl_write           (                   ),
      .ip_ctrl_read            (ip_ctrl_read       ),
      .axi_pc_asserted         (axi_pc_asserted1   ),
      .axi_pc_status           (axi_pc_status1     ),
      .aclk                    (local_ip_aclk      ),
      .aresetn                 (local_ip_arstn     ),
      .axi_awid                (awid1              ),
      .axi_awaddr              (awaddr1            ),
      .axi_awlen               (awlen1             ),
      .axi_awsize              (awsize1            ),
      .axi_awburst             (awburst1           ),
      .axi_awvalid             (awvalid1           ),
      .axi_awready             (awready1           ),
      .axi_wdata               (wdata1             ),
      .axi_wstrb               (wstrb1             ),
      .axi_wlast               (wlast1             ),
      .axi_wvalid              (wvalid1            ),
      .axi_wready              (wready1            ),
      .axi_bready              (bready1            ),
      .axi_bvalid              (bvalid1            ),
      .axi_bresp               (bresp1             ),
      .axi_bid                 (bid1               ),
      .axi_arid                (arid1              ),
      .axi_araddr              (araddr1            ),
      .axi_arlen               (arlen1             ),
      .axi_arsize              (arsize1            ),
      .axi_arburst             (arburst1           ),
      .axi_arvalid             (arvalid1           ),
      .axi_arready             (arready1           ),
      .axi_rid                 (rid1               ),
      .axi_rdata               (rdata1             ),
      .axi_rlast               (rlast1             ),
      .axi_rvalid              (rvalid1            ),
      .axi_rresp               (rresp1             ),
      .axi_rready              (rready1            ),
      .ip_awid                 (i_awid1            ),
      .ip_awaddr               (i_awaddr1          ),
      .ip_awlen                (i_awlen1           ),
      .ip_awsize               (i_awsize1          ),
      .ip_awburst              (i_awburst1         ),
      .ip_awvalid              (i_awvalid1         ),
      .ip_awready              (i_awready1         ),
      .ip_wdata                (i_wdata1           ),
      .ip_wstrb                (i_wstrb1           ),
      .ip_wlast                (i_wlast1           ),
      .ip_wvalid               (i_wvalid1          ),
      .ip_wready               (i_wready1          ),
      .ip_bready               (i_bready1          ),
      .ip_bvalid               (i_bvalid1          ),
      .ip_bresp                (i_bresp1[1]        ),
      .ip_bid                  (i_bid1             ),
      .ip_arid                 (i_arid1            ),
      .ip_araddr               (i_araddr1          ),
      .ip_arlen                (i_arlen1           ),
      .ip_arsize               (i_arsize1          ),
      .ip_arburst              (i_arburst1         ),
      .ip_arvalid              (i_arvalid1         ),
      .ip_arready              (i_arready1         ),
      .ip_rid                  (i_rid1             ),
      .ip_rdata                (i_rdata1           ),
      .ip_rlast                (i_rlast1           ),
      .ip_rvalid               (i_rvalid1          ),
      .ip_rresp                (i_rresp1[1]        ),
      .ip_rready               (i_rready1          )
    );
    assign i_rresp1[0]  = '0;
    assign i_bresp1[0]  = '0;


  alg_amba_vip_wrapper #(
    .DATA_WIDTH      (128),
    .ID              (3),
    .APB_RESYNC      (1)
  ) I_AXI_VIP_2 (
    .pclk                    (local_ip_pclk      ),
    .presetn                 (local_ip_prstn     ),
    .psel                    (vip2_psel          ),
    .penable                 (vip2_penable       ),
    .pwrite                  (vip2_pwrite        ),
    .pwdata                  (vip2_pwdata        ),
    .paddr                   (vip2_paddr[15:0]   ),
    .prdata                  (vip2_prdata        ),
    .pready                  (vip2_pready        ),
    .pintreq                 (vip2_pintreq       ),
    .pslverr                 (vip2_pslverr       ),
    .ip_ctrl_write           (                   ),
    .ip_ctrl_read            (ip_ctrl_read       ),
    .axi_pc_asserted         (axi_pc_asserted2   ),
    .axi_pc_status           (axi_pc_status2     ),
    .aclk                    (local_ip_aclk      ),
    .aresetn                 (local_ip_arstn     ),
    .axi_awid                (awid3              ),
    .axi_awaddr              (awaddr3            ),
    .axi_awlen               (awlen3             ),
    .axi_awsize              (awsize3            ),
    .axi_awburst             (awburst3           ),
    .axi_awvalid             (awvalid3           ),
    .axi_awready             (awready3           ),
    .axi_wdata               (wdata3             ),
    .axi_wstrb               (wstrb3             ),
    .axi_wlast               (wlast3             ),
    .axi_wvalid              (wvalid3            ),
    .axi_wready              (wready3            ),
    .axi_bready              (bready3            ),
    .axi_bvalid              (bvalid3            ),
    .axi_bresp               (bresp3             ),
    .axi_bid                 (bid3               ),
    .axi_arid                (arid3              ),
    .axi_araddr              (araddr3            ),
    .axi_arlen               (arlen3             ),
    .axi_arsize              (arsize3            ),
    .axi_arburst             (arburst3           ),
    .axi_arvalid             (arvalid3           ),
    .axi_arready             (arready3           ),
    .axi_rid                 (rid3               ),
    .axi_rdata               (rdata3             ),
    .axi_rlast               (rlast3             ),
    .axi_rvalid              (rvalid3            ),
    .axi_rresp               (rresp3             ),
    .axi_rready              (rready3            ),
    .ip_awid                 (i_awid3            ),
    .ip_awaddr               (i_awaddr3          ),
    .ip_awlen                (i_awlen3           ),
    .ip_awsize               (i_awsize3          ),
    .ip_awburst              (i_awburst3         ),
    .ip_awvalid              (i_awvalid3         ),
    .ip_awready              (i_awready3         ),
    .ip_wdata                (i_wdata3           ),
    .ip_wstrb                (i_wstrb3           ),
    .ip_wlast                (i_wlast3           ),
    .ip_wvalid               (i_wvalid3          ),
    .ip_wready               (i_wready3          ),
    .ip_bready               (i_bready3          ),
    .ip_bvalid               (i_bvalid3          ),
    .ip_bresp                (i_bresp3[1]        ),
    .ip_bid                  (i_bid3             ),
    .ip_arid                 (i_arid3            ),
    .ip_araddr               (i_araddr3          ),
    .ip_arlen                (i_arlen3           ),
    .ip_arsize               (i_arsize3          ),
    .ip_arburst              (i_arburst3         ),
    .ip_arvalid              (i_arvalid3         ),
    .ip_arready              (i_arready3         ),
    .ip_rid                  (i_rid3             ),
    .ip_rdata                (i_rdata3           ),
    .ip_rlast                (i_rlast3           ),
    .ip_rvalid               (i_rvalid3          ),
    .ip_rresp                (i_rresp3[1]        ),
    .ip_rready               (i_rready3          )
  );
  assign i_rresp3[0]  = '0;
  assign i_bresp3[0]  = '0;

  assign araddr4      = '0;
  assign arburst4     = '0;
  assign arid4        = '0;
  assign arlen4       = '0;
  assign arsize4      = '0;
  assign arvalid4     = '0;
  assign awaddr4      = '0;
  assign awburst4     = '0;
  assign awid4        = '0;
  assign awlen4       = '0;
  assign awsize4      = '0;
  assign awvalid4     = '0;
  assign bready4      = '0;
  assign rready4      = '0;
  assign wdata4       = '0;
  assign wstrb4       = '0;
  assign wlast4       = '0;
  assign wvalid4      = '0;
  
  assign i_araddr4    = '0;
  assign i_arburst4   = '0;
  assign i_arid4      = '0;
  assign i_arlen4     = '0;
  assign i_arready4   = '0;
  assign i_arsize4    = '0;
  assign i_arvalid4   = '0;
  assign i_awaddr4    = '0;
  assign i_awburst4   = '0;
  assign i_awid4      = '0;
  assign i_awlen4     = '0;
  assign i_awready4   = '0;
  assign i_awsize4    = '0;
  assign i_awvalid4   = '0;
  assign i_bready4    = '0;
  assign i_bvalid4    = '0;
  assign i_bresp4     = '0;
  assign i_bid4       = '0;
  assign i_rdata4     = '0;
  assign i_rid4       = '0;
  assign i_rlast4     = '0;
  assign i_rready4    = '0;
  assign i_rvalid4    = '0;
  assign i_rresp4     = '0;
  assign i_wdata4     = '0;
  assign i_wstrb4     = '0;
  assign i_wlast4     = '0;
  assign i_wready4    = '0;
  assign i_wvalid4    = '0;
  
  assign vip3_prdata      = 32'h00000000;
  assign vip3_pready      = '1;
  assign vip3_pintreq     = '0;
  assign vip3_pslverr     = '0;


  alg_amba_axi2axi_async #(
    .AXI_DATA_WIDTH (128)
  ) AXI_MCU_ASYNC_BRIDGE (
    .r_clk       (local_ip_clk),
    .r_rstn      (local_ip_rstn),
    .r_araddr    (i_araddr2),
    .r_arburst   (i_arburst2),
    .r_arid      (i_arid2),
    .r_arlen     (i_arlen2),
    .r_arready   (i_arready2),
    .r_arsize    (i_arsize2),
    .r_arvalid   (i_arvalid2),
    .r_awaddr    (i_awaddr2),
    .r_awburst   (i_awburst2),
    .r_awid      (i_awid2),
    .r_awlen     (i_awlen2),
    .r_awready   (i_awready2),
    .r_awsize    (i_awsize2),
    .r_awvalid   (i_awvalid2),
    .r_bready    (i_bready2),
    .r_bvalid    (i_bvalid2),
    .r_bresp     (i_bresp2),
    .r_bid       (i_bid2),
    .r_rdata     (i_rdata2),
    .r_rid       (i_rid2),
    .r_rlast     (i_rlast2),
    .r_rready    (i_rready2),
    .r_rvalid    (i_rvalid2),
    .r_rresp     (i_rresp2),
    .r_wdata     (i_wdata2),
    .r_wstrb     (i_wstrb2),
    .r_wlast     (i_wlast2),
    .r_wready    (i_wready2),
    .r_wvalid    (i_wvalid2),
    .w_clk       (local_ip_mclk),
    .w_rstn      (local_ip_mrstn),
    .w_araddr    (araddr_mcu),
    .w_arburst   (arburst_mcu),
    .w_arid      (arid_mcu),
    .w_arlen     (arlen_mcu),
    .w_arready   (arready_mcu),
    .w_arsize    (arsize_mcu),
    .w_arvalid   (arvalid_mcu),
    .w_awaddr    (awaddr_mcu),
    .w_awburst   (awburst_mcu),
    .w_awid      (awid_mcu),
    .w_awlen     (awlen_mcu),
    .w_awready   (awready_mcu),
    .w_awsize    (awsize_mcu),
    .w_awvalid   (awvalid_mcu),
    .w_bready    (bready_mcu),
    .w_bvalid    (bvalid_mcu),
    .w_bresp     (bresp_mcu),
    .w_bid       (bid_mcu),
    .w_rdata     (rdata_mcu),
    .w_rid       (rid_mcu),
    .w_rlast     (rlast_mcu),
    .w_rready    (rready_mcu),
    .w_rvalid    (rvalid_mcu),
    .w_rresp     (rresp_mcu),
    .w_wdata     (wdata_mcu),
    .w_wstrb     (wstrb_mcu),
    .w_wlast     (wlast_mcu),
    .w_wready    (wready_mcu),
    .w_wvalid    (wvalid_mcu)
  );

  alg_amba_vip_wrapper #(
    .DATA_WIDTH      (128),
    .ID              (5),
    .APB_RESYNC      (1)
  ) I_AXI_VIP_MCU (
    .pclk                    (local_ip_pclk      ),
    .presetn                 (local_ip_prstn     ),
    .psel                    (vip4_psel          ),
    .penable                 (vip4_penable       ),
    .pwrite                  (vip4_pwrite        ),
    .pwdata                  (vip4_pwdata        ),
    .paddr                   (vip4_paddr[15:0]   ),
    .prdata                  (vip4_prdata        ),
    .pready                  (vip4_pready        ),
    .pintreq                 (vip4_pintreq       ),
    .pslverr                 (vip4_pslverr       ),
    .ip_ctrl_write           (                   ),
    .ip_ctrl_read            (ip_ctrl_read       ),
    .axi_pc_asserted         (axi_pc_asserted3   ),
    .axi_pc_status           (axi_pc_status3     ),
    .aclk                    (local_ip_aclk      ),
    .aresetn                 (local_ip_arstn     ),
    .axi_awid                (awid2              ),
    .axi_awaddr              (awaddr2            ),
    .axi_awlen               (awlen2             ),
    .axi_awsize              (awsize2            ),
    .axi_awburst             (awburst2           ),
    .axi_awvalid             (awvalid2           ),
    .axi_awready             (awready2           ),
    .axi_wdata               (wdata2             ),
    .axi_wstrb               (wstrb2             ),
    .axi_wlast               (wlast2             ),
    .axi_wvalid              (wvalid2            ),
    .axi_wready              (wready2            ),
    .axi_bready              (bready2            ),
    .axi_bvalid              (bvalid2            ),
    .axi_bresp               (bresp2             ),
    .axi_bid                 (bid2               ),
    .axi_arid                (arid2              ),
    .axi_araddr              (araddr2            ),
    .axi_arlen               (arlen2             ),
    .axi_arsize              (arsize2            ),
    .axi_arburst             (arburst2           ),
    .axi_arvalid             (arvalid2           ),
    .axi_arready             (arready2           ),
    .axi_rid                 (rid2               ),
    .axi_rdata               (rdata2             ),
    .axi_rlast               (rlast2             ),
    .axi_rvalid              (rvalid2            ),
    .axi_rresp               (rresp2             ),
    .axi_rready              (rready2            ),
    .ip_awid                 (i_awid2            ),
    .ip_awaddr               (i_awaddr2          ),
    .ip_awlen                (i_awlen2           ),
    .ip_awsize               (i_awsize2          ),
    .ip_awburst              (i_awburst2         ),
    .ip_awvalid              (i_awvalid2         ),
    .ip_awready              (i_awready2         ),
    .ip_wdata                (i_wdata2           ),
    .ip_wstrb                (i_wstrb2           ),
    .ip_wlast                (i_wlast2           ),
    .ip_wvalid               (i_wvalid2          ),
    .ip_wready               (i_wready2          ),
    .ip_bready               (i_bready2          ),
    .ip_bvalid               (i_bvalid2          ),
    .ip_bresp                (i_bresp2[1]        ),
    .ip_bid                  (i_bid2             ),
    .ip_arid                 (i_arid2            ),
    .ip_araddr               (i_araddr2          ),
    .ip_arlen                (i_arlen2           ),
    .ip_arsize               (i_arsize2          ),
    .ip_arburst              (i_arburst2         ),
    .ip_arvalid              (i_arvalid2         ),
    .ip_arready              (i_arready2         ),
    .ip_rid                  (i_rid2             ),
    .ip_rdata                (i_rdata2           ),
    .ip_rlast                (i_rlast2           ),
    .ip_rvalid               (i_rvalid2          ),
    .ip_rresp                (i_rresp2[1]        ),
    .ip_rready               (i_rready2          )
  );
  assign i_rresp2[0]  = '0;
  assign i_bresp2[0]  = '0;




  assign m_axi_dc_araddr        = '0;
  assign m_axi_dc_arburst       = '0;
  assign m_axi_dc_arcache       = '0;
  assign m_axi_dc_arid          = '0;
  assign m_axi_dc_arlen         = '0;
  assign m_axi_dc_arlock        = '0;
  assign m_axi_dc_arprot        = '0;
  assign m_axi_dc_arqos         = '0;
  assign m_axi_dc_arsize        = '0;
  assign m_axi_dc_arvalid       = '0;
  assign m_axi_dc_awaddr        = '0;
  assign m_axi_dc_awburst       = '0;
  assign m_axi_dc_awcache       = '0;
  assign m_axi_dc_awid          = '0;
  assign m_axi_dc_awlen         = '0;
  assign m_axi_dc_awlock        = '0;
  assign m_axi_dc_awprot        = '0;
  assign m_axi_dc_awqos         = '0;
  assign m_axi_dc_awsize        = '0;
  assign m_axi_dc_awvalid       = '0;
  assign m_axi_dc_bready        = '0;
  assign m_axi_dc_rready        = '0;
  assign m_axi_dc_wdata         = '0;
  assign m_axi_dc_wlast         = '0;
  assign m_axi_dc_wstrb         = '0;
  assign m_axi_dc_wvalid        = '0;
  
  assign m_axi_ic_araddr        = '0;
  assign m_axi_ic_arburst       = '0;
  assign m_axi_ic_arcache       = '0;
  assign m_axi_ic_arid          = '0;
  assign m_axi_ic_arlen         = '0;
  assign m_axi_ic_arlock        = '0;
  assign m_axi_ic_arprot        = '0;
  assign m_axi_ic_arqos         = '0;
  assign m_axi_ic_arsize        = '0;
  assign m_axi_ic_arvalid       = '0;
  assign m_axi_ic_awaddr        = '0;
  assign m_axi_ic_awburst       = '0;
  assign m_axi_ic_awcache       = '0;
  assign m_axi_ic_awid          = '0;
  assign m_axi_ic_awlen         = '0;
  assign m_axi_ic_awlock        = '0;
  assign m_axi_ic_awprot        = '0;
  assign m_axi_ic_awqos         = '0;
  assign m_axi_ic_awsize        = '0;
  assign m_axi_ic_awvalid       = '0;
  assign m_axi_ic_bready        = '0;
  assign m_axi_ic_rready        = '0;
  assign m_axi_ic_wdata         = '0;
  assign m_axi_ic_wlast         = '0;
  assign m_axi_ic_wstrb         = '0;
  assign m_axi_ic_wvalid        = '0;


`ifndef RAM_COVERAGE_NOPP
`ifdef TOP_COVERAGE_NOPP
covergroup Interface_int@(posedge (local_ip_pclk));
  coverpoint ip_pintreq;
endgroup
Interface_int Interface_int_inst = new();
covergroup Interface_toggle_intbus with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {31,30,0,1};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_toggle_intbus toggle_intbus = new();
always @(posedge local_ip_pclk) begin
  for(int i=0;i<32;i++) begin
    toggle_intbus.sample(i,ip_pintbus[i]);
  end
end
covergroup Interface_apb @(posedge (local_ip_pclk));
  coverpoint ip_psel;
  coverpoint ip_penable;
  coverpoint ip_pwrite;
  coverpoint ip_pready;
endgroup
Interface_apb Interface_apb_inst = new();
covergroup Interface_apb_toggle_read with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[0:32-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_apb_toggle_read toggle_apbread = new();

covergroup Interface_apb_toggle_write with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[0:32-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_apb_toggle_write toggle_apbwrite = new();
covergroup Interface_apb_toggle_addr with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[2:16-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_apb_toggle_addr toggle_apbaddr = new();
always @(posedge local_ip_pclk) begin
  for(int i=0;i<32;i++) begin
    if (psel==1&&penable==1&&pwrite==0) begin
      toggle_apbread.sample(i,ip_prdata[i]);
    end
    if (psel==1&&penable==1&&pwrite==1) begin
      toggle_apbwrite.sample(i,ip_pwdata[i]);
    end
  end
  for(int i=0;i<16;i++) begin
    if (psel==1&&penable==1) begin
      toggle_apbaddr.sample(i,ip_paddr[i]);
    end
  end
end
covergroup Interface_axi0 @(posedge (local_ip_aclk));
  coverpoint i_arready0 {bins allowed[]={1};}
  coverpoint i_arvalid0;
  coverpoint i_arburst0 iff(i_arready0==1&&i_arvalid0==1){ bins allowed[]={1};illegal_bins excluded=default;}
  coverpoint i_arsize0  iff(i_arready0==1&&i_arvalid0==1){ bins allowed[]={4};illegal_bins excluded=default;}
  coverpoint i_arid0    iff(i_arready0==1&&i_arvalid0==1){ bins allowed[]={0,1,2,4,5,6,8,9,10,3,11,7};illegal_bins excluded=default;}
  coverpoint i_arlen0   iff(i_arready0==1&&i_arvalid0==1){ bins allowed[]={1,3,5,7,9,11,13,15,31};}
  coverpoint i_awready0 {bins allowed[]={1};}
  coverpoint i_awvalid0;
  coverpoint i_awburst0 iff(i_awready0==1&&i_awvalid0==1){ bins allowed[]={1};illegal_bins excluded=default;}
  coverpoint i_awsize0  iff(i_awready0==1&&i_awvalid0==1){ bins allowed[]={4};illegal_bins excluded=default;}
  coverpoint i_awid0    iff(i_awready0==1&&i_awvalid0==1){ bins allowed[]={0,1,6,9,10,2,7,3,4,5};illegal_bins excluded=default;}
  coverpoint i_awlen0   iff(i_awready0==1&&i_awvalid0==1){ bins allowed[]={1,3,5,7,9,11,13,15};}
endgroup
Interface_axi0 Interface_axi0_inst = new();
covergroup Interface_axi0_toggle_read with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[0:128-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi0_toggle_read toggle_axi0read = new();
covergroup Interface_axi0_toggle_write with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[0:128-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi0_toggle_write toggle_axi0write = new();
covergroup Interface_axi0_toggle_awrite with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[5:64-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi0_toggle_awrite toggle_axi0awrite = new();
covergroup Interface_axi0_toggle_aread with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[5:64-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi0_toggle_aread toggle_axi0aread = new();
always @(posedge local_ip_pclk) begin
  for(int i=0;i<128;i++) begin
    if (i_rvalid0==1&&i_rready0==1) begin
      toggle_axi0read.sample(i,i_rdata0[i]);
    end
    if (i_wvalid0==1&&i_wready0==1) begin
      toggle_axi0write.sample(i,i_wdata0[i]);
    end
  end
  for(int i=0;i<64;i++) begin
    if (i_arvalid0==1&&i_arready0==1) begin
      toggle_axi0aread.sample(i,i_araddr0[i]);
    end
    if (i_awvalid0==1&&i_awready0==1) begin
      toggle_axi0awrite.sample(i,i_awaddr0[i]);
    end
  end
end
covergroup Interface_axi1 @(posedge (local_ip_aclk));
  coverpoint i_arready1 {bins allowed[]={1};}
  coverpoint i_arvalid1;
  coverpoint i_arburst1 iff(i_arready1==1&&i_arvalid1==1){ bins allowed[]={1};illegal_bins excluded=default;}
  coverpoint i_arsize1  iff(i_arready1==1&&i_arvalid1==1){ bins allowed[]={4};illegal_bins excluded=default;}
  coverpoint i_arid1    iff(i_arready1==1&&i_arvalid1==1){ bins allowed[]={0,1,2,4,5,6,8,9,10,3,11,7};illegal_bins excluded=default;}
  coverpoint i_arlen1   iff(i_arready1==1&&i_arvalid1==1){ bins allowed[]={1,3,5,7,9,11,13,15,31};}
  coverpoint i_awready1 {bins allowed[]={1};}
  coverpoint i_awvalid1;
  coverpoint i_awburst1 iff(i_awready1==1&&i_awvalid1==1){ bins allowed[]={1};illegal_bins excluded=default;}
  coverpoint i_awsize1  iff(i_awready1==1&&i_awvalid1==1){ bins allowed[]={4};illegal_bins excluded=default;}
  coverpoint i_awid1    iff(i_awready1==1&&i_awvalid1==1){ bins allowed[]={0,1,6,9,10,2,7,3,2};illegal_bins excluded=default;}
  coverpoint i_awlen1   iff(i_awready1==1&&i_awvalid1==1){ bins allowed[]={1,3,5,7,9,11,13,15};}
endgroup
Interface_axi1 Interface_axi1_inst = new();
covergroup Interface_axi1_toggle_read with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[0:128-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi1_toggle_read toggle_axi1read = new();
covergroup Interface_axi1_toggle_write with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[0:128-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi1_toggle_write toggle_axi1write = new();
covergroup Interface_axi1_toggle_awrite with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[5:64-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi1_toggle_awrite toggle_axi1awrite = new();
covergroup Interface_axi1_toggle_aread with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[5:64-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi1_toggle_aread toggle_axi1aread = new();
always @(posedge local_ip_pclk) begin
  for(int i=0;i<128;i++) begin
    if (i_rvalid1==1&&i_rready1==1) begin
      toggle_axi1read.sample(i,i_rdata1[i]);
    end
    if (i_wvalid1==1&&i_wready1==1) begin
      toggle_axi1write.sample(i,i_wdata1[i]);
    end
  end
  for(int i=0;i<64;i++) begin
    if (i_arvalid1==1&&i_arready1==1) begin
      toggle_axi1aread.sample(i,i_araddr1[i]);
    end
    if (i_awvalid1==1&&i_awready1==1) begin
      toggle_axi1awrite.sample(i,i_awaddr1[i]);
    end
  end
end
covergroup Interface_axi2 @(posedge (local_ip_aclk));
  coverpoint i_arready2 {bins allowed[]={1};}
  coverpoint i_arvalid2;
  coverpoint i_arburst2 iff(i_arready2==1&&i_arvalid2==1){ bins allowed[]={1,2};illegal_bins excluded=default;}
  coverpoint i_arsize2  iff(i_arready2==1&&i_arvalid2==1){ bins allowed[]={0,2,3,4};illegal_bins excluded=default;}
  coverpoint i_arid2    iff(i_arready2==1&&i_arvalid2==1){ bins allowed[]={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};illegal_bins excluded=default;}
  coverpoint i_arlen2   iff(i_arready2==1&&i_arvalid2==1){ bins allowed[]={3};}
  coverpoint i_awready2 {bins allowed[]={1};}
  coverpoint i_awvalid2;
  coverpoint i_awburst2 iff(i_awready2==1&&i_awvalid2==1){ bins allowed[]={1};illegal_bins excluded=default;}
  coverpoint i_awsize2  iff(i_awready2==1&&i_awvalid2==1){ bins allowed[]={0,2,3,4};illegal_bins excluded=default;}
  coverpoint i_awid2    iff(i_awready2==1&&i_awvalid2==1){ bins allowed[]={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};illegal_bins excluded=default;}
  coverpoint i_awlen2   iff(i_awready2==1&&i_awvalid2==1){ bins allowed[]={3};}
endgroup
Interface_axi2 Interface_axi2_inst = new();
covergroup Interface_axi2_toggle_read with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[0:128-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi2_toggle_read toggle_axi2read = new();
covergroup Interface_axi2_toggle_write with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[0:128-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi2_toggle_write toggle_axi2write = new();
covergroup Interface_axi2_toggle_awrite with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[5:64-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi2_toggle_awrite toggle_axi2awrite = new();
covergroup Interface_axi2_toggle_aread with function sample(int bit_num, bit bit_val);
  coverpoint bit_val {
    bins value[] = {0,1};
    type_option.weight = 0;
  }
  coverpoint bit_num {
    bins bit_number[] = {[5:64-1]};
    type_option.weight = 0;
  }
  cp_bitXval : cross bit_num, bit_val;
endgroup
Interface_axi2_toggle_aread toggle_axi2aread = new();
always @(posedge local_ip_pclk) begin
  for(int i=0;i<128;i++) begin
    if (i_rvalid2==1&&i_rready2==1) begin
      toggle_axi2read.sample(i,i_rdata2[i]);
    end
    if (i_wvalid2==1&&i_wready2==1) begin
      toggle_axi2write.sample(i,i_wdata2[i]);
    end
  end
  for(int i=0;i<64;i++) begin
    if (i_arvalid2==1&&i_arready2==1) begin
      toggle_axi2aread.sample(i,i_araddr2[i]);
    end
    if (i_awvalid2==1&&i_awready2==1) begin
      toggle_axi2awrite.sample(i,i_awaddr2[i]);
    end
  end
end
`endif
`endif
endmodule
