module alg_amba_bufcheck (
  input  logic         clk,
  input  logic         rstn,
  input  logic         init,  
  
  output logic [31:0][31:0] debug,
  
  output logic [63:0]  m_awaddr,
  output logic [1:0]   m_awburst,
  output logic [4:0]   m_awid,
  output logic [7:0]   m_awlen,
  input  logic         m_awready,
  output logic [2:0]   m_awsize,
  output logic         m_awvalid,
  output logic         m_bready,
  input  logic         m_bvalid,
  input  logic         m_bresp,
  input  logic [4:0]   m_bid,
  output logic [127:0] m_wdata,
  output logic [15:0]  m_wstrb,
  output logic         m_wlast,
  input  logic         m_wready,
  output logic         m_wvalid,
  input  logic [63:0]  s_awaddr,
  input  logic [1:0]   s_awburst,
  input  logic [4:0]   s_awid,
  input  logic [7:0]   s_awlen,
  output logic         s_awready,
  input  logic [2:0]   s_awsize,
  input  logic         s_awvalid,
  input  logic         s_bready,
  output logic         s_bvalid,
  output logic         s_bresp,
  output logic [4:0]   s_bid,
  input  logic [127:0] s_wdata,
  input  logic [15:0]  s_wstrb,
  input  logic         s_wlast,
  output logic         s_wready,
  input  logic         s_wvalid,
  output logic  [21:0] paddr,
  output logic         psel,
  output logic         penable,
  output logic  [31:0] pwdata,
  output logic         pwrite,
  input  logic  [31:0] prdata,
  input  logic         pready
);


  
  
    parameter     CBUF_AXIID  = 4;
    parameter     CBUF_WSIZE  = 128;  
    parameter     CBUF_LINES  = 256;  
    parameter     CBUF_PITCH  = 8192; 
    parameter     CBUF_WORDS  = CBUF_LINES*CBUF_PITCH*8/CBUF_WSIZE; 
    localparam    CBUF_L2ADDR = $clog2(CBUF_WORDS);

  
  
    parameter     REG_POSTPROC_TOP  = 32'h00091000;
    localparam    REG_POSTPROC_CMD  = REG_POSTPROC_TOP + 32'h40;

    localparam    [21:0]  ADDR_PPParams  = REG_POSTPROC_CMD + 4*0;
    localparam    [21:0]  ADDR_CbConfig  = REG_POSTPROC_CMD + 4*40;
    localparam    [21:0]  ADDR_PicSize   = REG_POSTPROC_CMD + 4*1;  
    localparam    [21:0]  ADDR_PicPitch  = REG_POSTPROC_CMD + 4*10;
    localparam    [21:0]  ADDR_YBufLsb   = REG_POSTPROC_CMD + 4*2;
    localparam    [21:0]  ADDR_YBufMsb   = REG_POSTPROC_CMD + 4*3;
    localparam    [21:0]  ADDR_C1BufLsb  = REG_POSTPROC_CMD + 4*4;
    localparam    [21:0]  ADDR_C1BufMsb  = REG_POSTPROC_CMD + 4*5;
    localparam    [21:0]  ADDR_C2BufLsb  = REG_POSTPROC_CMD + 4*12;
    localparam    [21:0]  ADDR_C2BufMsb  = REG_POSTPROC_CMD + 4*13;

    localparam    [21:0]  ADDR_CbRdLines = REG_POSTPROC_TOP + 4*12;
    localparam    [21:0]  ADDR_CbWrLines = REG_POSTPROC_TOP + 4*13;
    localparam    [21:0]  ADDR_CbWrPos   = REG_POSTPROC_TOP + 4*14;

    localparam    DelayLastBresp = 1;


  
  
    typedef struct packed {
      logic [63:0]  awaddr;
      logic [1:0]   awburst;
      logic [4:0]   awid;
      logic [7:0]   awlen;
      logic [2:0]   awsize;
      } Req_t;

    typedef struct packed {
      logic [127:0] wdata;
      logic [15:0]  wstrb;
      logic         wlast;
      } Data_t;


    Req_t req_in;
    assign req_in.awaddr  = s_awaddr;
    assign req_in.awburst = s_awburst;
    assign req_in.awid    = s_awid;
    assign req_in.awlen   = s_awlen;
    assign req_in.awsize  = s_awsize;

    Data_t data_in;
    assign data_in.wdata  = s_wdata;
    assign data_in.wstrb  = s_wstrb;
    assign data_in.wlast  = s_wlast;

    wire   req_in_pixl    = req_in.awid==CBUF_AXIID;



  
  
    typedef enum logic [4:0] {FRM_IDLE,FRM_ACTV,FRM_TERM,FRM_WEND,FRM_DONE,FRM_INIT0,FRM_INIT1,FRM_INIT2,RD_PPCFG,RD_PPCMD,RD_PICSZ,RD_PITCH,PP_SIZE,RD_BASE0L,RD_BASE0M,PP_BASE0S,RD_BASE1L,RD_BASE1M,PP_BASE1S,RD_BASE2L,RD_BASE2M,PP_BASE2S} etop_state;

    etop_state top_state,next_top_state;
    wire  top_state_change = top_state!=next_top_state;

    wire  pdone;
    logic pidle;
    logic cb_empty;
    logic pp_cb_enab;
    logic din_last_rxd;
    logic bresp_lvl0;
    logic bresp_idle;

    wire  frm_idle    = top_state==FRM_IDLE;
    wire  frm_actv    = top_state==FRM_ACTV;
    wire  frm_term    = top_state==FRM_TERM;
    wire  frm_wend    = top_state==FRM_WEND;
    wire  frm_init0   = top_state==FRM_INIT0;
    wire  frm_wbuff   = frm_actv &&  pp_cb_enab;
    wire  frm_bypass  = frm_actv && !pp_cb_enab;
    wire  frm_start   = s_awvalid && req_in_pixl && frm_idle && pidle;

    always_comb
    begin
      next_top_state = top_state;
      case(top_state)
        FRM_IDLE:   if(frm_start)   next_top_state = RD_PPCFG;
        RD_PPCFG:   if(pdone)       next_top_state = RD_PPCMD;
        RD_PPCMD:   if(pdone)       next_top_state = RD_PICSZ;
        RD_PICSZ:   if(pdone)       next_top_state = RD_PITCH;
        RD_PITCH:   if(pdone)       next_top_state = PP_SIZE;
        PP_SIZE :                   next_top_state = RD_BASE0L;
        RD_BASE0L:  if(pdone)       next_top_state = RD_BASE0M;
        RD_BASE0M:  if(pdone)       next_top_state = PP_BASE0S;
        PP_BASE0S:                  next_top_state = RD_BASE1L;
        RD_BASE1L:  if(pdone)       next_top_state = RD_BASE1M;
        RD_BASE1M:  if(pdone)       next_top_state = PP_BASE1S;
        PP_BASE1S:                  next_top_state = RD_BASE2L;
        RD_BASE2L:  if(pdone)       next_top_state = RD_BASE2M;
        RD_BASE2M:  if(pdone)       next_top_state = PP_BASE2S;
        PP_BASE2S:                  next_top_state = FRM_INIT0;
        FRM_INIT0:                  next_top_state = FRM_ACTV;
        FRM_ACTV:   if(din_last_rxd)next_top_state = pp_cb_enab?FRM_TERM:FRM_WEND;
        FRM_TERM:   if(cb_empty)    next_top_state = FRM_WEND;
        FRM_WEND:   if(bresp_lvl0)  next_top_state = FRM_DONE;
        FRM_DONE:   if(bresp_idle)  next_top_state = FRM_IDLE;
      endcase
    end

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)    top_state <= FRM_IDLE;
    else if(init) top_state <= FRM_IDLE;
    else          top_state <= next_top_state;

   
    logic top_preq,top_preq_nxt;
    always_comb
    begin
      case(next_top_state)
        RD_PPCFG:   top_preq_nxt = 1'b1;
        RD_PPCMD:   top_preq_nxt = 1'b1;
        RD_PICSZ:   top_preq_nxt = 1'b1;
        RD_PITCH:   top_preq_nxt = 1'b1;
        RD_BASE0L:  top_preq_nxt = 1'b1;
        RD_BASE0M:  top_preq_nxt = 1'b1;
        RD_BASE1L:  top_preq_nxt = 1'b1;
        RD_BASE1M:  top_preq_nxt = 1'b1;
        RD_BASE2L:  top_preq_nxt = 1'b1;
        RD_BASE2M:  top_preq_nxt = 1'b1;
        default:    top_preq_nxt = 1'b0;
      endcase
    end

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)    top_preq <= 1'b0;
    else if(init) top_preq <= 1'b0;
    else          top_preq <= top_preq_nxt && top_state_change;


   
   
    reg [3:0][31:0] cb_cfg;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)      cb_cfg <= '0;
    else if(pdone)
      case(top_state)
        RD_PPCFG:  cb_cfg[0] <= prdata;
        RD_PICSZ:  cb_cfg[1] <= prdata;
        RD_PITCH:  cb_cfg[2] <= prdata;
        RD_PPCMD:  cb_cfg[3] <= prdata;
      endcase

    assign      pp_cb_enab    = cb_cfg[0][31];
    wire [15:0] pp_cb_lines   = cb_cfg[0][15: 0];
    wire [15:0] pp_pic_wdth   = cb_cfg[1][15: 0];
    wire [15:0] pp_pic_hght   = cb_cfg[1][31:16];
    wire [19:0] pp_pic_pitch  = cb_cfg[2][19: 0];
    wire [ 1:0] pp_out_bdepth = cb_cfg[3][30:28];
    wire [ 1:0] pp_out_fmt    = cb_cfg[3][27:26];
    wire        pp_out_packd  = cb_cfg[3][22];

    wire [15:0] pp_cb_lines_max = (pp_cb_lines > pp_pic_hght)? pp_pic_hght:pp_cb_lines;

    wire [15:0] pp_wdth_rnd   = (pp_pic_wdth+63)&16'hFFC0;                
  
    wire [ 1:0] pp_last_plane =  pp_out_packd?0:2;
    wire [ 2:0] pp_wdth_scale =  pp_out_packd?4:|pp_out_bdepth?2:1;
    wire [15:0] pp_wdth_bytes =  pp_wdth_rnd*pp_wdth_scale;
    wire [15:4] pp_wdth_wrds  =  pp_wdth_bytes[15:4];                     
    wire [15:4] pp_ptch_wrds  =  pp_pic_pitch[15:4]+(|pp_pic_pitch[3:0]); 

    reg  [31:0] pp_pic_wrds;
    reg  [31:0] pp_pic_wrds_sel;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)         pp_pic_wrds <= '0;
    else if(frm_init0) pp_pic_wrds <= pp_out_packd?(pp_wdth_wrds*pp_pic_hght):pp_pic_wrds_sel;

    wire [31:0] pp_pic_wrds_400 =  (pp_wdth_wrds*pp_pic_hght);
    wire [31:0] pp_pic_wrds_420 = ((pp_wdth_wrds*pp_pic_hght)*3)>>1;
    wire [31:0] pp_pic_wrds_422 =  (pp_wdth_wrds*pp_pic_hght)*2;
    wire [31:0] pp_pic_wrds_444 =  (pp_wdth_wrds*pp_pic_hght)*3;
    always_comb
    begin
      case(pp_out_fmt)
        2'd3:    pp_pic_wrds_sel = pp_pic_wrds_444;
        2'd2:    pp_pic_wrds_sel = pp_pic_wrds_422;
        2'd1:    pp_pic_wrds_sel = pp_pic_wrds_420;
        default: pp_pic_wrds_sel = pp_pic_wrds_400;
      endcase
    end

    reg [31:0] pp_pln_wrds;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)         pp_pln_wrds <= '0;
    else if(frm_init0) pp_pln_wrds <= pp_wdth_wrds*pp_pic_hght;

    reg [2:0][1:0][31:0] pp_base_addr;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)      pp_base_addr <= '0;
    else if(pdone)
      case(top_state)
        RD_BASE0L: pp_base_addr[0][0] <= prdata;
        RD_BASE0M: pp_base_addr[0][1] <= prdata;
        RD_BASE1L: pp_base_addr[1][0] <= prdata;
        RD_BASE1M: pp_base_addr[1][1] <= prdata;
        RD_BASE2L: pp_base_addr[2][0] <= prdata;
        RD_BASE2M: pp_base_addr[2][1] <= prdata;
      endcase

    reg      [31:0] pp_cb_size;
    reg [2:0][63:0] pp_last_addr;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)     {pp_last_addr,pp_cb_size} <= '0;
    else
      case(top_state)
        PP_SIZE:   pp_cb_size      <= pp_cb_lines_max*pp_pic_pitch;
        PP_BASE0S: pp_last_addr[0] <= pp_base_addr[0]+pp_cb_size;
        PP_BASE1S: pp_last_addr[1] <= pp_base_addr[1]+pp_cb_size;
        PP_BASE2S: pp_last_addr[2] <= pp_base_addr[2]+pp_cb_size;
      endcase

  
    wire     [31:0] hw_cb_size_words = CBUF_WORDS;
    wire     [31:0] pp_cb_size_words = (pp_cb_size[31:4] + |pp_cb_size[3:0])>>pp_out_packd;
    wire            pp_cb_size_ovf   = (pp_cb_size_words > hw_cb_size_words)?1:0;

  
  
  
  
  
    logic [15:0] pp_upd_count;
    wire         up_cnt_last  = pp_upd_count==1024;
    wire         inc_upd_cnt  = frm_wbuff|frm_term;
    wire         upd_wlines   = up_cnt_last;

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)            pp_upd_count <= 0;
    else if(init)         pp_upd_count <= 0;
    else if(inc_upd_cnt)  pp_upd_count <= up_cnt_last?0:pp_upd_count+1;


    reg [15:0] pp_lines_wrote;
    wire       upd_pp_wrote  = pdone && paddr==ADDR_CbWrLines;
    wire       set_pp_wrote  = din_last_rxd && pp_cb_enab;

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)            pp_lines_wrote <= '0;
    else if(frm_start)    pp_lines_wrote <= '0;
    else if(set_pp_wrote) pp_lines_wrote <= pp_pic_hght;  
    else if(upd_pp_wrote) pp_lines_wrote <= prdata;


  
  
    typedef enum logic [3:0] {P_IDLE, P_SEL, P_ENAB,P_DONE}    apb_state;
    apb_state    pstate,next_pstate;
    logic        pstart;
    
    logic        upd_rlines_req;
    logic        upd_rlines_pend;
    logic [31:0] upd_rlines_val;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)              upd_rlines_pend <= 1'b0;
    else if(upd_rlines_req) upd_rlines_pend <= 1'b1;
    else if(pstart)         upd_rlines_pend <= 1'b0;
    
  
    wire         upd_status_req = (s_awready && s_awvalid && frm_actv);
    logic        upd_status_pend;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)              upd_status_pend <= 1'b0;
    else if(upd_status_req) upd_status_pend <= 1'b1;
    else if(pstart)         upd_status_pend <= 1'b0;
    
    assign pidle   = pstate==P_IDLE;
    assign pstart  = pstate==P_IDLE && (top_preq || upd_wlines || upd_rlines_pend || upd_status_pend);
    assign pdone   = pstate==P_DONE;
    assign penable = pstate==P_ENAB;
    assign psel    = pstate==P_ENAB || pstate==P_SEL;
    
    always_comb
    begin
      next_pstate = pstate;
      case(pstate)
        P_IDLE:  if(pstart) next_pstate = P_SEL;
        P_SEL:              next_pstate = P_ENAB;
        P_ENAB:  if(pready) next_pstate = P_DONE;
        default:            next_pstate = P_IDLE;
      endcase
    end
    
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn) pstate <= P_IDLE;
    else       pstate <= next_pstate;
    
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)              {paddr,pwrite,pwdata} <= 0;
    else if(pdone)          {paddr,pwrite,pwdata} <= 0;
    else if(pstart)
    begin
           if(upd_rlines_pend) {paddr,pwrite,pwdata} <= {ADDR_CbRdLines,1'b1,upd_rlines_val};
      else if(upd_status_pend) {paddr,pwrite,pwdata} <= {ADDR_CbRdLines,1'b1,upd_rlines_val};
      else
      begin
        case(next_top_state)
          RD_PPCFG:  {paddr,pwrite,pwdata} <= {ADDR_CbConfig, 1'b0,32'b0};
          RD_PPCMD:  {paddr,pwrite,pwdata} <= {ADDR_PPParams, 1'b0,32'b0};
          RD_PICSZ:  {paddr,pwrite,pwdata} <= {ADDR_PicSize,  1'b0,32'b0};
          RD_PITCH:  {paddr,pwrite,pwdata} <= {ADDR_PicPitch, 1'b0,32'b0};
          RD_BASE0L: {paddr,pwrite,pwdata} <= {ADDR_YBufLsb , 1'b0,32'b0};
          RD_BASE0M: {paddr,pwrite,pwdata} <= {ADDR_YBufMsb , 1'b0,32'b0};
          RD_BASE1L: {paddr,pwrite,pwdata} <= {ADDR_C1BufLsb, 1'b0,32'b0};
          RD_BASE1M: {paddr,pwrite,pwdata} <= {ADDR_C1BufMsb, 1'b0,32'b0};
          RD_BASE2L: {paddr,pwrite,pwdata} <= {ADDR_C2BufLsb, 1'b0,32'b0};
          RD_BASE2M: {paddr,pwrite,pwdata} <= {ADDR_C2BufMsb, 1'b0,32'b0};
          default:   {paddr,pwrite,pwdata} <= {ADDR_CbWrLines,1'b0,32'b0};
        endcase
      end
    end


  
  
    typedef enum logic [3:0] {DIN_IDLE, DIN_CHECK,DIN_STORE,DIN_BYPASS}     eDinState;
    eDinState din_state,next_din_state;

    wire req_d1_pixl;
    wire din_strb      = s_wvalid && s_wready;
    wire din_cb_strb   = s_wvalid && s_wready && req_d1_pixl;
    wire din_strb_last = din_strb && s_wlast;

    wire st_idle       = din_state == DIN_IDLE;
    wire st_check      = din_state == DIN_CHECK;
    wire st_bypass     = din_state == DIN_BYPASS;
    wire st_store      = din_state == DIN_STORE;
    wire store_done    = st_store && din_strb_last;

    logic [2:0] hit_cbuf;
    logic       axi_busy;
    logic       cbuf_busy;
    wire        chk_wait  = |hit_cbuf ? cbuf_busy : axi_busy;
    wire        load_cmd  = (frm_actv |!req_in_pixl) && s_awvalid && st_idle;
    assign      s_awready = (frm_actv |!req_in_pixl) && st_idle;

    always_comb
    begin
      next_din_state = din_state;
      case(din_state)
        DIN_IDLE:      if(load_cmd)      next_din_state = DIN_CHECK;
        DIN_CHECK:     if(!chk_wait)     next_din_state =~|hit_cbuf ? DIN_BYPASS:DIN_STORE;
        DIN_STORE:     if(din_strb_last) next_din_state = DIN_IDLE;
        DIN_BYPASS:    if(din_strb_last) next_din_state = DIN_IDLE;
      endcase
    end

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)    din_state <= DIN_IDLE;
    else if(init) din_state <= DIN_IDLE;
    else          din_state <= next_din_state;

    Req_t req_d1;
    always_ff @ (posedge clk or negedge rstn)
    if(!rstn)         req_d1  <= '0;
    else if(load_cmd) req_d1  <= req_in;

    logic store_done_1d;
    always_ff @ (posedge clk or negedge rstn)
    if(!rstn)         store_done_1d  <= '0;
    else              store_done_1d  <= store_done;

    assign req_d1_pixl = req_d1.awid==CBUF_AXIID;

   
    logic [2:0][63:0] base_diff,base_diff_nxt;
    logic [2:0][63:0] last_diff,last_diff_nxt;

    always_comb
    begin
      base_diff_nxt[0] <= req_d1.awaddr - pp_base_addr[0];
      base_diff_nxt[1] <= req_d1.awaddr - pp_base_addr[1];
      base_diff_nxt[2] <= req_d1.awaddr - pp_base_addr[2];
      last_diff_nxt[0] <= req_d1.awaddr - pp_last_addr[0];
      last_diff_nxt[1] <= req_d1.awaddr - pp_last_addr[1];
      last_diff_nxt[2] <= req_d1.awaddr - pp_last_addr[2];
    end

    always_ff @ (posedge clk or negedge rstn)
    if(!rstn)         {base_diff,last_diff} <= '0;
    else if(st_check)
    begin
      base_diff[0] <= base_diff_nxt[0];
      base_diff[1] <= base_diff_nxt[1];
      base_diff[2] <= base_diff_nxt[2];
      last_diff[0] <= last_diff_nxt[0];
      last_diff[1] <= last_diff_nxt[1];
      last_diff[2] <= last_diff_nxt[2];
    end

    
    assign hit_cbuf[0] = !base_diff_nxt[0][63] && last_diff_nxt[0][63] && req_d1_pixl && !frm_bypass;
    assign hit_cbuf[1] = !base_diff_nxt[1][63] && last_diff_nxt[1][63] && req_d1_pixl && !frm_bypass && !pp_out_packd;
    assign hit_cbuf[2] = !base_diff_nxt[2][63] && last_diff_nxt[2][63] && req_d1_pixl && !frm_bypass && !pp_out_packd;

    logic [1:0] din_pln;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)        din_pln <= 0;
    else if(st_check) din_pln <= hit_cbuf[2]?2'd2:hit_cbuf[1]?2'd1:2'd0;

   
   
    logic [2:0][31:0] din_pln_wrds;
    wire  [31:0]      din_pln_wrds_p1 = din_pln_wrds[din_pln]+1'b1;

    always_ff @ (posedge clk or negedge rstn)
    if(!rstn)            din_pln_wrds          <= '0;
    else if(frm_start)   din_pln_wrds          <= '0;
    else if(din_cb_strb) din_pln_wrds[din_pln] <= din_pln_wrds_p1;

    always_ff @ (posedge clk or negedge rstn)
    if(!rstn)            din_last_rxd <= '0;
    else if(frm_start)   din_last_rxd <= '0;
    else if(din_cb_strb) din_last_rxd <= pp_cb_enab?(din_pln==pp_last_plane && din_pln_wrds_p1==pp_pln_wrds):(din_pln_wrds_p1==pp_pic_wrds);



  
  
    logic [15:0] cb_lines_avail;
    logic [15:0] cb_pace_count;
    logic        cb_clr_pace;
  
    wire         cb_pace_done = cb_pace_count==2;
    wire         inc_pace = |cb_lines_avail && !cb_pace_done && pp_cb_enab;

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)          cb_pace_count <= 0;
    else if(init)       cb_pace_count <= 0;
    else if(cb_clr_pace)cb_pace_count <= 0;
    else if(inc_pace)   cb_pace_count <= cb_pace_count+1;

   
    typedef enum logic [3:0] {CB_IDLE,CB_STORE,CB_DREQ,CB_DUMP}   eCbState;
    eCbState cb_state,next_cb_state;

    logic  dout_strb_last;
    wire   st_cb_idle    = cb_state==CB_IDLE;
    wire   st_cb_store   = cb_state==CB_STORE;
    wire   st_cb_dreq    = cb_state==CB_DREQ;
    wire   st_cb_dump    = cb_state==CB_DUMP;

    logic  cb_dreq_ready;
    logic  cb_rd_brst_done;
    wire   cb_store_trig = st_cb_idle && st_check && |hit_cbuf;
    wire   cb_dump_trig  = st_cb_idle && cb_pace_done && !cb_store_trig;
    wire   cb_trig       = cb_store_trig || cb_dump_trig;
    assign cb_clr_pace   = !st_cb_idle;

    logic [9:0]  cb_rd_xloc;
    logic  data_fifo_stall;
    wire   cb_wren       = st_cb_store && s_wvalid;
    wire   cb_rden       = st_cb_dump  && !data_fifo_stall && (|cb_rd_xloc[1:0] || m_awready); 
    assign cbuf_busy     = !st_cb_idle;


    always_comb
    begin
      next_cb_state = cb_state;
      case(cb_state)
        CB_IDLE:     if(cb_trig)          next_cb_state = cb_store_trig?CB_STORE:CB_DREQ;
        CB_STORE:    if(din_strb_last)    next_cb_state = CB_IDLE;
        CB_DREQ:     if(cb_dreq_ready)    next_cb_state = CB_DUMP;
        CB_DUMP:     if(cb_rd_brst_done)  next_cb_state = CB_IDLE;
      endcase
    end

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)    cb_state <= CB_IDLE;
    else if(init) cb_state <= CB_IDLE;
    else          cb_state <= next_cb_state;



   
   
    logic [CBUF_L2ADDR:0] cb_waddr;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)              cb_waddr <=  0;
    else if(cb_store_trig)  cb_waddr <= (hit_cbuf[0]?base_diff_nxt[0]:hit_cbuf[1]?base_diff_nxt[1]:base_diff_nxt[2])>>4;
    else if(cb_wren)        cb_waddr <=  cb_waddr+1;


   
   
  
    wire  [11:0] cb_rd_xloc_p1   = cb_rd_xloc+1;
    wire         cb_rd_xloc_last = cb_rd_xloc_p1==pp_wdth_wrds;
    wire         cb_rd_row_done  = cb_rden &&  cb_rd_xloc_last;
    wire         cb_rd_upd_mask  = cb_rd_row_done && !pp_out_packd;
    assign       cb_rd_brst_done = cb_rden && &cb_rd_xloc[1:0];

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)              cb_rd_xloc <= 0;
    else if(frm_start)      cb_rd_xloc <= 0;
    else if(cb_rden)        cb_rd_xloc <= cb_rd_xloc_last?0:cb_rd_xloc_p1;

    logic [2:0] cb_rd_mask;
    wire        cb_rd_line_done = cb_rd_row_done && (pp_out_packd|cb_rd_mask[2]);
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)              cb_rd_mask <= 3'b001;
    else if(frm_start)      cb_rd_mask <= 3'b001;
    else if(cb_rd_upd_mask) cb_rd_mask <= {cb_rd_mask[1:0],cb_rd_mask[2]};


    logic [15:0] cb_rd_pic_line;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)              cb_rd_pic_line <= 0;
    else if(frm_start)      cb_rd_pic_line <= 0;
    else if(cb_rd_line_done)cb_rd_pic_line <= cb_rd_pic_line+1;


    assign cb_lines_avail = pp_lines_wrote-cb_rd_pic_line;
    assign cb_empty       = ~|cb_lines_avail;

    logic [15:0] cb_rd_buf_line;
    wire  [15:0] cb_rd_buf_line_p1 = cb_rd_buf_line+1;
    wire         cb_rd_buf_line_last = cb_rd_buf_line_p1==pp_cb_lines_max;

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)              cb_rd_buf_line <= 0;
    else if(frm_start)      cb_rd_buf_line <= 0;
    else if(cb_rd_line_done)cb_rd_buf_line <= cb_rd_buf_line_last?0:cb_rd_buf_line_p1;


   
    assign upd_rlines_req = cb_rd_line_done;
  
  
    wire [14:0] bufcheck_status;
    assign upd_rlines_val = cb_rd_pic_line + (bufcheck_status<<17); 

   
    logic [CBUF_L2ADDR:0] cb_raddr;
  
    wire  [CBUF_L2ADDR:0] cb_raddr_nxt = cb_rd_buf_line*pp_ptch_wrds+cb_rd_xloc;
    wire  [CBUF_L2ADDR:0] cb_raddr_p1  = cb_raddr+1;

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)            cb_raddr <= 0;
    else if(cb_dump_trig) cb_raddr <= cb_raddr_nxt;
    else if(cb_rden)      cb_raddr <= cb_raddr_p1;

   
  
    wire  [31:0]  cb_out_offs_nxt = cb_rd_pic_line*pp_ptch_wrds+cb_rd_xloc;
    wire  [63:0]  cb_out_base_nxt = cb_rd_mask[0]?pp_base_addr[0]:cb_rd_mask[1]?pp_base_addr[1]:pp_base_addr[2];
    wire  [63:0]  cb_out_addr_nxt = cb_out_base_nxt+cb_out_offs_nxt*16;

    Req_t req_cbuf;
    always_ff @ (posedge clk or negedge rstn)
    if(!rstn)             req_cbuf  <= '0;
    else if(cb_dump_trig)
    begin
      req_cbuf.awaddr   <= cb_out_addr_nxt;
      req_cbuf.awburst  <= 1; 
      req_cbuf.awsize   <= 4; 
      req_cbuf.awid     <= CBUF_AXIID;
      req_cbuf.awlen    <= 3; 
    end


   
   
    logic [71:0] alg_ram_cbuf_0_q_h;
    logic [71:0] alg_ram_cbuf_0_q_l;
    logic [71:0] alg_ram_cbuf_1_q_h;
    logic [71:0] alg_ram_cbuf_1_q_l;
    logic [71:0] alg_ram_cbuf_2_q_h;
    logic [71:0] alg_ram_cbuf_2_q_l;
    logic [71:0] alg_ram_cbuf_0_data_h;
    logic [71:0] alg_ram_cbuf_0_data_l;
    logic [71:0] alg_ram_cbuf_1_data_h;
    logic [71:0] alg_ram_cbuf_1_data_l;
    logic [71:0] alg_ram_cbuf_2_data_h;
    logic [71:0] alg_ram_cbuf_2_data_l;
    logic [CBUF_L2ADDR-1:0] alg_ram_cbuf_0_addr;
    logic [CBUF_L2ADDR-1:0] alg_ram_cbuf_1_addr;
    logic [CBUF_L2ADDR-1:0] alg_ram_cbuf_2_addr;
    alg_amba_uram #(.NUM_WORD(CBUF_WORDS)) I_ALG_RAM_CBUF0_HIGH (
      .clk  (clk),
      .wren (alg_ram_cbuf_0_wren),
      .rden (alg_ram_cbuf_0_rden),
      .addr (alg_ram_cbuf_0_addr),
      .data (alg_ram_cbuf_0_data_h),
      .q    (alg_ram_cbuf_0_q_h)
    );
    alg_amba_uram #(.NUM_WORD(CBUF_WORDS)) I_ALG_RAM_CBUF0_LOW (
      .clk  (clk),
      .wren (alg_ram_cbuf_0_wren),
      .rden (alg_ram_cbuf_0_rden),
      .addr (alg_ram_cbuf_0_addr),
      .data (alg_ram_cbuf_0_data_l),
      .q    (alg_ram_cbuf_0_q_l)
    );
    alg_amba_uram #(.NUM_WORD(CBUF_WORDS)) I_ALG_RAM_CBUF1_HIGH (
      .clk  (clk),
      .wren (alg_ram_cbuf_1_wren),
      .rden (alg_ram_cbuf_1_rden),
      .addr (alg_ram_cbuf_1_addr),
      .data (alg_ram_cbuf_1_data_h),
      .q    (alg_ram_cbuf_1_q_h)
    );
    alg_amba_uram #(.NUM_WORD(CBUF_WORDS)) I_ALG_RAM_CBUF1_LOW (
      .clk  (clk),
      .wren (alg_ram_cbuf_1_wren),
      .rden (alg_ram_cbuf_1_rden),
      .addr (alg_ram_cbuf_1_addr),
      .data (alg_ram_cbuf_1_data_l),
      .q    (alg_ram_cbuf_1_q_l)
    );
    alg_amba_uram #(.NUM_WORD(CBUF_WORDS)) I_ALG_RAM_CBUF2_HIGH (
      .clk  (clk),
      .wren (alg_ram_cbuf_2_wren),
      .rden (alg_ram_cbuf_2_rden),
      .addr (alg_ram_cbuf_2_addr),
      .data (alg_ram_cbuf_2_data_h),
      .q    (alg_ram_cbuf_2_q_h)
    );
    alg_amba_uram #(.NUM_WORD(CBUF_WORDS)) I_ALG_RAM_CBUF2_LOW (
      .clk  (clk),
      .wren (alg_ram_cbuf_2_wren),
      .rden (alg_ram_cbuf_2_rden),
      .addr (alg_ram_cbuf_2_addr),
      .data (alg_ram_cbuf_2_data_l),
      .q    (alg_ram_cbuf_2_q_l)
    );

    
    wire [2:0] ch_rd_sel = pp_out_packd ? (cb_raddr[0]?3'b010:3'b001) : cb_rd_mask;
    wire [2:0] ch_wr_sel = pp_out_packd ? (cb_waddr[0]?3'b010:3'b001) : hit_cbuf;

    assign alg_ram_cbuf_0_wren =  cb_wren && ch_wr_sel[0];
    assign alg_ram_cbuf_0_rden =  cb_rden && ch_rd_sel[0];
    assign alg_ram_cbuf_0_addr = (cb_wren ?  cb_waddr : cb_raddr)>>pp_out_packd;
    assign alg_ram_cbuf_0_data_l = {8'h00,s_wdata[63:0]};
    assign alg_ram_cbuf_0_data_h = {8'h00,s_wdata[127:64]};

    assign alg_ram_cbuf_1_wren =  cb_wren && ch_wr_sel[1];
    assign alg_ram_cbuf_1_rden =  cb_rden && ch_rd_sel[1];
    assign alg_ram_cbuf_1_addr = (cb_wren ?  cb_waddr : cb_raddr)>>pp_out_packd;
    assign alg_ram_cbuf_1_data_l = {8'h00,s_wdata[63:0]};
    assign alg_ram_cbuf_1_data_h = {8'h00,s_wdata[127:64]};

    assign alg_ram_cbuf_2_wren =  cb_wren && ch_wr_sel[2];
    assign alg_ram_cbuf_2_rden =  cb_rden && ch_rd_sel[2];
    assign alg_ram_cbuf_2_addr = (cb_wren ?  cb_waddr : cb_raddr)>>pp_out_packd;
    assign alg_ram_cbuf_2_data_l = {8'h00,s_wdata[63:0]};
    assign alg_ram_cbuf_2_data_h = {8'h00,s_wdata[127:64]};


    logic ram_rden_1d;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)        ram_rden_1d <= 0;
    else              ram_rden_1d <= cb_rden;

    logic ram_last_1d;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)        ram_last_1d <= 0;
    else              ram_last_1d <= cb_rden && &cb_rd_xloc[1:0]; 

    logic [2:0] ram_mask_1d;
    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)        ram_mask_1d <= 0;
    else              ram_mask_1d <= ch_rd_sel;

    wire [127:0]  ram_rdata = ram_mask_1d[0]?{alg_ram_cbuf_0_q_h[63:0],alg_ram_cbuf_0_q_l[63:0]}:ram_mask_1d[1]?{alg_ram_cbuf_1_q_h[63:0],alg_ram_cbuf_1_q_l[63:0]}:{alg_ram_cbuf_2_q_h[63:0],alg_ram_cbuf_2_q_l[63:0]};


  
  
    typedef enum logic [3:0] {X_IDLE,X_AREQ,X_WDATA}     axi_state;
    axi_state xstate,next_xstate;

    wire   st_x_idle     =  xstate==X_IDLE;
    wire   st_x_areq     =  xstate==X_AREQ;
    wire   st_x_data     =  xstate==X_WDATA;

    wire   load_byp_cmd  =  st_x_idle && st_check && ~|hit_cbuf;
    wire   load_cbuf_cmd =  st_x_idle && st_cb_dreq && !load_byp_cmd;
    wire   load_xcmd     =  load_byp_cmd || load_cbuf_cmd;
    wire   dout_actv     =  xstate==X_WDATA;
    assign cb_dreq_ready =  st_x_idle && !load_byp_cmd;
    assign axi_busy      = !st_x_idle;


    logic  xstrb_last;

    always_comb
    begin
      next_xstate = xstate;
      case(xstate)
        X_IDLE:  if(load_xcmd)    next_xstate = X_AREQ;
        X_AREQ:  if(m_awready)    next_xstate = X_WDATA;
        X_WDATA: if(xstrb_last)   next_xstate = X_IDLE;
      endcase
    end

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)    xstate <= X_IDLE;
    else if(init) xstate <= X_IDLE;
    else          xstate <= next_xstate;


    Req_t req_out;
    always_ff @ (posedge clk or negedge rstn)
    if(!rstn)               req_out <= 0;
    else if(init)           req_out <= 0;
    else if(load_byp_cmd)   req_out <= req_d1;
    else if(load_cbuf_cmd)  req_out <= req_cbuf;


    assign m_awaddr  = req_out.awaddr ;
    assign m_awburst = req_out.awburst;
    assign m_awid    = req_out.awid   ;
    assign m_awlen   = req_out.awlen  ;
    assign m_awsize  = req_out.awsize ;
    assign m_awvalid = st_x_areq;


  
  
    localparam DataFifoWrds = 3;
    localparam DataFifoBW   = $bits(Data_t);
    localparam DataFifoAW   = $clog2(DataFifoWrds);

    logic  data_fifo_wr_full;
    logic  data_fifo_wr_push;
    Data_t data_fifo_wr_data;

    logic  data_fifo_rd_accept;
    logic  data_fifo_rd_empty;
    Data_t data_fifo_rd_data;
    wire   data_fifo_rd_avail = ~data_fifo_rd_empty;

    alg_amba_fifo_fwft
      #(.FIFO_WIDTH      (DataFifoBW      ),
        .FIFO_LOG2_DEPTH (2               )
      )
      data_fifo
      (
        .clk          (clk                   ),
        .rstn         (rstn                  ),
        
        .wreq         (data_fifo_wr_push     ),
        .wfull        (data_fifo_wr_full     ),
        .wdata        (data_fifo_wr_data     ),
        
        .rreq         (data_fifo_rd_accept   ),
        .rempty       (data_fifo_rd_empty    ),
        .rdata        (data_fifo_rd_data     )
      );

   
    assign data_fifo_wr_push       = (s_wvalid && st_bypass) || (dout_actv && ram_rden_1d);
    assign data_fifo_wr_data.wdata = st_bypass ? s_wdata : ram_rdata;
    assign data_fifo_wr_data.wstrb = st_bypass ? s_wstrb : '1;
    assign data_fifo_wr_data.wlast = st_bypass ? s_wlast : ram_last_1d;

    assign s_wready = (!data_fifo_wr_full && st_bypass) || st_cb_store;

   
    assign m_wdata    = dout_actv ? data_fifo_rd_data.wdata:'0;
    assign m_wstrb    = dout_actv ? data_fifo_rd_data.wstrb:'0;
    assign m_wlast    = dout_actv ? data_fifo_rd_data.wlast:'0;
    assign m_wvalid   = dout_actv ? data_fifo_rd_avail:0;

    assign data_fifo_rd_accept = dout_actv?m_wready:1'b0;

    wire   dout_strb      = m_wvalid&&m_wready;
    assign xstrb_last     = m_wvalid&&m_wready&&m_wlast;
    assign dout_strb_last = dout_actv&&xstrb_last;

   
    
    
    reg [DataFifoAW:0] data_fifo_lvl;
    wire               data_fifo_incr = data_fifo_wr_push && !data_fifo_wr_full;
    wire               data_fifo_decr = data_fifo_rd_accept && !data_fifo_rd_empty;

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)    data_fifo_lvl <= 0;
    else if(init) data_fifo_lvl <= 0;
    else          data_fifo_lvl <= data_fifo_lvl + data_fifo_incr - data_fifo_decr;

    assign        data_fifo_stall = (data_fifo_lvl+data_fifo_incr)==DataFifoWrds;


  
  
    typedef enum logic [2:0] {B_IDLE, B_MASTER, B_WAIT} bresp_state;
    bresp_state bstate,next_bstate;

    wire   dump_bresp    =  pp_cb_enab && m_bid==CBUF_AXIID;
    wire   load_m_bresp  =  m_bvalid && m_bready && !dump_bresp;
    wire   load_cb_bresp = DelayLastBresp?((store_done_1d && !din_last_rxd) || (frm_wend && bresp_lvl0)):store_done_1d;
    wire   load_bresp    =  load_m_bresp | load_cb_bresp;
    assign bresp_idle    =  bstate==B_IDLE;

    assign s_bvalid      =  bstate==B_MASTER;
    assign m_bready      = (bstate==B_IDLE && !(load_cb_bresp || store_done)) || dump_bresp; 

    always_comb
    begin
      next_bstate = bstate;
      case(bstate)
        B_IDLE:     if(load_bresp)     next_bstate = B_MASTER;
        B_MASTER:   if(s_bready)       next_bstate = B_IDLE;
      endcase
    end

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)             bstate <= B_IDLE;
    else if(init)          bstate <= B_IDLE;
    else                   bstate <= next_bstate;

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)            {s_bresp,s_bid} <= 0;
    else if(load_m_bresp) {s_bresp,s_bid} <= {m_bresp,m_bid};
    else if(load_cb_bresp){s_bresp,s_bid} <= {1'b0,CBUF_AXIID[4:0]};

   
    logic [31:0] bresp_lvl;
    wire         bresp_incr  =  m_awvalid && m_awready && m_awid==CBUF_AXIID;
    wire         bresp_decr  =  m_bvalid  && m_bready  && m_bid==CBUF_AXIID;
    assign       bresp_lvl0  = ~|bresp_lvl;

    always_ff @ (posedge clk, negedge rstn)
    if (!rstn)    bresp_lvl <= 0;
    else if(init) bresp_lvl <= 0;
    else          bresp_lvl <= bresp_lvl + bresp_incr - bresp_decr;

    assign bufcheck_status = {pp_cb_size_ovf,|xstate,cb_state,din_state,top_state};

   
   
   
    

    
    
     wire        dbgm_astrb = m_awvalid && m_awready;
     wire        dbgm_bstrb = m_bvalid  && m_bready;
     wire [5:0]  dbgm_aid   = m_awid;
     wire [5:0]  dbgm_bid   = m_bid;

     logic [31:0][7:0] dbgm_num_aid;
     always @(posedge clk or negedge rstn)
     if(!rstn)           dbgm_num_aid   <= 0;
     else if(dbgm_astrb)  dbgm_num_aid[dbgm_aid] <= dbgm_num_aid[dbgm_aid]+1;

     logic [31:0][7:0] dbgm_num_bid;
     always @(posedge clk or negedge rstn)
     if(!rstn)           dbgm_num_bid   <= 0;
     else if(dbgm_bstrb)  dbgm_num_bid[dbgm_bid] <= dbgm_num_bid[dbgm_bid]+1;

     logic signed [31:0][7:0] dbgm_num_out;
     always_comb
     for(int i=0;i<32;i++)
     begin
       dbgm_num_out[i] = dbgm_num_aid[i]-dbgm_num_bid[i];
     end


    
    
     wire        dbgs_astrb = s_awvalid && s_awready;
     wire        dbgs_bstrb = s_bvalid  && s_bready;
     wire [5:0]  dbgs_aid   = s_awid;
     wire [5:0]  dbgs_bid   = s_bid;

     logic [31:0][7:0] dbgs_num_aid;
     always @(posedge clk or negedge rstn)
     if(!rstn)           dbgs_num_aid   <= 0;
     else if(dbgs_astrb)  dbgs_num_aid[dbgs_aid] <= dbgs_num_aid[dbgs_aid]+1;

     logic [31:0][7:0] dbgs_num_bid;
     always @(posedge clk or negedge rstn)
     if(!rstn)           dbgs_num_bid   <= 0;
     else if(dbgs_bstrb)  dbgs_num_bid[dbgs_bid] <= dbgs_num_bid[dbgs_bid]+1;

     logic signed [31:0][7:0] dbgs_num_out;
     always_comb
     for(int i=0;i<32;i++)
     begin
       dbgs_num_out[i] = dbgs_num_aid[i]-dbgs_num_bid[i];
     end

    always_comb
    begin
      debug = '0;
      
      debug[0][ 4: 0]  = top_state;        
      debug[0][ 7: 5]  = bstate;           
      debug[0][11: 8]  = din_state;        
      debug[0][15:12]  = cb_state;         
      debug[0][19:16]  = xstate;           
      debug[0][22:20]  = hit_cbuf;         
      debug[0][23]     = dump_bresp;       
      debug[0][31:24]  = {|bresp_lvl[31:7],bresp_lvl[6:0]};        
      
      debug[1][15: 0]  = pp_lines_wrote;   
      debug[1][31:16]  = cb_rd_pic_line;   
      
      debug[2][15: 0]  = cb_pace_count;    
      debug[2][31:16]  = pp_upd_count;     
      
      debug[3][11: 0]  = pp_ptch_wrds;     
      debug[3][25:16]  = cb_rd_xloc;       
      debug[3][31]     = pp_cb_size_ovf;   
      
      debug[4][ 4: 0]  = req_d1.awid;      
      debug[4][ 6: 5]  = req_d1.awburst;   
      debug[4][ 9: 7]  = req_d1.awsize;    
      debug[4][17:10]  = req_d1.awlen;     
      debug[4][31:18]  = req_d1.awaddr;    
      
      debug[5][ 4: 0]  = req_cbuf.awid;    
      debug[5][ 6: 5]  = req_cbuf.awburst; 
      debug[5][ 9: 7]  = req_cbuf.awsize;  
      debug[5][17:10]  = req_cbuf.awlen;   
      debug[5][31:18]  = req_cbuf.awaddr;  
      
      debug[6][0]      = s_awready;        
      debug[6][1]      = s_awvalid;        
      debug[6][6:2]    = s_awid;           
      debug[6][7]      = s_wready;         
      debug[6][8]      = s_wvalid;         
      debug[6][9]      = s_bready;         
      debug[6][10]     = s_bvalid;         
      debug[6][15:11]  = s_bid;            
      
      debug[6][16]     = m_awready;        
      debug[6][17]     = m_awvalid;        
      debug[6][22:18]  = m_awid;           
      debug[6][23]     = m_wready;         
      debug[6][24]     = m_wvalid;         
      debug[6][25]     = m_bready;         
      debug[6][26]     = m_bvalid;         
      debug[6][31:27]  = m_bid;            
      
      debug[7]         = pp_pln_wrds;      
      debug[8]         = pp_pic_wrds;      
      
      debug[9]         = din_pln_wrds[0];  
      debug[10]        = din_pln_wrds[1];  
      debug[11]        = din_pln_wrds[2];  
      
      debug[12]        = cb_cfg[0];        
      debug[13]        = cb_cfg[1];        
      debug[14]        = cb_cfg[2];        
      debug[15]        = cb_cfg[3];        
      
      debug[16][31: 0] = {dbgm_num_out[ 3],dbgm_num_out[ 2],dbgm_num_out[ 1],dbgm_num_out[ 0]};
      debug[17][31: 0] = {dbgm_num_out[ 7],dbgm_num_out[ 6],dbgm_num_out[ 5],dbgm_num_out[ 4]};
      debug[18][31: 0] = {dbgm_num_out[11],dbgm_num_out[10],dbgm_num_out[ 9],dbgm_num_out[ 8]};
      debug[19][31: 0] = {dbgm_num_out[15],dbgm_num_out[14],dbgm_num_out[13],dbgm_num_out[12]};
      debug[20][31: 0] = {dbgm_num_out[19],dbgm_num_out[18],dbgm_num_out[17],dbgm_num_out[16]};
      debug[21][31: 0] = {dbgm_num_out[23],dbgm_num_out[22],dbgm_num_out[21],dbgm_num_out[20]};
      debug[22][31: 0] = {dbgm_num_out[27],dbgm_num_out[26],dbgm_num_out[25],dbgm_num_out[24]};
      debug[23][31: 0] = {dbgm_num_out[31],dbgm_num_out[30],dbgm_num_out[29],dbgm_num_out[28]};
      
      debug[24][31: 0] = {dbgs_num_out[ 3],dbgs_num_out[ 2],dbgs_num_out[ 1],dbgs_num_out[ 0]};
      debug[25][31: 0] = {dbgs_num_out[ 7],dbgs_num_out[ 6],dbgs_num_out[ 5],dbgs_num_out[ 4]};
      debug[26][31: 0] = {dbgs_num_out[11],dbgs_num_out[10],dbgs_num_out[ 9],dbgs_num_out[ 8]};
      debug[27][31: 0] = {dbgs_num_out[15],dbgs_num_out[14],dbgs_num_out[13],dbgs_num_out[12]};
      debug[28][31: 0] = {dbgs_num_out[19],dbgs_num_out[18],dbgs_num_out[17],dbgs_num_out[16]};
      debug[29][31: 0] = {dbgs_num_out[23],dbgs_num_out[22],dbgs_num_out[21],dbgs_num_out[20]};
      debug[30][31: 0] = {dbgs_num_out[27],dbgs_num_out[26],dbgs_num_out[25],dbgs_num_out[24]};
      debug[31][31: 0] = {dbgs_num_out[31],dbgs_num_out[30],dbgs_num_out[29],dbgs_num_out[28]};
    end

endmodule
