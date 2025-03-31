
module dma_channel_ctrl
    import dma_pkg::*;
(
    input  wire             i_clk,
    input  wire             i_rst_n,

    input  wire             i_en,
    input  dma_desc_t       i_desc,

    input  logic            i_int_en,
    input  logic            i_int_clr,
    output logic            o_int,

    output logic            o_en_val,
    output logic            o_en_hus,
    output logic            o_clr_val,
    output logic            o_clr_hus,

    input  dma_global_cfg_t i_global_cfg,
    output dma_global_sts_t o_global_sts,

    input  logic            i_cmd_vld,
    output logic            o_cmd_rdy,
    output logic            o_cmd_done,
    input  logic [DMA_CMD_SIZE-1:0] i_cmd_data,
    input  logic [$clog2(DMA_CMD_N_FORMATS)-1:0] i_cmd_format,

    output dma_ll_t         o_ll,
    output logic            o_ll_req,
    input  logic            i_ll_data_req,
    output logic            o_ll_data_gnt,
    input  dma_bufdata_t    i_ll_data,

    output dma_desc_t       o_desc,
    output logic            o_en,
    input  logic [2:0]      i_busy
);

    localparam int unsigned EVENT_W = 1;

    logic busy_q;
    logic busy_dly_q;
    dma_desc_t desc_d;
    dma_desc_t desc_q;
    logic en_d;
    logic [2:0] en_q;
    logic completion;
    logic      cmd_accept;
    logic      ll_desc_req, ll_desc_gnt;
    dma_desc_t ll_desc;

    //always_comb completion = |en_q[1:0] ? 1'b0 : !busy_q && (en_q[2] || busy_dly_q);
    always_comb completion = !busy_q && busy_dly_q;

    always_comb o_en_val  = 1'b0;
    always_comb o_en_hus  = completion;
    always_comb o_clr_val = 1'b0;
    always_comb o_clr_hus = 1'b0;

    always_comb o_cmd_done = completion && i_global_cfg.mode;
    always_comb o_cmd_rdy  = !busy_q && i_global_cfg.mode;
    always_comb cmd_accept = o_cmd_rdy && i_cmd_vld;

    dma_channel_ll s_ll (
    .i_clk,
    .i_rst_n,

    .i_ll_addr     ( desc_q.ll.ll_addr ),
    .i_ll_mode     ( desc_q.ll.ll_mode ),
    .i_ll_en       ( (i_global_cfg.mode ? i_cmd_format == 'd4 && cmd_accept : i_desc.ll.ll_en) && !i_busy[0]),

    .o_ll_req,
    .i_ll_gnt      (1'b1),
    .o_ll,

    .i_ll_data_req,
    .o_ll_data_gnt,
    .i_ll_data,

    .o_desc       (ll_desc),
    .o_desc_req   (ll_desc_req),
    .i_desc_gnt   (ll_desc_gnt),

    .i_default_desc  (desc_q)
);

    always_ff @ (posedge i_clk or negedge i_rst_n)
        if (!i_rst_n) begin
            desc_q <= '0;
            en_q   <= 3'b0;
            busy_q <= 1'b0;
            busy_dly_q <= 1'b0;
        end
        else begin
            if (en_d) begin
              desc_q <= desc_d;
            end
            if (|{en_d, en_q})
              busy_q <= 1'b1;
            else if (!i_busy)
              busy_q <= 1'b0;
            en_q <= {en_q[1:0], en_d};
            busy_dly_q <= busy_q;
        end

    always_comb en_d = ( i_global_cfg.mode ? cmd_accept : i_en ) && !busy_q && !busy_dly_q;


    always_comb begin
      ll_desc_gnt = 1'b0;
      if (ll_desc_req) begin
        desc_d = ll_desc;
        ll_desc_gnt = 1'b1;
      end
      else if (i_global_cfg.mode) begin
        desc_d = decode_cmd_f(i_cmd_data, i_cmd_format, desc_q);
      end
      else begin
        desc_d = i_desc;
      end
      if (desc_d.glb.ytype == DSBL) begin
        desc_d.src.yrowsize = 'd1;
        desc_d.dst.yrowsize = 'd1;
        if(desc_d.glb.xtype == DSBL || !(|desc_d.dst.xbytesize)) begin
          desc_d.src.xbytesize = '0;
        end
        else if (desc_d.dst.xbytesize < desc_d.src.xbytesize) begin
          desc_d.src.xbytesize = desc_d.dst.xbytesize;
        end
        if(desc_d.glb.xtype == DSBL || (!(|desc_d.src.xbytesize) && desc_d.glb.xtype != FILL)) begin
          desc_d.dst.xbytesize = '0;
        end
        else if (desc_d.glb.xtype == CONT && desc_d.src.xbytesize < desc_d.dst.xbytesize) begin
          desc_d.dst.xbytesize = desc_d.src.xbytesize;
        end
      end
    end

    always_comb o_en = en_q[0];
    always_comb o_desc = desc_q;
    always_comb o_global_sts = '{ busy : busy_q };

    logic event_pulse;   // TODO : finalise interrupt behaviour

    always_comb event_pulse = completion;

    dma_events #( .N_EVENTS(1))
    s_event
    (
      .i_clk,
      .i_rst_n,
      .i_event_set(event_pulse),
      .i_int_clr  (i_int_clr),
      .i_int_mask (desc_q.glb.int_en),
      .i_event_mask ('1), // TODO
      .o_int,
      .o_event()
    );



endmodule
