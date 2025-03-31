// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L2 crossbar module.
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_XBAR_SV
`define L2_XBAR_SV

module l2_xbar
  import l2_pkg::*;
  import l2_cfg_pkg::*;
  (
  // Clock and reset signals
  input  wire                             i_clk,
  input  wire                             i_rst_n,

  // Memory interface
  input  l2_mem_req_t                     i_mem_req,      // ASO-UNUSED_INPUT: LSB part of the address not used
  output logic                            o_mem_rd_ready,
  output logic                            o_mem_wr_ready,
  output l2_mem_rsp_t                     o_mem_rsp,

  // Bank interface
  output l2_bank_req_t [L2_NUM_BANKS-1:0] o_bank_req,
  input  l2_ram_rsp_t  [L2_NUM_BANKS-1:0] i_bank_rsp

);
  // =====================================================
  // Local parameters
  // =====================================================

  // =====================================================
  // Type definition
  // =====================================================
  typedef struct packed {
    logic          we;
    l2_bank_addr_t addr;
  } l2_xbar_rr_hdr_t;

  typedef struct packed {
    l2_sram_strb_t [L2_NUM_SRAMS-1:0] wbe;
    l2_sram_data_t [L2_NUM_SRAMS-1:0] data;
  } l2_xbar_req_data_t;

  typedef struct packed {
    l2_xbar_rr_hdr_t  [L2_NUM_BANKS-1:0] hdr;
    logic             [L2_NUM_BANKS-1:0] req;
    l2_xbar_req_data_t                   data;
  } l2_req_wire_pipeline_t;

  // =====================================================
  // Derivated Local parameters
  // =====================================================
  localparam int unsigned XbarDataWd = L2_NUM_BANKS*($bits(l2_xbar_rr_hdr_t)+1)+$bits(l2_xbar_req_data_t);

  // =====================================================
  // Signal declarations
  // =====================================================
  l2_xbar_rr_hdr_t                                                   rd_xbar_hdr;
  logic                                           [L2_NUM_BANKS-1:0] rd_req_valid;
  logic                                           [L2_NUM_BANKS-1:0] rd_ready;
  l2_xbar_rr_hdr_t                                                   wr_xbar_hdr;
  logic                                           [L2_NUM_BANKS-1:0] wr_req_valid;
  logic                                           [L2_NUM_BANKS-1:0] wr_ready;
  l2_xbar_rr_hdr_t   [L2_MAX_WIRE_REQ_LATENCY-1:0][L2_NUM_BANKS-1:0] bank_hdr_d;
  l2_xbar_rr_hdr_t   [L2_MAX_WIRE_REQ_LATENCY-1:0][L2_NUM_BANKS-1:0] bank_hdr_q;
  logic              [L2_MAX_WIRE_REQ_LATENCY-1:0][L2_NUM_BANKS-1:0] bank_req_d;
  logic              [L2_MAX_WIRE_REQ_LATENCY-1:0][L2_NUM_BANKS-1:0] bank_req_q;
  logic              [L2_MAX_WIRE_REQ_LATENCY-1:0]                   bank_req_vld_d;
  logic              [L2_MAX_WIRE_REQ_LATENCY-1:0]                   bank_req_vld_q;
  l2_xbar_req_data_t [L2_MAX_WIRE_REQ_LATENCY-1:0]                   xbar_data_d;
  l2_xbar_req_data_t [L2_MAX_WIRE_REQ_LATENCY-1:0]                   xbar_data_q;
  l2_bank_req_t                                   [L2_NUM_BANKS-1:0] bank_req_lat_d;
  l2_sram_data_t              [L2_RSP_GROUPS-1:0] [L2_NUM_SRAMS-1:0] mem_group_rsp_d;
  l2_sram_data_t              [L2_RSP_GROUPS-1:0] [L2_NUM_SRAMS-1:0] mem_group_rsp_q;
  logic                       [L2_RSP_GROUPS-1:0]                    mem_group_rsp_vld_d;
  logic                       [L2_RSP_GROUPS-1:0]                    mem_group_rsp_vld_q;
  l2_sram_data_t   [L2_MAX_STAGE_RSP_LATENCY-1:0] [L2_NUM_SRAMS-1:0] mem_stage_rsp_d;
  l2_sram_data_t   [L2_MAX_STAGE_RSP_LATENCY-1:0] [L2_NUM_SRAMS-1:0] mem_stage_rsp_init;
  l2_sram_data_t   [L2_MAX_STAGE_RSP_LATENCY-1:0] [L2_NUM_SRAMS-1:0] mem_stage_rsp_q;
  logic            [L2_MAX_STAGE_RSP_LATENCY-1:0]                    mem_stage_rsp_vld_d;
  logic            [L2_MAX_STAGE_RSP_LATENCY-1:0]                    mem_stage_rsp_vld_init;
  logic            [L2_MAX_STAGE_RSP_LATENCY-1:0]                    mem_stage_rsp_vld_q;
  // =====================================================
  // RTL
  // =====================================================

  /// @u_shift_valid_resp
  /// Shift register used to generate a valid to the response
  cc_cnt_shift_reg #(
    .data_t(logic),
    .Stages(L2_MEMORY_RESP_LATENCY)
  ) u_shift_valid_resp (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_clear  (1'b0),
    .i_stall  (1'b0),
    .i_data   (1'b1),
    .i_data_en((i_mem_req.wr.en && o_mem_wr_ready)),
    .o_data   (/* NC */), // ASO-UNUSED_OUTPUT: Only data_en and out updated are used
    .o_updated(o_mem_rsp.wr_rsp)
  );

  /// @
  /// Merge all read ready signals from the RR arb into one
  always_comb o_mem_rd_ready = rd_ready[i_mem_req.rd.addr.bank];

  /// @
  /// Merge all write eady signals from the RR arb into one
  always_comb o_mem_wr_ready = wr_ready[i_mem_req.wr.addr.bank];

  /// @rd_hdr_unroll_comb_proc
  /// Unroll the read header between the bank rr arb
  always_comb begin : rd_hdr_unroll_comb_proc
      rd_xbar_hdr = '{
        we: 1'b0,
        addr: '{
          ram: i_mem_req.rd.addr.ram,
          sram: i_mem_req.rd.addr.sram
        }
      };
  end

  /// @wr_hdr_unroll_comb_proc
  /// Unroll the write header between the bank rr arb
  always_comb begin : wr_hdr_unroll_comb_proc
    wr_xbar_hdr = '{
      we: 1'b1,
      addr: '{
        ram: i_mem_req.wr.addr.ram,
        sram: i_mem_req.wr.addr.sram
      }
    };
  end

  /// @rd_req_valid_unroll_comb_proc
  /// Unroll the read req between the bank rr arb
  always_comb begin : rd_req_valid_unroll_comb_proc
    foreach (rd_req_valid[i]) begin
      rd_req_valid[i] = i_mem_req.rd.en && (i_mem_req.rd.addr.bank == i);
    end
  end

  /// @wr_req_valid_unroll_comb_proc
  /// Unroll the write req between the bank rr arb
  always_comb begin : wr_req_valid_unroll_comb_proc
    foreach (wr_req_valid[i]) begin
      wr_req_valid[i] = i_mem_req.wr.en && (i_mem_req.wr.addr.bank == i);
    end
  end

  /// @u_rr_arb[L2_NUM_BANKS-1:0]
  /// Unroll the bank rr arb
  for (genvar bank = 0; bank < L2_NUM_BANKS; bank++) begin : g_rr_arb
  cc_stream_round_robin_arbiter #(
    .data_t(l2_xbar_rr_hdr_t),
    .N_INP(2),
    .ARBITER("rr")
  ) u_rr_arb (
    .i_clk       (i_clk),
    .i_rst_n     (i_rst_n),

    .inp_data_i  ({rd_xbar_hdr, wr_xbar_hdr}),
    .inp_valid_i ({rd_req_valid[bank], wr_req_valid[bank]}),
    .inp_ready_o ({rd_ready[bank], wr_ready[bank]}),

    .oup_data_o  (bank_hdr_d[0][bank]),
    .oup_valid_o (bank_req_d[0][bank]),
    .oup_ready_i ('1)
  );
  end

  /// @xbar_data_comb_proc
  /// Preparing data and wbe to be stored
  always_comb begin : xbar_data_comb_proc
    xbar_data_d[0] = '{
      wbe: i_mem_req.wr.wbe,
      data: i_mem_req.wr.data
    };
  end

  for(genvar stage=0; stage<L2_MAX_WIRE_REQ_LATENCY; stage++) begin : g_wire_req_pipelane
  l2_req_wire_pipeline_t req_pipe_q;
  /// @u_shift_wire_pipeline
  /// Shift register used to destribute the request
  cc_cnt_shift_reg #(
    .data_t(l2_req_wire_pipeline_t),
    .Stages(1)
  ) u_shift_wire_pipeline (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_clear  (1'b0),
    .i_stall  (1'b0),
    .i_data   (l2_req_wire_pipeline_t'{
                 hdr: bank_hdr_d[stage]
                ,req: bank_req_d[stage]
                ,data: xbar_data_d[stage]
              }),
    .i_data_en(bank_req_vld_d[stage]),
    .o_data   (req_pipe_q),
    .o_updated(bank_req_vld_q[stage])
  );
  always_comb begin : unroll_req_pipe_seq_proc
    bank_hdr_q[stage]  = req_pipe_q.hdr;
    bank_req_q[stage]  = req_pipe_q.req;
    xbar_data_q[stage] = req_pipe_q.data;
  end
  end

  always_comb begin : shift_data_req_comb_proc
    bank_req_vld_d = {bank_req_vld_q[L2_MAX_WIRE_REQ_LATENCY-2:0], |bank_req_d[0]};
    bank_hdr_d[L2_MAX_WIRE_REQ_LATENCY-1:1] = bank_hdr_q[L2_MAX_WIRE_REQ_LATENCY-2:0];
    bank_req_d[L2_MAX_WIRE_REQ_LATENCY-1:1] = bank_req_q[L2_MAX_WIRE_REQ_LATENCY-2:0];
    xbar_data_d[L2_MAX_WIRE_REQ_LATENCY-1:1] = xbar_data_q[L2_MAX_WIRE_REQ_LATENCY-2:0];
  end

  /// @bank_req_comb_proc
  /// Unroll bank request
  always_comb begin : bank_req_comb_proc
    foreach (bank_req_lat_d[i]) begin
      bank_req_lat_d[i] = '{
        ce: bank_req_q[L2_REQ_WIRE_LATENCY[i]-1][i] & bank_req_vld_q[L2_REQ_WIRE_LATENCY[i]-1],
        bank: '{
          addr: '{
            ram: bank_hdr_q[L2_REQ_WIRE_LATENCY[i]-1][i].addr.ram,
            sram: bank_hdr_q[L2_REQ_WIRE_LATENCY[i]-1][i].addr.sram
          },
          we: bank_hdr_q[L2_REQ_WIRE_LATENCY[i]-1][i].we,
          wbe: xbar_data_q[L2_REQ_WIRE_LATENCY[i]-1].wbe,
          data: xbar_data_q[L2_REQ_WIRE_LATENCY[i]-1].data
        }
      };
    end
  end

  for(genvar bank=0; bank<L2_NUM_BANKS; bank++) begin : g_bank_req_pipelane
  /// @u_shift_bank_pipeline
  /// Shift register used to pipeline the bank request
  cc_cnt_shift_reg #(
    .data_t(l2_bank_t),
    .Stages(L2_REQ_BANK_LATENCY[bank])
  ) u_shift_bank_pipeline (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .i_clear  (1'b0),
    .i_stall  (1'b0),
    .i_data   (bank_req_lat_d[bank].bank),
    .i_data_en(bank_req_lat_d[bank].ce),
    .o_data   (o_bank_req[bank].bank),
    .o_updated(o_bank_req[bank].ce)
  );
  end

  /// @combine_bank_rsp_comb_proc
  /// Combining bank responses with an OR gate
  always_comb begin : combine_bank_rsp_comb_proc
    mem_group_rsp_d = '0;
    mem_group_rsp_vld_d = '0;
    foreach (i_bank_rsp[bank]) begin
      mem_group_rsp_vld_d[L2_RSP_GROUP[bank]] |= i_bank_rsp[bank].valid;
      mem_group_rsp_d[L2_RSP_GROUP[bank]] |= i_bank_rsp[bank].data;
    end
  end

  for(genvar group=0; group<L2_RSP_GROUPS; group++) begin : g_group_rsp_pipelane
    l2_ram_rsp_t int_mem_group_rsp;
    logic        shift_en;
    /// @shift_enable_seq_proc
    /// Keep shift enable to send data and clean it
    always_ff @( posedge i_clk, negedge i_rst_n ) begin : shift_enable_seq_proc
      if      (~i_rst_n)                              shift_en <= 1'b0;
      else if (mem_group_rsp_vld_d[group] ^ shift_en) shift_en <= mem_group_rsp_vld_d[group];
    end
    /// @u_shift_group_rsp_data
    /// Shift register used to register data response per group
    cc_cnt_shift_reg #(
      .data_t(l2_ram_rsp_t),
      .Stages(L2_RSP_GROUP_LATENCY[group])
    ) u_shift_group_rsp_data (
      .i_clk    (i_clk),
      .i_rst_n  (i_rst_n),
      .i_clear  (1'b0),
      .i_stall  (1'b0),
      .i_data   (l2_ram_rsp_t'{
                               data: mem_group_rsp_d[group]
                              ,valid: mem_group_rsp_vld_d[group]
                              }),
      .i_data_en(mem_group_rsp_vld_d[group] | shift_en),
      .o_data   (int_mem_group_rsp),
      .o_updated()
    );
    always_comb mem_group_rsp_vld_q[group] = int_mem_group_rsp.valid;
    always_comb mem_group_rsp_q[group] = int_mem_group_rsp.data;
  end

  /// @
  /// Get the initial value used in the OR Gate per stage
  always_comb mem_stage_rsp_init = {{$bits(l2_sram_data_t)*L2_NUM_SRAMS{1'b0}}
                                      ,mem_stage_rsp_q[L2_MAX_STAGE_RSP_LATENCY-1:1]};

  /// @mem_stage_rsp_comb_proc
  /// Combine the answers per group and combine them into the right pipeline stage
  always_comb begin : mem_stage_rsp_comb_proc
    foreach (mem_stage_rsp_d[stage]) begin
      mem_stage_rsp_d[stage] = mem_stage_rsp_init[stage];
      foreach (mem_group_rsp_q[group]) begin
        if ((stage+1) == L2_RSP_STAGE_LATENCY[group]) begin
          mem_stage_rsp_d[stage] |= mem_group_rsp_q[group];
        end
      end
    end
  end

  /// @
  /// Get the initial value used in the OR Gate per stage
  always_comb mem_stage_rsp_vld_init = {{$bits(l2_sram_data_t)*L2_NUM_SRAMS{1'b0}}
                                      ,mem_stage_rsp_vld_q[L2_MAX_STAGE_RSP_LATENCY-1:1]};

  /// @mem_stage_rsp_vld_comb_proc
  /// Combine the valid answers per group and combine them into the right pipeline stage
  always_comb begin : mem_stage_rsp_vld_comb_proc
    foreach (mem_stage_rsp_vld_d[stage]) begin
      mem_stage_rsp_vld_d[stage] = mem_stage_rsp_vld_init[stage];
      foreach (mem_group_rsp_vld_q[group]) begin
        if ((stage+1) == L2_RSP_STAGE_LATENCY[group]) begin
          mem_stage_rsp_vld_d[stage] |= mem_group_rsp_vld_q[group];
        end
      end
    end
  end

  for(genvar stage=0; stage<L2_MAX_STAGE_RSP_LATENCY; stage++) begin : g_stage_rsp_pipelane
    l2_ram_rsp_t int_mem_stage_rsp;
    logic        shift_en;
    /// @shift_enable_seq_proc
    /// Keep shift enable to send data and clean it
    always_ff @( posedge i_clk, negedge i_rst_n ) begin : shift_enable_seq_proc
      if      (~i_rst_n)                              shift_en <= 1'b0;
      else if (mem_stage_rsp_vld_d[stage] ^ shift_en) shift_en <= mem_stage_rsp_vld_d[stage];
    end
    /// @u_shift_stage_rsp_data
    /// Shift register used to register data response per stage
    cc_cnt_shift_reg #(
      .data_t(l2_ram_rsp_t),
      .Stages(1)
    ) u_shift_stage_rsp_data (
      .i_clk    (i_clk),
      .i_rst_n  (i_rst_n),
      .i_clear  (1'b0),
      .i_stall  (1'b0),
      .i_data   (l2_ram_rsp_t'{
                               data: mem_stage_rsp_d[stage]
                              ,valid: mem_stage_rsp_vld_d[stage]
                              }),
      .i_data_en(mem_stage_rsp_vld_d[stage] | shift_en),
      .o_data   (int_mem_stage_rsp),
      .o_updated()
    );
    always_comb mem_stage_rsp_vld_q[stage] = int_mem_stage_rsp.valid;
    always_comb mem_stage_rsp_q[stage] = int_mem_stage_rsp.data;
  end

  /// @
  /// Drive the output response
  always_comb o_mem_rsp.data = mem_stage_rsp_q[0];

  /// @
  /// Drive the output response valid
  always_comb o_mem_rsp.rd_rsp = mem_stage_rsp_vld_q[0];

endmodule

`endif  // L2_XBAR_SV
