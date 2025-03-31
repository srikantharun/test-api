// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Scratchpad control module
// Owner: Joao Martins <joao.martins@axelera.ai>

`ifndef SPM_CONTROL_SV
  `define SPM_CONTROL_SV

module spm_control
  import spm_pkg::*;
#(
  parameter int unsigned SPM_MEM_SIZE_KB    = 128,
  parameter int unsigned SPM_MEM_WBE_WIDTH  = 8,
  parameter int unsigned SPM_MEM_ADDR_WIDTH = 17,
  parameter int unsigned SPM_MEM_DATA_WIDTH = 64,
  parameter int unsigned ECC_PROTECTION_EN  = 0,
  parameter int unsigned OOR_ERR_EN         = 1,
  parameter int unsigned SPM_NB_REQ_PIPELINE = 0,
  parameter int unsigned SPM_NB_RSP_PIPELINE = 0,
  parameter int unsigned SPM_MAX_NUM_WR_OSR = 8,
  parameter int unsigned SPM_MAX_NUM_RD_OSR = 8,
  // AXI types
  parameter type spm_axi_data_t   = logic [64-1:0],
  parameter type spm_axi_addr_t   = logic [32-1:0],
  parameter type spm_axi_strb_t   = logic [8-1:0],
  parameter type spm_axi_len_t    = axi_pkg::axi_len_t,
  parameter type spm_axi_id_t     = logic [4-1:0], // Taken from top sys_spm.pkg
  parameter type spm_axi_size_t   = axi_pkg::axi_size_t,
  parameter type spm_axi_burst_t  = axi_pkg::axi_burst_t,
  parameter type spm_axi_resp_t   = axi_pkg::axi_resp_e,
  parameter type spm_axi_cache_t  = axi_pkg::axi_cache_t,
  parameter type spm_axi_prot_t   = axi_pkg::axi_prot_t
) (
  // Clock, positive edge triggered
  input  wire i_clk,
  // Asynchronous reset, active low
  input  wire i_rst_n,
  // AXI write address channel
  input  logic            i_axi_s_awvalid,
  input  spm_axi_addr_t   i_axi_s_awaddr,
  input  spm_axi_id_t     i_axi_s_awid,
  input  spm_axi_len_t    i_axi_s_awlen,
  input  spm_axi_size_t   i_axi_s_awsize,
  input  spm_axi_burst_t  i_axi_s_awburst,
  input  logic            i_axi_s_awlock,
  input  spm_axi_cache_t  i_axi_s_awcache,
  input  spm_axi_prot_t   i_axi_s_awprot,
  output logic            o_axi_s_awready,
  // AXI write data channel
  input  logic           i_axi_s_wvalid,
  input  logic           i_axi_s_wlast,
  input  spm_axi_data_t  i_axi_s_wdata,
  input  spm_axi_strb_t  i_axi_s_wstrb,
  output logic           o_axi_s_wready,
  // AXI write response channel
  output logic           o_axi_s_bvalid,
  output spm_axi_id_t    o_axi_s_bid,
  output spm_axi_resp_t  o_axi_s_bresp,
  input  logic           i_axi_s_bready,
  // AXI read address channel
  input  logic            i_axi_s_arvalid,
  input  spm_axi_addr_t   i_axi_s_araddr,
  input  spm_axi_id_t     i_axi_s_arid,
  input  spm_axi_len_t    i_axi_s_arlen,
  input  spm_axi_size_t   i_axi_s_arsize,
  input  spm_axi_burst_t  i_axi_s_arburst,
  input  logic            i_axi_s_arlock,
  input  spm_axi_cache_t  i_axi_s_arcache,
  input  spm_axi_prot_t   i_axi_s_arprot,
  output logic            o_axi_s_arready,
  // AXI read data/response channel
  output logic           o_axi_s_rvalid,
  output logic           o_axi_s_rlast,
  output spm_axi_id_t    o_axi_s_rid,
  output spm_axi_data_t  o_axi_s_rdata,
  output spm_axi_resp_t  o_axi_s_rresp,
  input  logic           i_axi_s_rready,
  // Memory interface
  output logic                           o_mem_req,
  output logic                           o_mem_we,
  output logic  [SPM_MEM_WBE_WIDTH-1:0]  o_mem_be,
  output logic [SPM_MEM_ADDR_WIDTH-1:0]  o_mem_addr,
  output logic [SPM_MEM_DATA_WIDTH-1:0]  o_mem_wdata,
  input  logic [SPM_MEM_DATA_WIDTH-1:0]  i_mem_rdata,
  input  logic                           i_mem_rvalid,
  // Interface to Error status CSR register
  output logic              o_irq,
  input  logic              i_scp_ecc_disable,
  output spm_error_status_t o_scp_error_status,
  // Internal observation signals
  output spm_obs_t          o_spm_obs
);

    // =====================================================
    // Localparam declarations
    localparam int unsigned SPM_AXI_DATA_WIDTH = $bits(spm_axi_data_t);
    localparam int unsigned SPM_AXI_ADDR_WIDTH = $bits(spm_axi_addr_t);

    localparam int unsigned DATA_WIDTH  = SPM_AXI_DATA_WIDTH;
    localparam int unsigned ADDR_WIDTH  = SPM_AXI_ADDR_WIDTH;
    localparam int unsigned WBE_WIDTH   = DATA_WIDTH/8;
    localparam int unsigned AXI_SIZE_WIDTH = $bits(spm_axi_size_t);

    localparam int unsigned MEM_ADDR_LSB   = $clog2({32'b0, DATA_WIDTH/8});
    localparam int unsigned MEM_ADDR_MSB   = $clog2(SPM_MEM_SIZE_KB) - 1 + 10;
    localparam int unsigned MEM_ADDR_WIDTH = MEM_ADDR_MSB-MEM_ADDR_LSB+1;
    localparam int unsigned MEM_SPACE_KB   = SPM_MEM_SIZE_KB - 1;

    // 3 is the minimum fixed latency for the read data from the memory macros (except SPM_NB_REQ_PIPELINE and SPM_NB_RSP_PIPELINE)
    // there is also have one flop stage before the FIFO that can not be stalled and 1 additional cycle to be on the safe side
    localparam int unsigned MEM_PATH_STATIC_DELAY   = 5;
    localparam int unsigned SPM_CTRL_RSP_FIFO_DEPTH = (SPM_NB_REQ_PIPELINE + SPM_NB_RSP_PIPELINE + MEM_PATH_STATIC_DELAY);

    localparam logic [SPM_MEM_WBE_WIDTH-1:0] WBE_ALL_ONES = {SPM_MEM_WBE_WIDTH{1'b1}};
    localparam logic [SPM_MEM_WBE_WIDTH-1:0] WBE_ALL_ZERO = {SPM_MEM_WBE_WIDTH{1'b0}};

    localparam int unsigned OSR_SIZE = 8 + SPM_NB_REQ_PIPELINE + SPM_NB_RSP_PIPELINE; // Overprovision should be fine with 8
    // Types
    typedef logic [MEM_ADDR_MSB:0]         spm_mem_addr_t;
    typedef logic [SPM_MEM_DATA_WIDTH-1:0] spm_mem_data_t;
    typedef logic [SPM_MEM_WBE_WIDTH-1:0]  spm_mem_wbe_t;

    // ----- Memory access types
    // - Note: I considered adding these structs in spm_pkg but then I wouldn't
    // have the  spm_axi_* types.
    typedef struct packed {
        logic          en;
        spm_axi_addr_t addr;
        spm_axi_strb_t wbe;
        spm_axi_data_t data;
    } spm_axi2reg_wr_t;

    typedef struct packed {
        logic          en;
        spm_axi_addr_t addr;
    } spm_axi2reg_rd_t;

    typedef struct packed {
        spm_axi2reg_wr_t wr;
        spm_axi2reg_rd_t rd;
    } spm_axi2reg_req_t;

    typedef struct packed {
        spm_axi_data_t data;
        logic          wr_rsp;
        logic          wr_err;
        logic          rd_rsp;
        logic          rd_err;
    } spm_axi2reg_rsp_t;

    typedef struct packed {
      logic is_rmw;
      logic is_error;
    } fsm_rsp_t;

    // =====================================================
    // Support functions
    function automatic spm_ecc_err_index_t get_err_index (spm_mem_addr_t addr);
        get_err_index = {{($bits(spm_ecc_err_index_t)-($bits(spm_mem_addr_t)-3)){1'b0}},
                          addr[$bits(spm_mem_addr_t)-1:3]};
    endfunction

    // =====================================================
    // Signal declaration
    spm_error_status_t  err_status;
    spm_ecc_err_type_t  highest_sever_err_seen_q;
    logic disable_csr_err_status_update;
    logic write_req;

    // Bridge signals
    axi_pkg::axi_resp_t axi_s_rresp;
    axi_pkg::axi_resp_t axi_s_bresp;
    spm_axi2reg_req_t  axi2reg_req;
    spm_axi2reg_rsp_t  axi2reg_rsp;

    spm_mem_data_t mem_wdata;
    spm_mem_wbe_t  mem_wbe;
    spm_mem_data_t mem_rdata_q;
    logic mem_rvalid_q;

    // FSM Response Fifo
    fsm_rsp_t rsp_fifo_i_data;
    logic     rsp_fifo_i_valid;
    logic     rsp_fifo_o_ready;
    fsm_rsp_t rsp_fifo_o_data;
    fsm_rsp_t rsp_fifo_o_data_q;
    logic     rsp_fifo_o_valid;
    logic     rsp_fifo_i_ready;

    spm_access_t axi2reg_ready;
    spm_access_t new_req;
    spm_access_t addr_hit_mem;
    spm_access_t addr_invalid;

    spm_mem_addr_t addr_d;
    spm_mem_addr_t addr_q;
    spm_mem_addr_t mem_addr_all_bit;
    spm_mem_addr_t in_flight_rmw_addr_all_bit;

    spm_axi_data_t wdata_masked;
    spm_axi_data_t wdata_masked_q;
    spm_axi_data_t rdata_masked;
    spm_axi_data_t rmw_data;
    spm_axi_data_t wdata;
    spm_axi_data_t data_req_q;
    spm_axi_strb_t wbe_q;

    // FSMs
    logic state_en;
    state_t state, next_state;

    // ---- to organise
    logic rmw_needed;
    logic rmw_needed_q;
    logic waiting_for_rmw;
    logic waiting_for_rmw_q;
    logic mem_req;
    logic mem_we;

    spm_access_t new_valid_req;
    spm_access_t new_valid_req_q;
    spm_access_t new_req_error;
    spm_access_t new_req_error_q;

    // =====================================================
    // RTL

    // --------------------
    // AXI Bridge
    always_comb begin : adjust_type_comb
      o_axi_s_rresp = spm_axi_resp_t'(axi_s_rresp);
      o_axi_s_bresp = spm_axi_resp_t'(axi_s_bresp);
    end

  axi2reg #(
    .IDW          ($bits(spm_axi_id_t)),
    .AW           ($bits(spm_axi_addr_t)),
    .DW           ($bits(spm_axi_data_t)),
    .BW           ($bits(spm_axi_len_t)),
    .NR_WR_REQS   (SPM_MAX_NUM_WR_OSR),
    .NR_RD_REQS   (SPM_MAX_NUM_RD_OSR),
    .RD_RESP_DEPTH(OSR_SIZE),
    .WR_RESP_DEPTH(OSR_SIZE),
    .OSR          (OSR_SIZE)
  ) u_axi2mem (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    // - AXI-S
    // Write Address Channel
    .awid            (i_axi_s_awid),
    .awaddr          (i_axi_s_awaddr),
    .awlen           (i_axi_s_awlen),
    .awsize          (i_axi_s_awsize),
    .awburst         (i_axi_s_awburst),
    .awvalid         (i_axi_s_awvalid),
    .awready         (o_axi_s_awready),
    // Read Address Channel
    .arid            (i_axi_s_arid),
    .araddr          (i_axi_s_araddr),
    .arlen           (i_axi_s_arlen),
    .arsize          (i_axi_s_arsize),
    .arburst         (i_axi_s_arburst),
    .arvalid         (i_axi_s_arvalid),
    .arready         (o_axi_s_arready),
    // Write  Data Channel
    .wdata           (i_axi_s_wdata),
    .wstrb           (i_axi_s_wstrb),
    .wlast           (i_axi_s_wlast),
    .wvalid          (i_axi_s_wvalid),
    .wready          (o_axi_s_wready),
    // Read Data Channel
    .rid             (o_axi_s_rid),
    .rdata           (o_axi_s_rdata),
    .rresp           (axi_s_rresp),
    .rlast           (o_axi_s_rlast),
    .rvalid          (o_axi_s_rvalid),
    .rready          (i_axi_s_rready),
    // Write Response Channel
    .bid             (o_axi_s_bid),
    .bresp           (axi_s_bresp),
    .bvalid          (o_axi_s_bvalid),
    .bready          (i_axi_s_bready),
    // - REG-M
    // Write path:
    .reg_wvld        (axi2reg_req.wr.en),
    .reg_wrdy        (axi2reg_ready.wr),
    .reg_waddr       (axi2reg_req.wr.addr),
    .reg_wdata       (axi2reg_req.wr.data),
    .reg_wstrb       (axi2reg_req.wr.wbe),
    .reg_wresp_vld   (axi2reg_rsp.wr_rsp),
    .reg_wresp_rdy   (/*NC*/),
    .reg_wresp_error (axi2reg_rsp.wr_err),
    // Read path:
    .reg_rvld        (axi2reg_req.rd.en),
    .reg_rrdy        (axi2reg_ready.rd),
    .reg_raddr       (axi2reg_req.rd.addr),
    .reg_rresp_vld   (axi2reg_rsp.rd_rsp),
    .reg_rresp_rdy   (/*NC*/),
    .reg_rresp_error (axi2reg_rsp.rd_err),
    .reg_rresp_data  (axi2reg_rsp.data)
  );

  // --------------------
  // Access response
  logic rsp_fifo_pop , rsp_fifo_pop_q, rmw_pushed;
  logic rsp_fifo_push, rsp_fifo_push_q;

  always_comb begin
    axi2reg_rsp.rd_rsp = rsp_fifo_pop_q & ~rsp_fifo_o_data_q.is_rmw;
    axi2reg_rsp.rd_err = rsp_fifo_o_data_q.is_error;

    axi2reg_rsp.wr_rsp = (o_mem_req & o_mem_we) | (new_valid_req_q & new_req_error_q.wr);
    axi2reg_rsp.wr_err = new_req_error_q.wr;
  end

  // Check whether request address is within memory range
  // TODO(jmartins, Bronze, Try to achieve mem range check in a better way -> check cmdblock_desc_mem.sv )
  if (ADDR_WIDTH >= 11) begin : g_addr_hit_space
    assign addr_hit_mem.rd = (axi2reg_req.rd.addr[ADDR_WIDTH-1:10] <= MEM_SPACE_KB[ADDR_WIDTH-11:0]);
    assign addr_hit_mem.wr = (axi2reg_req.wr.addr[ADDR_WIDTH-1:10] <= MEM_SPACE_KB[ADDR_WIDTH-11:0]);
  end else begin : g_addr_always_hit_space
    assign addr_hit_mem = '{default:0};
  end

  // If Out-of-Range error indication is enabled, indicate the error
  if (OOR_ERR_EN) begin : g_out_of_range_error_enable
    assign addr_invalid.rd = ~addr_hit_mem.rd;
    assign addr_invalid.wr = ~addr_hit_mem.wr;
  end else begin : g_out_of_range_error_disable
    assign addr_invalid = '{default:0};
  end

  // Since a read is always a single cycle affair, this is a very simple arb
  // TODO(jmartins, Bronze, Should I use a better arb here? Get cmdblock approach here)
  assign axi2reg_ready.rd = (state==ST_SPM_IDLE);
  assign axi2reg_ready.wr = (state==ST_SPM_IDLE) & ~axi2reg_req.rd.en;

  assign new_req.rd = axi2reg_req.rd.en & axi2reg_ready.rd;
  assign new_req.wr = axi2reg_req.wr.en & axi2reg_ready.wr;

  // The request is valid when it is within the address range of the memory
  assign new_valid_req.rd = new_req.rd & ~addr_invalid.rd;
  assign new_valid_req.wr = new_req.wr & ~addr_invalid.wr;

  // The request is valid when it is within the address range of the memory
  assign new_req_error.rd = new_req.rd & addr_invalid.rd;
  assign new_req_error.wr = new_req.wr & addr_invalid.wr;

  // Let's pipeline it to make it align with ECC computation
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) new_valid_req_q <= '{default:0};
    else          new_valid_req_q <= new_valid_req;
  end
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) new_req_error_q <= '{default:0};
    else          new_req_error_q <= new_req_error;
  end

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) rmw_needed_q <= 1'b0;
    else          rmw_needed_q <= rmw_needed;
  end

  // Write request is writing less than 64-bit
  // -- If we have a partial write there will be a 0 somewhere in the write strobe field
  assign write_partial = ~(&axi2reg_req.wr.wbe);

  // ----------------------------------------------------------------------
  // Check whether a Read-Modify-Write is needed
  // RMW is needed only when ECC protection is enabled and
  // the write request is writing partial data.
  // The read-modify is needed as the ECC code is protecting the full
  // 64-bit of data in the memory and needs to be updated if new data
  // is written.
  if (ECC_PROTECTION_EN) begin : g_ecc
    assign rmw_needed = new_valid_req.wr & write_partial;
  end else begin : g_no_ecc
    assign rmw_needed = 1'b0;
  end

  // When a RMW is issued we'll need to apply a mask. The masked write can be prepared and held here while the
  // masked read data is computed when we receive it from the memory
   // Determine the data that needs to be written in the write part of the RMW
   // TODO - rename the signals below such that they will be consistent
   for (genvar byte_num=0; unsigned'(byte_num) < WBE_WIDTH; byte_num++) begin: gen_mask_wdata
     // Use the write strobe to mask the data that should not be written
     assign wdata_masked[byte_num*8+:8] = {8{axi2reg_req.wr.wbe[byte_num]}} & axi2reg_req.wr.data[byte_num*8+:8];
     // Use the reverse mask to mask the bits of the rdata that need to be written
     assign rdata_masked[byte_num*8+:8]  = {8{~wbe_q[byte_num]}} & axi2reg_rsp.data[byte_num*8+:8];
   end

   // Registers to keep the state of the Write transaction data and wbe during RMW until we get the read data
   always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      wdata_masked_q <= '0;
      wbe_q          <= '0;
    end else if (new_valid_req.wr) begin
      wdata_masked_q <= wdata_masked;
      wbe_q          <= axi2reg_req.wr.wbe;
    end
  end

   // Modify data
   assign rmw_data = wdata_masked_q | rdata_masked;

   // We register req data to meet timing around ECC
   always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      data_req_q <= '0;
    end else if (new_valid_req.wr) begin
      data_req_q <= axi2reg_req.wr.data;
    end
  end
  // Select data to be written to the memory
  // In case no RMW is needed then simply take the input data
  // else use the modified data

  // We need one clock cycle later after (state == ST_SPM_LOCKED) as mem_rvalid_q is asserted exactly one clock cycle later
  assign wdata = (mem_rvalid_q & waiting_for_rmw_q) ? rmw_data : data_req_q;

  // ----------------------------------------------------------------------
  // Input FSM
  always_comb begin
    state_en = 1'b0;
    next_state = state;
    case (state)
      // ----------------------------------------------------------------------
      // ST_SPM_IDLE
      ST_SPM_IDLE: begin
        state_en = (|new_req);
        if(rmw_needed) next_state = ST_SPM_LOCKED; // Need to lock and wait for loopback
        else           next_state = ST_SPM_IDLE;   // Keep pushing
      end
      // ----------------------------------------------------------------------
      // ST_SPM_LOCKED
      // - This state is reached when:
      //    - A read-modify-write is needed
      ST_SPM_LOCKED: begin
       // waiting_for_rmw_q guarantees that the State machine will exit from the LOCK state only
       // when read daya for RMW is returned from the memory
        if(mem_rvalid_q & waiting_for_rmw_q) begin
          state_en = 1'b1;
          next_state = ST_SPM_IDLE;
        end
      end
      // ----------------------------------------------------------------------
      // DEFAULT STATE
      default: begin
        state_en   = 1'b1;
        next_state = ST_SPM_IDLE;
      end
    endcase
  end

  // Update state of FSM
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      state <= ST_SPM_IDLE;
    end else if (state_en) begin
      state <= next_state;
    end
  end


  // Indication that a RMW transaction is in progress
  assign waiting_for_rmw = rsp_fifo_o_data.is_rmw & rsp_fifo_o_valid;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) waiting_for_rmw_q <= 1'b0;
    else          waiting_for_rmw_q <= waiting_for_rmw;
  end

  // Push entries on every memory request
  always_comb begin
    rsp_fifo_i_data.is_error = |new_req_error_q;
    // If the response FSM is locked we're waiting for a read to loopback as a write
    rsp_fifo_i_data.is_rmw = (waiting_for_rmw_q) ? 1'b1 : rmw_needed_q;

    rsp_fifo_i_valid = (o_mem_req & ~o_mem_we) | (new_req_error_q.rd);
  end

  // Pop FIFO entries if
  // - We're IDLE, meaning we keep seeing writes or errors
  // - When we receive a read response and send the write back
  // - When we receive a read response and send it out

  assign rsp_fifo_i_ready = i_mem_rvalid;
  cc_stream_fifo #(
    .Depth(SPM_CTRL_RSP_FIFO_DEPTH),
    .data_t(fsm_rsp_t),
    .FallThrough(1'b0)
    //.AddrWidth() // let the math be done by the module
  ) u_rsp_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),
    .i_flush(1'b0), // never flush
    // Pushed by input FSM
    .i_data (rsp_fifo_i_data),
    .i_valid(rsp_fifo_i_valid),
    .o_ready(rsp_fifo_o_ready),
    // Popped by response FSM
    .o_data (rsp_fifo_o_data),
    .o_valid(rsp_fifo_o_valid),
    .i_ready(rsp_fifo_i_ready),
    // Maybe one day I'll connect the obs
    .o_usage(/*NC*/),
    .o_full (/*NC*/),
    .o_empty(/*NC*/)
  );

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      rsp_fifo_o_data_q <= '{default:'0};
    end else if(rsp_fifo_pop) begin
      rsp_fifo_o_data_q <= rsp_fifo_o_data;
    end
  end
  assign rsp_fifo_push = rsp_fifo_i_valid & rsp_fifo_o_ready;
  assign rsp_fifo_pop  = rsp_fifo_o_valid & rsp_fifo_i_ready;
  assign rmw_pushed = rsp_fifo_i_data.is_rmw & rsp_fifo_push;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n)          in_flight_rmw_addr_all_bit <= '{default:0};
    else if(rmw_pushed) in_flight_rmw_addr_all_bit <= mem_addr_all_bit;
  end
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) rsp_fifo_pop_q <= 1'b0;
    else          rsp_fifo_pop_q <= rsp_fifo_pop;
  end
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) rsp_fifo_push_q <= 1'b0;
    else          rsp_fifo_push_q <= rsp_fifo_push;
  end

  //--------------------------
  // The memory response is always pipelined in order to allow
  // timing to be met.
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n)
      mem_rdata_q  <= '0;
    else if (i_mem_rvalid)
      mem_rdata_q <= i_mem_rdata; // Gate the 72 flops by adding an enable on them
  end

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n)
      mem_rvalid_q <= 1'b0;
    else
      mem_rvalid_q <= i_mem_rvalid;
  end

  // ------------------------------------------------------------
  // spyglass disable_block STARC-2.3.4.3
  // spyglass disable_block STARC05-3.3.1.4b
  // Register address and size of request
  assign addr_d = axi2reg_ready.wr ? axi2reg_req.wr.addr : axi2reg_req.rd.addr;

  always_ff @(posedge i_clk) begin
    if (|new_req) begin
      addr_q <= addr_d[MEM_ADDR_MSB:0];
    end
  end
  // spyglass enable_block STARC05-3.3.1.4b
  // spyglass enable_block STARC-2.3.4.3

  assign write_req = waiting_for_rmw_q | new_valid_req_q.wr;

  assign mem_addr_all_bit = (waiting_for_rmw_q) ? in_flight_rmw_addr_all_bit : addr_q;
  assign mem_req = (|new_valid_req_q);
  assign mem_we = (new_valid_req_q.wr & ~rmw_needed_q); // Gated with rmw_needed_q to guarantee that read is first generated during rmw

  if (ECC_PROTECTION_EN) begin : g_ecc_mem_wbe
    assign mem_wbe = write_req ? WBE_ALL_ONES : WBE_ALL_ZERO;
  end else begin : g_no_ecc_mem_wbe
    assign mem_wbe   = write_req ? wbe_q : WBE_ALL_ZERO;
  end

  // ----------------------------------------------------------------------
  // Interface to Memory
  // - Write data and byte enable dependent on ECC generate block
  always_comb begin
    if(waiting_for_rmw_q) begin
      // If we get here we know we'll get a write of the entire memory line to the address of the
      // rmw read issued earlier
      o_mem_req = mem_rvalid_q;
      o_mem_we  = 1'b1;
      o_mem_be  = WBE_ALL_ONES;
    end else begin
      o_mem_req = mem_req;
      o_mem_we  = mem_we;
      o_mem_be  = mem_wbe;
    end
      o_mem_wdata = mem_wdata;
      o_mem_addr = mem_addr_all_bit[MEM_ADDR_MSB:MEM_ADDR_LSB];
  end

  // ----------------------------------------------------------------------
  // ECC Protection

  // Encode the ECC code bits and pad them to the write access data
  // - With ECC Enabled
  //  -- Encode bits and add them to the MSBs of the data to be written
  //  -- The entire data granule is always written
  // - With ECC Disabled
  //  -- Feedthrough of the data
  //  -- Support for strobe writes since we don't need to recompute ECC
  if (ECC_PROTECTION_EN) begin : gen_ecc_enc
    prim_secded_72_64_enc u_ecc_enc (
      .data_i  (wdata),
      .data_o  (mem_wdata)
    );
  end else begin: gen_noecc_enc
    assign mem_wdata = wdata;
  end

  // Decode the ECC bits from the read data and determine whether an ECC error is present
  if (ECC_PROTECTION_EN) begin : gen_ecc_dec
    logic [1:0]             err;
    spm_ecc_err_syndrome_t  syndrome;
    spm_axi_data_t          mem_rdata_repaired;
    spm_mem_data_t          mem_rdata_gated;

    // Make sure the read data is active only one clock cycle to the ECC decoder
    assign mem_rdata_gated = (mem_rdata_q & {$bits(spm_mem_data_t){mem_rvalid_q}});

    prim_secded_72_64_dec u_ecc_dec (
      .data_i     (mem_rdata_gated),
      .data_o     (mem_rdata_repaired),
      .syndrome_o (syndrome),
      .err_o      (err)
    );

    assign err_status.ecc_err        = (|err) & ~i_scp_ecc_disable;
    assign err_status.ecc_err_type   = spm_ecc_err_type_t'(err[1]);
    assign err_status.ecc_err_index  = get_err_index(mem_addr_all_bit);

    assign err_status.ecc_err_syndrome  = syndrome;
    // Data repaired
    assign  axi2reg_rsp.data = i_scp_ecc_disable ? mem_rdata_q[SPM_AXI_DATA_WIDTH-1:0] : mem_rdata_repaired;


    // A flop to keep the higest severity state for the "ECC error type"
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (~i_rst_n) begin
        highest_sever_err_seen_q <= SINGLE;
      end
      else if(err_status.ecc_err & (err_status.ecc_err_type == DOUBLE)) begin
        highest_sever_err_seen_q <= DOUBLE;
      end
    end

    // Indication to disable updating the ECC CSR in order to maintain the the highest severity of the error
    assign disable_csr_err_status_update = ((err_status.ecc_err_type == SINGLE) & (highest_sever_err_seen_q == DOUBLE));


  end else begin: gen_noecc_dec
    // No error info present
    assign  err_status.ecc_err          = '0;
    assign  err_status.ecc_err_type     = spm_ecc_err_type_t'('0);
    assign  err_status.ecc_err_index    = '0;
    assign  err_status.ecc_err_syndrome = '0;

    assign  highest_sever_err_seen_q = '0;
    assign  disable_csr_err_status_update = 1'b0;
    // Data as read from the memory
    assign  axi2reg_rsp.data = mem_rdata_q;
  end

  // ----------------------------------------------------------------------
  // Output handling

  // Error reportings
  always_comb begin
    o_scp_error_status.ecc_err          = (err_status.ecc_err & ~disable_csr_err_status_update);
    o_scp_error_status.ecc_err_index    = err_status.ecc_err_index;
    o_scp_error_status.ecc_err_type     = err_status.ecc_err_type;
    o_scp_error_status.ecc_err_syndrome = err_status.ecc_err_syndrome;

    o_irq = highest_sever_err_seen_q;
  end


// Internal observation signals
  always_comb begin
    o_spm_obs.irq                = o_irq;
    o_spm_obs.mem_rvalid         = i_mem_rvalid;
    o_spm_obs.mem_we             = o_mem_we;
    o_spm_obs.mem_req            = o_mem_req;
    o_spm_obs.rsp_fifo_pop       = rsp_fifo_pop;
    o_spm_obs.rsp_fifo_push      = rsp_fifo_push;
    o_spm_obs.waiting_for_rmw    = waiting_for_rmw;
    o_spm_obs.state              = logic'(state);
    o_spm_obs.axi2reg_rsp_rd_err = axi2reg_rsp.rd_err;
    o_spm_obs.axi2reg_rsp_rd_rsp = axi2reg_rsp.rd_rsp;
    o_spm_obs.axi2reg_ready_rd   = axi2reg_ready.rd;
    o_spm_obs.axi2reg_req_rd_en  = axi2reg_req.rd.en;
    o_spm_obs.axi2reg_rsp_wr_err = axi2reg_rsp.wr_err;
    o_spm_obs.axi2reg_rsp_wr_rsp = axi2reg_rsp.wr_rsp;
    o_spm_obs.axi2reg_ready_wr   = axi2reg_ready.wr;
    o_spm_obs.axi2reg_req_wr_en  = axi2reg_req.wr.en;
  end

endmodule

`endif // SPM_CONTROL_SV
