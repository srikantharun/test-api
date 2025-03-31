// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>


/// Two Port (1R + 1W) Memory deconflict to avoid reading and writing in the same cycle.
///
/// In case there is a read and write in the same cycle the write will be delayed.
/// Written data will be return instead of read data in case a delayed write conflicts with a new read.
///
/// !!! note "Assumption"
///
///     - Read and write are on the same clock.
///     - Read Latency is 1.
///
module axe_ccl_mem_1rp_1wp_deconflict #(
  /// Number of Words of the Data Array `addr_t = logic [$clog2(NumWords)-1:0]`
  parameter int unsigned NumWords    = 16,
  /// The Data Width of each Individual Word in Bits
  parameter int unsigned DataWidth   = 16,
  /// The Byte Width (in Bits) which will patition write data. MUST be a divisor of DataWidth!
  parameter int unsigned ByteWidth   = 1,

  /// Derived parameter: Address type
  localparam type addr_t   = logic[$clog2(NumWords)-1:0],
  /// Derived Parameter: Payload Data Type
  localparam type data_t   = logic[DataWidth-1:0],
  /// Derived Paramter: Byte Enable vector
  localparam type enable_t = logic[(DataWidth/ByteWidth)-1:0]
) (
  /// Clock for Writes and Reads, positive edge triggered
  input  wire       i_clk,
  /// Asynchronous reset for writes and Reads, active low
  input  wire       i_rst_n,

  /// Request to write to the array, active high
  input  logic      i_wr_req,
  /// The Word address of the write request
  input  addr_t     i_wr_addr,
  /// The write data payload
  input  data_t     i_wr_data,
  /// The write enable mask for the individual bytes
  input  enable_t   i_wr_mask,

  /// Request to write to the array, active high
  input  logic      i_rd_req,
  /// The word address of the read request
  input  addr_t     i_rd_addr,
  /// The read data payload. updates `Latency` cycles after the respective request.
  output  data_t    o_rd_data,

  /// Request to read from the array, active high
  output logic      o_wr_req,
  /// The Word address of the write request
  output addr_t     o_wr_addr,
  /// The write data payload
  output data_t     o_wr_data,
  /// The write enable mask for the individual bytes
  output enable_t   o_wr_mask,

  /// Request to read from the array, active high
  output logic      o_rd_req,
  /// The word address of the read request
  output addr_t     o_rd_addr,
  /// The read data payload. updates `Latency` cycles after the respective request.
  input  data_t     i_rd_data
);

  typedef struct packed {
    addr_t addr;
    data_t data;
    enable_t mask;
  } wr_info_t;

  typedef enum logic {
    s_norm,
    s_clash
  } state_e;

  state_e state_d, state_q;

  logic block_read;
  logic block_write;

  logic addr_match, stored_wr_match, stored_rd_match;

  logic wr_info_en;
  wr_info_t wr_info, wr_info_q;
  logic rd_data_en;
  data_t rd_data_q;
  logic ret_read_en;
  logic ret_read_q;

  always_comb wr_info = wr_info_t'{
    data: i_wr_data,
    addr: i_wr_addr,
    mask: i_wr_mask
  };

  // either block a write when in normal state, or always write as conflict is resolved by delaying write:
  always_comb o_wr_req  = (state_q == s_norm) ? i_wr_req & ~block_write : 1'b1;
  // block read in case a delayed write goes to the same address as currently being read. Write data can be return immediatly
  always_comb o_rd_req  = i_rd_req & ~block_read;
  always_comb o_rd_addr = i_rd_addr;

  always_comb o_wr_addr = (state_q == s_norm) ? i_wr_addr : wr_info_q.addr;
  always_comb o_wr_data = (state_q == s_norm) ? i_wr_data : wr_info_q.data;
  always_comb o_wr_mask = (state_q == s_norm) ? i_wr_mask : wr_info_q.mask;
  always_comb o_rd_data = ret_read_q ? rd_data_q : i_rd_data;

  always_comb addr_match      = i_wr_addr      == i_rd_addr;
  always_comb stored_wr_match = wr_info_q.addr == i_rd_addr;

  always_comb begin
    state_d     = s_norm; // by default return back
    wr_info_en  = 1'b0;
    block_write = 1'b0;
    block_read  = 1'b0;
    rd_data_en  = 1'b0;

    unique case (state_q)
      s_norm: begin
        // clash when read and write both have the same row address and are requesting the memory in the same cycle
        if (addr_match && (i_wr_req & i_rd_req)) begin
          state_d     = s_clash;
          wr_info_en  = 1'b1;
          block_write = 1'b1;
        end
      end

      s_clash: begin
        // there has been a clash and the stored write needs to be written
        if (i_wr_req) begin // in case a new write comes in: store and stay in state
          wr_info_en = 1'b1;
          state_d    = s_clash;
        end

        if (i_rd_req && stored_wr_match) begin // also a read active, that is hitting what we try to write. Block read and return write data
          block_read = 1'b1;
          rd_data_en = 1'b1;
        end
      end
      default: state_d = s_norm;
    endcase
  end

  // store the read and write request and or rd data if required
  always_comb ret_read_en = rd_data_en | ret_read_q;
  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n) begin
      wr_info_q  <= '0;
      rd_data_q  <= '0;
      ret_read_q <= '0;
      state_q    <= s_norm;
    end else begin
      state_q   <= state_d;
      if (wr_info_en)  wr_info_q <= wr_info;
      if (rd_data_en)  rd_data_q <= wr_info_q.data;
      if (ret_read_en) ret_read_q <= rd_data_en;
    end
  end

endmodule
