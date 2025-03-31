`ifndef SYNC_FIFO_GUARD
`define SYNC_FIFO_GUARD

module sync_fifo #( parameter int unsigned                          FIFO_DEPTH      = 32 ,
                    parameter type                                  data_t          = logic [31:0],
                    parameter int unsigned                          MEM_MACRO_USE   = 0  ,
                    parameter int unsigned                          MEM_MACRO_TYPE  = 0  ,
                    /// The data flip-flops are implemented with reset flops
                    parameter bit                                   RESET_DATA_FLOP = 1  ,
                    parameter bit         [$clog2(FIFO_DEPTH)-1:0] ALMOST_EMPTY_THR = 1  ,
                    parameter bit         [$clog2(FIFO_DEPTH)-1:0] ALMOST_FULL_THR  = 1
                  )
(

  input  wire  i_clk          ,
  input  wire  i_rst_n         ,

  input  logic  rd_req_i       ,
  output data_t rd_data_o      ,
  output logic  empty_o        ,
  output logic  almost_empty_o ,

  input  logic  wr_req_i       ,
  input  data_t wr_data_i      ,
  output logic  full_o         ,
  output logic  almost_full_o

);

  if (MEM_MACRO_USE  != 0) $fatal(1, "Parameter: 'MEM_MACRO_USE' is not supported; is: %d", MEM_MACRO_USE);
  if (MEM_MACRO_TYPE != 0) $fatal(1, "Parameter: 'MEM_MACRO_TYPE' is not supported; is: %d", MEM_MACRO_TYPE);

  localparam int unsigned           PtrWidth         = $clog2(FIFO_DEPTH);
  localparam bit [PtrWidth - 1 : 0] PtrMaxVal        = FIFO_DEPTH - 1;
  localparam bit [PtrWidth     : 0] PtrDepthDiff     =
                                    { 1'b1, {PtrWidth{1'b0}} } - FIFO_DEPTH[PtrWidth:0];
  localparam bit [PtrWidth     : 0] AlmostFullClrVal = FIFO_DEPTH - ALMOST_FULL_THR;
  localparam bit [PtrWidth     : 0] AlmostFullSetVal = FIFO_DEPTH - ALMOST_FULL_THR - 1;
  localparam bit [PtrWidth     : 0] AlmostEmptyClrVal = ALMOST_EMPTY_THR;
  localparam bit [PtrWidth     : 0] AlmostEmptySetVal = ALMOST_EMPTY_THR + 1;

  // Internal registers and wires
  logic [PtrWidth : 0] wr_ptr_nxt       ;
  logic [PtrWidth : 0] wr_ptr           ;
  logic [PtrWidth : 0] rd_ptr_nxt       ;
  logic [PtrWidth : 0] rd_ptr           ;
  logic [PtrWidth : 0] wr_ptr_chk       ;
  logic [PtrWidth : 0] rd_ptr_chk       ;
  logic                ptr_msb_diff     ;
  logic [PtrWidth : 0] words_num        ;
  logic                flags_update     ;
  logic                wr_full_val      ;
  logic                wr_full          ;
  logic                almost_full_set  ;
  logic                almost_full_clr  ;
  logic                almost_full      ;
  logic                rd_empty         ;
  logic                almost_empty_set ;
  logic                almost_empty_clr ;
  logic                almost_empty     ;


  // FIFO write pointer
  always_comb begin
    if (wr_ptr[PtrWidth - 1 : 0] == PtrMaxVal)
      wr_ptr_nxt = { !wr_ptr[PtrWidth], {PtrWidth{1'b0}} };
    else
      wr_ptr_nxt = wr_ptr + { {PtrWidth{1'b0}}, 1'b1 };
  end
  always_comb wr_ptr_chk = (wr_req_i & !wr_full) ? wr_ptr_nxt : wr_ptr;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) wr_ptr <= '0;
    else if (wr_req_i & !wr_full) wr_ptr <= wr_ptr_nxt;

  // FIFO read pointer
  always_comb begin
    if (rd_ptr[PtrWidth - 1 : 0] == PtrMaxVal)
      rd_ptr_nxt = { !rd_ptr[PtrWidth], {PtrWidth{1'b0}} };
    else
      rd_ptr_nxt = rd_ptr + { {PtrWidth{1'b0}}, 1'b1 };
  end
  always_comb rd_ptr_chk = (rd_req_i & !rd_empty) ? rd_ptr_nxt : rd_ptr;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) rd_ptr <= '0;
    else if (rd_req_i & !rd_empty) rd_ptr <= rd_ptr_nxt;

  // FIFO full logic
  assign flags_update = wr_req_i | rd_req_i;
  assign wr_full_val  = wr_ptr_chk == {!rd_ptr_chk[PtrWidth], rd_ptr_chk[PtrWidth-1:0]};

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)          wr_full <= 1'b0;
    else if (flags_update) wr_full <= wr_full_val;


  assign ptr_msb_diff = wr_ptr[PtrWidth] ^ rd_ptr[PtrWidth];
  assign words_num    = {ptr_msb_diff, wr_ptr[PtrWidth-1:0]} - {1'b0, rd_ptr[PtrWidth-1:0]} -
                        (ptr_msb_diff? PtrDepthDiff : {(PtrWidth+1){1'b0}});

  assign almost_full_clr = (words_num == AlmostFullClrVal) &  rd_req_i & !wr_req_i;
  assign almost_full_set = (words_num == AlmostFullSetVal) & !rd_req_i &  wr_req_i;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)              almost_full <= 1'b0;
    else if (almost_full_clr) almost_full <= 1'b0;
    else if (almost_full_set) almost_full <= 1'b1;

  // FIFO empty logic
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)           rd_empty <= 1'b1;
    else if (flags_update) rd_empty <= rd_ptr_chk == wr_ptr_chk;

  assign almost_empty_set = (words_num == AlmostEmptySetVal) &  rd_req_i & !wr_req_i;
  assign almost_empty_clr = (words_num == AlmostEmptyClrVal) & !rd_req_i &  wr_req_i;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)               almost_empty <= 1'b1;
    else if (almost_empty_set) almost_empty <= 1'b1;
    else if (almost_empty_clr) almost_empty <= 1'b0;

  // Output FIFO flags
  assign empty_o        = rd_empty;
  assign almost_empty_o = almost_empty;

  assign full_o         = wr_full;
  assign almost_full_o  = almost_full;

  // FIFO
    if (MEM_MACRO_USE == 1) begin : g_mem_macro_

      if (MEM_MACRO_TYPE == 0) begin : g_reg_file_
      end // g_reg_file_

      else if (MEM_MACRO_TYPE == 1) begin : g_sram_
      end // g_sram_

      // synopsys translate_off
      else begin : g_macro_err_
        $error("Incorrect MEM_MACRO_TYPE parameter value is used");
      end
      // synopsys translate_on

    end // g_mem_macro_

    else begin : g_reg_arr_
      data_t fifo_reg[FIFO_DEPTH];

      if (RESET_DATA_FLOP) begin : gen_data_reset
        // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
        always_ff @(posedge i_clk or negedge i_rst_n) begin
          if (!i_rst_n) begin
            foreach (fifo_reg[entry_idx]) fifo_reg[entry_idx] <= data_t'(0);
          end else if (wr_req_i & !wr_full) begin
            fifo_reg[wr_ptr[PtrWidth-1:0]] <= wr_data_i;
          end
        end
      end : gen_data_reset
      else begin : gen_data_no_reset
        // DFFL: D-Flip-Flop, load enable
        always_ff @(posedge i_clk) begin
          if (wr_req_i & !wr_full) fifo_reg[wr_ptr[PtrWidth-1:0]] <= wr_data_i;
        end
      end : gen_data_no_reset


      assign rd_data_o = fifo_reg[rd_ptr[PtrWidth-1:0]];

    end // g_reg_arr_




  // Assertions
  // synopsys translate_off
  `ifdef ASSERTIONS_ON
    bit               assert_disable;
    bit [PtrWidth:0] cnt;

    initial begin
      assert_disable = 1'b1;
      @(posedge i_clk);
      @(negedge i_rst_n);
      assert_disable = 1'b0;
    end

    always @(posedge i_clk)
      if (!i_rst_n)
        cnt = '0;
      else
        cnt = cnt - {'0, rd_req_i & !rd_empty} + {'0, wr_req_i & !wr_full};

    property p_bad_access(inc, flag);
      @(posedge i_clk)
      disable iff (!i_rst_n | assert_disable) inc |-> ~flag;
    endproperty : p_bad_access

    property p_almost_full(set_clr, threshold);
      @(posedge i_clk)
      disable iff (!i_rst_n | assert_disable)
                  (set_clr ? (cnt >= (FIFO_DEPTH - threshold)) : (cnt <  (FIFO_DEPTH - threshold)))
                  |-> (set_clr ? almost_full : !almost_full);
    endproperty : p_almost_full

    property p_almost_empty(set_clr, threshold);
      @(posedge i_clk)
      disable iff (!i_rst_n | assert_disable)
                  (set_clr ? (cnt <= threshold) : (cnt >  threshold))
                   |-> (set_clr ? almost_empty : !almost_empty);
    endproperty : p_almost_empty

    property p_empty;
      @(posedge i_clk)
      disable iff (!i_rst_n | assert_disable) (rd_empty ^ (cnt != '0));
    endproperty : p_empty

    property p_full;
      @(posedge i_clk)
      disable iff (!i_rst_n | assert_disable) (wr_full ^ (cnt != FIFO_DEPTH));
    endproperty

    property p_words_num;
      @(posedge i_clk)
      disable iff (!i_rst_n | assert_disable) (words_num === cnt);
    endproperty

    // Checks if attempt to write into full FIFO happened
    check_wr_to_full       : assert property(p_bad_access(wr_req_i, full_o))
                             else $error("Write access attempted to full FIFO");

    // Checks if attempt to read from empty FIFO happened
    check_rd_from_empty    : assert property(p_bad_access(rd_req_i, empty_o))
                             else $error("Read access attempted from empty FIFO");

    // Checks whether almost_full flag goes to 1 at the right moment
    check_almost_full_set  : assert property(p_almost_full(1, ALMOST_FULL_THR))
                             else $error("almost_full flag is incorrectly set to 1");

    // Checks whether almost_full flad goes to 0 at the right moment
    check_almost_full_clr  : assert property(p_almost_full(0, ALMOST_FULL_THR))
                             else $error("almost_full flag is incorrectly set to 0");

    // Checks whether almost_empty flag goes to 1 at the right moment
    check_almost_empty_set : assert property(p_almost_empty(1, ALMOST_EMPTY_THR))
                             else $error("almost_empty flag is incorrectly set to 1");

    // Checks whether almost_empty flad goes to 0 at the right moment
    check_almost_empty_clr : assert property(p_almost_empty(0, ALMOST_EMPTY_THR))
                             else $error("almost_empty flag is incorrectly set to 0");

    // Check if empty flag works correctly
    check_empty            : assert property(p_empty)
                             else $error("empty flag has inccorrect value");

    // Check if full flag operates correctly
    check_full             : assert property(p_full)
                             else $error("full flag has incorrect value");

    // Check if words_num works correctly
    check_words_num        : assert property(p_words_num)
                             else $error("Incorrect value in words_num counter");

  `endif
  // synopsys translate_on

endmodule

`endif // SYNC_FIFO_GUARD
