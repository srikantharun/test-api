// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: static descriptor memory, with AXI and one wide row read (stream like) interface
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_DESC_MEM__SV_
`define _CMDBLOCK_DESC_MEM__SV_

module cmdblock_desc_mem #(
  parameter int IDW = 4,
  parameter int AW  = 36,
  parameter int DW  = 64,
  parameter int BW  = 6,

  parameter int MEM_DEPTH = 4,
  parameter int MEM_WIDTH = 30,
  parameter int ARB_SCHEME = 1,
  parameter int OUTP_SHIELD = 0,
  parameter int ADDR_CAP = 'h1000,

  parameter int DATA_ALIGN = DW,  // Note: changing this value to have multiple rows inside a DW
                                           //       will result a different memory configuration.
                                           // .MEM_DEPTH(4), .MEM_WIDTH(30) with .DW(64) and .DATA_ALIGN(32)
                                           // will for example result in a memory of 2 deep and 60 wide

  parameter int USE_MACRO = 0,
  parameter SRAM_IMPL_KEY = "HD",
  parameter type ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  parameter type ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t,
  parameter int GENERAL_CLOCK_GATE = 0,
  parameter int VERSION = 0  // 0: normal, 1: error response fixed to 0 (ECO)
) (
  input wire i_clk,
  input logic i_rst_n,
  input logic scan_mode,

  ///// AXI slave:
  // Write Address Channel
  input  logic [ IDW-1:0] awid,
  input  logic [  AW-1:0] awaddr,
  input  logic [  BW-1:0] awlen,
  input  logic [     2:0] awsize,
  input  logic [     1:0] awburst,
  input  logic            awvalid,
  output logic            awready,
  // Read Address Channel
  input  logic [ IDW-1:0] arid,
  input  logic [  AW-1:0] araddr,
  input  logic [  BW-1:0] arlen,
  input  logic [     2:0] arsize,
  input  logic [     1:0] arburst,
  input  logic            arvalid,
  output logic            arready,
  // Write  Data Channel
  input  logic [  DW-1:0] wdata,
  input  logic [DW/8-1:0] wstrb,
  input  logic            wlast,
  input  logic            wvalid,
  output logic            wready,
  // Read Data Channel
  output logic [ IDW-1:0] rid,
  output logic [  DW-1:0] rdata,
  output logic [     1:0] rresp,
  output logic            rlast,
  output logic            rvalid,
  input  logic            rready,
  // Write Response Channel
  output logic [ IDW-1:0] bid,
  output logic [     1:0] bresp,
  output logic            bvalid,
  input  logic            bready,

  ///// wide row read slave
  input  logic                         rd_row_rvalid,
  input  logic [cc_math_pkg::index_width(MEM_DEPTH)-1:0] rd_row_raddr,
  output logic                         rd_row_rready,

  output logic                 rd_resp_vld,
  output logic [MEM_WIDTH-1:0] rd_resp_data,

  ///// SRAM Sideband Signals
  input  ram_impl_inp_t i_sram_impl,
  output ram_impl_oup_t o_sram_impl
);

  // in case the mem width is smaller then the DW, it's optional to have multiple 'rows' in one DW if the alignement is set smaller
  // else the default alignment of DW is used
  localparam int Aligment = ((MEM_WIDTH < DW) && (DATA_ALIGN < DW)) ? DATA_ALIGN : DW;
  // how many 'rows' that need to be placed in one memory row entry:
  localparam int MemRowsInDw = (MEM_WIDTH < DW) ? DW / Aligment : 1;
  // The real total memory width now depends on how many 'rows' are placed in an memory entry:
  localparam int TotMemWidth = MemRowsInDw * MEM_WIDTH;
  // And the depth can be smaller because of that:
  localparam int TotMemDepth = (MEM_DEPTH + MemRowsInDw - 1) / MemRowsInDw;
  // get memory width alligned on DW size. This will be the address offset between memory rows
  localparam int MemWidthAligned = ((TotMemWidth + DW - 1) / DW) * DW;
  localparam int TotAddrSpace = MemWidthAligned * TotMemDepth;

  localparam int RowInDwBits = cc_math_pkg::index_width(MemRowsInDw);
  localparam int RowSelBits = $clog2(TotMemDepth);
  localparam int DwSelBits = $clog2((TotMemWidth + DW - 1) / DW);
  localparam int DwSelLsb = $clog2(DW / 8);

  localparam int ChkAddrMsb = $clog2(ADDR_CAP);

  /// AXI2REG:
  logic axi2reg_wvld, axi2reg_wrdy, axi2reg_wresp_vld, axi2reg_wresp_rdy;
  logic axi2reg_rvld, axi2reg_rrdy, axi2reg_rresp_vld, axi2reg_rresp_rdy;
  logic axi2reg_wresp_error, axi2reg_rresp_error;
  logic [                    DW-1:0] axi2reg_rresp_data;
  logic [                    DW-1:0] axi2reg_wdata;
  logic [                    AW-1:0] axi2reg_waddr;
  logic [                  DW/8-1:0] axi2reg_wstrb;
  logic [                    AW-1:0] axi2reg_raddr;

  /// str arbiters:
  logic                              axi_arb_vld;
  logic                              axi_arb_rdy;
  logic                              axi_arb_sel;

  logic                              mem_arb_vld;
  logic                              mem_arb_rdy;
  logic                              mem_arb_sel;

  logic                              mem_res_vld;

  // translated AXI addressing:
  logic [          RowSelBits-1:0] axi_wmem_addr;
  logic [DwSelBits+DwSelLsb-1:0] axi_wmem_sub_addr;
  logic                              axi_waddr_out_of_range;
  logic [          RowSelBits-1:0] axi_rmem_addr;
  logic [DwSelBits+DwSelLsb-1:0] axi_rmem_sub_addr;
  logic                              axi_raddr_out_of_range;

  // mem driver / selection:
  logic [          RowSelBits-1:0] mem_addr;
  logic [        RowInDwBits-1:0] mem_row_sel;
  reg   [        RowInDwBits-1:0] mem_res_row_sel;
  reg   [        RowInDwBits-1:0] mem_res_row_sel_q;
  logic [DwSelBits+DwSelLsb-1:0] mem_sub_addr;
  reg   [DwSelBits+DwSelLsb-1:0] mem_sub_addr_q;
  logic [DwSelBits+DwSelLsb-1:0] mem_res_sub_addr;
  reg   [DwSelBits+DwSelLsb-1:0] mem_res_sub_addr_q;
  logic [                       1:0] dat_sel;
  logic [                       1:0] resp_sel;
  reg   [                       1:0] resp_sel_q;
  reg                                mem_res_vld_q;

  // memory
  logic                              mem_we_n;
  logic [         TotMemWidth-1:0] mem_rdata;
  logic [         TotMemWidth-1:0] mem_rdata_q;
  logic [         TotMemWidth-1:0] mem_wdata;
  logic [   (TotMemWidth+7)/8-1:0] mem_wbyte_en;

  logic                              addr_out_of_range;
  logic                              resp_addr_out_of_range;
  logic                              resp_addr_out_of_range_q;

  logic                              not_connected;

  function automatic int min(int a, int b);
    if (a < b) return a;
    else return b;
  endfunction
  // no backpressure on memory possible:
  // spyglass disable_block W528
  if (TotMemWidth - DW <= 0) begin : gen_nc_with_subaddr
    assign not_connected = axi2reg_wresp_rdy | axi2reg_rresp_rdy | (|mem_sub_addr_q) | (|mem_res_sub_addr_q);
  end else begin : gen_nc_without_subaddr
    assign not_connected = axi2reg_wresp_rdy | axi2reg_rresp_rdy;
  end
  // spyglass enable_block W528

  //////// AXI 2 REG, convert AXI to simple alligned single access
  axi2reg #(
    .IDW(IDW),
    .AW(AW),
    .DW(DW),
    .BW(BW),
    .NR_WR_REQS(2),
    .NR_RD_REQS(2),
    .WBUF(2),
    .OSR(2),
    .RD_RESP_DEPTH(2),
    .WR_RESP_DEPTH(2)
  ) i_axi_reg (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    ///// AXI slave:
    // Write Address Channel
    .awid(awid),
    .awaddr(awaddr),
    .awlen(awlen),
    .awsize(awsize),
    .awburst(awburst),
    .awvalid(awvalid),
    .awready(awready),
    // Read Address Channel
    .arid(arid),
    .araddr(araddr),
    .arlen(arlen),
    .arsize(arsize),
    .arburst(arburst),
    .arvalid(arvalid),
    .arready(arready),
    // Write  Data Channel
    .wdata(wdata),
    .wstrb(wstrb),
    .wlast(wlast),
    .wvalid(wvalid),
    .wready(wready),
    // Read Data Channel
    .rid(rid),
    .rdata(rdata),
    .rresp(rresp),
    .rlast(rlast),
    .rvalid(rvalid),
    .rready(rready),
    // Write Response Channel
    .bid(bid),
    .bresp(bresp),
    .bvalid(bvalid),
    .bready(bready),

    ////// reg master:
    // Write path:
    .reg_wvld(axi2reg_wvld),
    .reg_wrdy(axi2reg_wrdy),
    .reg_waddr(axi2reg_waddr),
    .reg_wdata(axi2reg_wdata),
    .reg_wstrb(axi2reg_wstrb),
    .reg_wresp_vld(axi2reg_wresp_vld),
    .reg_wresp_rdy(axi2reg_wresp_rdy),
    .reg_wresp_error(axi2reg_wresp_error),

    // Read path:
    .reg_rvld(axi2reg_rvld),
    .reg_rrdy(axi2reg_rrdy),
    .reg_raddr(axi2reg_raddr),
    .reg_rresp_vld(axi2reg_rresp_vld),
    .reg_rresp_rdy(axi2reg_rresp_rdy),
    .reg_rresp_error(axi2reg_rresp_error),
    .reg_rresp_data(axi2reg_rresp_data)
  );

  cmdblock_str_arb #(
    .PRIO(1)
  ) i_axi_r_w_arb (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .sel(axi_arb_sel),

    .vld_s0(axi2reg_wvld),
    .rdy_s0(axi2reg_wrdy),
    .vld_s1(axi2reg_rvld),
    .rdy_s1(axi2reg_rrdy),

    .vld_m(axi_arb_vld),
    .rdy_m(axi_arb_rdy)
  );

  cmdblock_str_arb #(
    .PRIO(ARB_SCHEME)
  ) i_axi_row_arb (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .sel(mem_arb_sel),

    .vld_s0(rd_row_rvalid),
    .rdy_s0(rd_row_rready),
    .vld_s1(axi_arb_vld),
    .rdy_s1(axi_arb_rdy),

    .vld_m(mem_arb_vld),
    .rdy_m(mem_arb_rdy)
  );

  assign dat_sel = {mem_arb_sel, axi_arb_sel};
  assign mem_arb_rdy = '1;  // mem always accepting

  always_comb begin : i_axi_waddr_trans
    // default out of range, unless hit found:
    axi_waddr_out_of_range = 1'b1;
    axi_wmem_sub_addr = axi2reg_waddr[ChkAddrMsb-1:DwSelLsb];
    axi_wmem_addr = 0;

    for (int i = 0; i < TotMemDepth; i++) begin
      if ((unsigned'(i*MemWidthAligned/DW) <= axi2reg_waddr[ChkAddrMsb-1:DwSelLsb]) &&
            (unsigned'((i+1)*MemWidthAligned/DW) > axi2reg_waddr[ChkAddrMsb-1:DwSelLsb])) begin
        // only one range will be active at the time
        // spyglass disable_block W415a
        axi_wmem_addr = unsigned'(i);
        axi_wmem_sub_addr = axi2reg_waddr[ChkAddrMsb-1:0] - unsigned'(i * (MemWidthAligned / 8));
        axi_waddr_out_of_range = 1'b0;
        // spyglass enable_block W415a
      end
    end
  end

  always_comb begin : i_axi_raddr_trans
    // default out of range, unless hit found:
    axi_raddr_out_of_range = 1'b1;
    axi_rmem_sub_addr = axi2reg_raddr[ChkAddrMsb-1:0];
    axi_rmem_addr = 0;

    for (int i = 0; i < TotMemDepth; i++) begin
      if ((unsigned'(i*MemWidthAligned/DW) <= axi2reg_raddr[ChkAddrMsb-1:DwSelLsb]) &&
            (unsigned'((i+1)*MemWidthAligned/DW) > axi2reg_raddr[ChkAddrMsb-1:DwSelLsb])) begin
        // only one range will be active at the time
        // spyglass disable_block W415a
      axi_rmem_addr = unsigned'(i);
        axi_rmem_sub_addr = axi2reg_raddr[ChkAddrMsb-1:0] - unsigned'(i * (MemWidthAligned / 8));
        axi_raddr_out_of_range = 1'b0;
        // spyglass enable_block W415a
      end
    end
  end

  always_comb begin : i_mem_req_in_sel
    unique case (dat_sel)
      2'b00, 2'b01: begin  // rd_row
        mem_we_n = 'b1;
        if (MemRowsInDw > 1) begin
          mem_addr = rd_row_raddr[cc_math_pkg::index_width(MEM_DEPTH)-1:RowInDwBits];
          mem_row_sel = rd_row_raddr[RowInDwBits-1:0];
        end else begin
          mem_addr = rd_row_raddr[cc_math_pkg::index_width(MEM_DEPTH)-1:0];
        end
        mem_sub_addr = '0;
        addr_out_of_range = '0;
      end
      2'b10: begin  // axi write
        mem_we_n = 'b0;
        mem_addr = axi_wmem_addr;
        if (MemRowsInDw > 1) mem_row_sel = '0;
        mem_sub_addr = axi_wmem_sub_addr;
        addr_out_of_range = axi_waddr_out_of_range;
      end
      default: begin // 2'b11 axi read
        mem_we_n = 'b1;
        mem_addr = axi_rmem_addr;
        if (MemRowsInDw > 1) mem_row_sel = '0;
        mem_sub_addr = axi_rmem_sub_addr;
        addr_out_of_range = axi_raddr_out_of_range;
      end
    endcase
  end

  always_comb begin : i_mem_resp_sel
    rd_resp_vld = 1'b0;
    axi2reg_wresp_vld = '0;
    axi2reg_rresp_vld = '0;
    unique case (resp_sel_q)
      2'b00, 2'b01:  // rd_row
      rd_resp_vld = mem_res_vld_q;
      2'b10:  // axi write
      axi2reg_wresp_vld = mem_res_vld_q;
      default: // 2'b11 axi read
      axi2reg_rresp_vld = mem_res_vld_q;
    endcase
  end

  if (OUTP_SHIELD) begin : gen_sh
    always_ff @(posedge i_clk, negedge i_rst_n) begin : shield
      if (i_rst_n == 1'b0) begin
        resp_sel_q <= '0;
        mem_res_vld_q <= '0;
        mem_rdata_q <= '0;
        mem_sub_addr_q <= '0;
        mem_res_sub_addr_q <= '0;
        if (MemRowsInDw > 1) mem_res_row_sel_q <= '0;
        resp_addr_out_of_range_q <= '0;
      end else begin
        if (mem_arb_vld == 1'b1) begin
          resp_sel_q <= resp_sel;
          mem_sub_addr_q <= mem_sub_addr;
          if (MemRowsInDw > 1)mem_res_row_sel_q <= mem_res_row_sel;
        end
        if (mem_res_vld) begin
          mem_rdata_q <= mem_rdata;
          mem_res_sub_addr_q <= mem_res_sub_addr;
          resp_addr_out_of_range_q <= resp_addr_out_of_range;
        end
        if (mem_res_vld ^ mem_res_vld_q) begin
          mem_res_vld_q <= mem_res_vld;
        end
      end
    end
  end else begin : gen_dir
    assign resp_sel_q = resp_sel;
    assign resp_addr_out_of_range_q = resp_addr_out_of_range;
    assign mem_res_vld_q = mem_res_vld;
    assign mem_rdata_q = mem_rdata;
    assign mem_sub_addr_q = mem_sub_addr;
    assign mem_res_sub_addr_q = mem_res_sub_addr;
    if (MemRowsInDw > 1)
      assign mem_res_row_sel_q = mem_res_row_sel;
  end

  // assign to responses:
  if (MemRowsInDw > 1) begin : gen_rsp_data
    assign rd_resp_data = '0 | (mem_rdata_q >> (MEM_WIDTH * mem_res_row_sel_q));
  end else begin : gen_rsp_data
    assign rd_resp_data = mem_rdata_q;
  end

  //pragma translate_off
`ifdef ASSERTIONS_ON
  property mem_rdata_not_all_x;
    @(posedge i_clk)  // mask i_clk with valid to minimize simulation time impact
    // disable when: in reset, when there has not been a memory access, and when access was a write
    disable iff (!i_rst_n) (mem_res_vld_q && (~resp_addr_out_of_range_q) && (resp_sel_q != 2'b10)) |-> $countbits(
        rd_resp_data, 'x, 'z
    ) != MEM_WIDTH;
  endproperty

  chk_mem_rdata_not_all_x :
  assert property (mem_rdata_not_all_x)
  else $warning("ATTENTION!!! CMD Block DescMem: Reading all X's!!!");
`endif
  //pragma translate_on

  if (TotMemWidth - DW <= 0) begin  : gen_no_shift // no shift needed, mem is smaller then data width
    assign axi2reg_rresp_data = '0 | mem_rdata_q;
    assign mem_wdata = axi2reg_wdata[TotMemWidth-1:0];
    assign mem_wbyte_en = axi2reg_wstrb[$bits(mem_wbyte_en)-1:0];
  end else begin : gen_shift // shift based on sub address
    assign axi2reg_rresp_data = '0 | (mem_rdata_q >> (DW * mem_res_sub_addr_q[DwSelBits+DwSelLsb-1:DwSelLsb]));

    // replicate wdata, and shift byte_en:
    assign mem_wbyte_en = '0 | (axi2reg_wstrb << (((DW+7)/8) * mem_sub_addr_q[DwSelBits+DwSelLsb-1:DwSelLsb]));
    for (genvar i = 0; i < TotMemWidth; i += DW) begin : gen_byte_assign
      if (i > (TotMemWidth - DW)) begin : gen_strb // last one
        assign mem_wdata[TotMemWidth-1:i] = axi2reg_wdata;
      end else begin : gen_strb
        assign mem_wdata[i+DW-1:i] = axi2reg_wdata;
      end
    end
  end

  // actuall memory:
  if (USE_MACRO == 0) begin : gen_flop
    wire i_clk_rows;
    // only flops for now:
    logic [TotMemDepth-1:0] row_en;  // one hot
    logic [TotMemDepth-1:0][TotMemWidth-1:0] reg_out;
    logic [TotMemDepth-1:0][TotMemWidth-1:0] reg_out_masked;

    assign mem_res_sub_addr = mem_sub_addr;
    assign mem_res_vld = mem_arb_vld;
    if (MemRowsInDw > 1)
      assign mem_res_row_sel = mem_row_sel;
    assign resp_addr_out_of_range = addr_out_of_range;
    assign resp_sel = dat_sel;

    if (GENERAL_CLOCK_GATE == 0) begin : gen_clk_passthough
      assign i_clk_rows = i_clk;
    end else begin : gen_clk_gate
      axe_tcl_clk_gating i_cg (
        .i_clk(i_clk),
        .i_en(mem_arb_vld),
        .i_test_en(scan_mode),
        .o_clk(i_clk_rows)
      );
    end

    for (genvar row = 0; row < TotMemDepth; row++) begin : gen_storage
      cmdblock_reg #(
        .REG_W(TotMemWidth)
      ) i_row (
        .i_clk(i_clk_rows),

        .en(row_en[row] & ~mem_we_n),
        .byte_en(mem_wbyte_en),
        .d(mem_wdata),
        .q(reg_out[row])
      );

      if (row > 0) begin : gen_row_masked
        assign reg_out_masked[row] = {TotMemWidth{row_en[row]}} & reg_out[row] | reg_out_masked[row-1];
      end else begin : gen_row
        assign reg_out_masked[row] = {TotMemWidth{row_en[row]}} & reg_out[row];
      end
    end
    assign mem_rdata = reg_out_masked[TotMemDepth-1];

    // one hot encoding for the row enable:
    always_comb begin
      for (int row = 0; row < TotMemDepth; row++) begin
        // one hot encoding:
        if (mem_addr == row) begin
          row_en[row] = mem_arb_vld & ~addr_out_of_range;
        end else begin
          row_en[row] = 1'b0;
        end
      end
    end

    logic not_connected2;
    assign not_connected2 = |i_sram_impl; // ASO-UNUSED_VARIABLE: sram_impl not used in case of flop array
  end else begin : gen_ram
    logic scan_mode_nc;
    always_comb scan_mode_nc = scan_mode; // ASO-UNUSED_VARIABLE: scan mode not required in case macro is used
    // as macro adds a default cycle latency the response should also be delayed:
    always_ff @(posedge i_clk, negedge i_rst_n) begin : i_mem_info_reg
      if (i_rst_n == 1'b0) begin
        mem_res_sub_addr <= '0;
        mem_res_vld <= '0;
        if (MemRowsInDw > 1) mem_res_row_sel <= '0;
        resp_sel <= '0;
        resp_addr_out_of_range <= '0;
      end else begin
        if (mem_arb_vld | mem_res_vld) begin
          mem_res_sub_addr <= mem_sub_addr;
          mem_res_vld <= mem_arb_vld;
          if (MemRowsInDw > 1) mem_res_row_sel <= mem_row_sel;
          resp_sel <= dat_sel;
          resp_addr_out_of_range <= addr_out_of_range;
        end
      end
    end

    // use tc_sram:
    axe_tcl_ram_1rwp #(
      .NumWords(TotMemDepth),
      .DataWidth(TotMemWidth),
      .ByteWidth(8),
      .ReadLatency(1),
      .ImplKey(SRAM_IMPL_KEY),
      .impl_inp_t(ram_impl_inp_t),
      .impl_oup_t(ram_impl_oup_t)
    ) u_tc_ram (
      .i_clk,
      .i_rst_n,
      .i_req(mem_arb_vld & ~addr_out_of_range),
      .i_addr(mem_addr),
      .i_wr_enable(~mem_we_n),
      .i_wr_data(mem_wdata),
      .i_wr_mask(mem_wbyte_en),
      .o_rd_data(mem_rdata),
      .i_impl(i_sram_impl),
      .o_impl(o_sram_impl)
    );
  end

  assign axi2reg_wresp_error = resp_addr_out_of_range_q;
  assign axi2reg_rresp_error = resp_addr_out_of_range_q;

endmodule

`endif  // _CMDBLOCK_DESC_MEM__SV_
