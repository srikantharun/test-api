// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tasos Psarras <anastasios.psarras@axelera.ai>
// Description: Generic Memory Instantiator
//              For a _desired_ Depth (`DEPTH`) and Data Width (`DATAW`)
//              and a _available macro_ Depth (`MACRO_DEPTH`) and Data Width (`MACRO_DATAW`),
//              it instantiates as many macros as required to extend in Data Width and in Depth.
//              CAUTION! When DEPTH > MACRO_DEPTH, the MACRO_DEPTH must be a power-of-2
//              (unsupported configurations cause run-time assertion failure)

module noc_common_mem_wrap_top #(
    parameter int unsigned DATAW = 1,
    parameter int unsigned DEPTH = 1,
    parameter int unsigned MACRO_DATAW = 0,
    parameter int unsigned MACRO_DEPTH = 0,
    parameter int unsigned ADDRW = $clog2(DEPTH)
) (
    input  wire             Clk,
    input  wire             RstN,
    input  logic            RdEn,
    input  logic[ADDRW-1:0] RdAddr,
    output logic[DATAW-1:0] RdData,
    input  logic            WrEn,
    input  logic[ADDRW-1:0] WrAddr,
    input  logic[DATAW-1:0] WrBitEn,
    input  logic[DATAW-1:0] WrData,
    input  logic            se,
    input  logic            pde,
    output logic            prn,
    input  logic            ret
);
    // -- Memory configuration -- //
    localparam int unsigned MACRO_COUNT = DEPTH / MACRO_DEPTH + (((DEPTH % MACRO_DEPTH) > 0) ? 1 : 0);
    localparam int unsigned MACRO_ADDRW = $clog2(MACRO_DEPTH);
    localparam int unsigned RANK_ADDRW = $clog2(MACRO_COUNT);

    // -- Memory impl pins -- //
    axe_tcl_sram_pkg::impl_inp_t mem_impl_inp;
    axe_tcl_sram_pkg::impl_oup_t mem_impl_out;
    axe_tcl_sram_pkg::impl_inp_t[MACRO_COUNT-1:0] impl_to_mem;
    axe_tcl_sram_pkg::impl_oup_t[MACRO_COUNT-1:0] impl_from_mem;
    // Input & Output -- First & Last in the chain
    assign mem_impl_inp = axe_tcl_sram_pkg::impl_inp_t'{
        ret: ret,
        pde: pde,
        se: se,
        default: '0
    };
    assign prn = mem_impl_out.prn;
    // Intermediate Memory Wiring
    axe_tcl_sram_cfg #(
        .NUM_SRAMS(MACRO_COUNT)
    ) u_sram_cfg_impl (
        .i_s(mem_impl_inp),
        .o_s(mem_impl_out),
        .o_m(impl_to_mem),
        .i_m(impl_from_mem)
    );

    // -- Memory instantiation, wiring & logic -- //
    logic[MACRO_COUNT-1:0] inp_rd_mem_sel;
    logic[MACRO_COUNT-1:0] inp_wr_mem_sel;
    logic[MACRO_COUNT-1:0] inp_rd_en;
    logic[MACRO_COUNT-1:0] inp_wr_en;
    logic[MACRO_COUNT-1:0] out_rd_mem_sel;
    logic[MACRO_COUNT-1:0][DATAW-1:0] out_rd_mem_data;

    assign inp_rd_en = {MACRO_COUNT{RdEn}} & inp_rd_mem_sel;
    assign inp_wr_en = {MACRO_COUNT{WrEn & WrBitEn[0]}} & inp_wr_mem_sel; // assumming ast_wr_bit_en_legal holds!

    if (MACRO_COUNT == 1) begin: g_if_ranks_eq_1
        assign inp_rd_mem_sel = 1'b1;
        assign inp_wr_mem_sel = 1'b1;
        assign out_rd_mem_sel = 1'b1;

        assign RdData = out_rd_mem_data[0];
    end else begin: g_if_ranks_gt_1
        logic[MACRO_COUNT-1:0] inp_rd_mem_sel_r;

        assign inp_rd_mem_sel = 1 << RdAddr[MACRO_ADDRW +: RANK_ADDRW];
        assign inp_wr_mem_sel = 1 << WrAddr[MACRO_ADDRW +: RANK_ADDRW];

        always_ff @(posedge Clk or negedge RstN) begin: ff_rd_mem_sel
            if (!RstN) begin
                inp_rd_mem_sel_r <= '0;
            end else begin
                inp_rd_mem_sel_r <= inp_rd_mem_sel;
            end
        end
        assign out_rd_mem_sel = inp_rd_mem_sel_r;

        axe_ccl_mux_onehot #(
            .DataWidth (DATAW),
            .data_t    (logic[DATAW-1:0]),
            .NumInputs (MACRO_COUNT)
        ) u_mux (
            .i_data   (out_rd_mem_data),
            .i_select (out_rd_mem_sel),
            .o_data   (RdData)
        );
    end

    for (genvar m=0; unsigned'(m)<MACRO_COUNT; m++) begin: g_for_m_mem
        noc_common_mem_wrap_data_ext #(
            .DATAW       (DATAW),
            .MACRO_DATAW (MACRO_DATAW),
            .MACRO_DEPTH (MACRO_DEPTH)
        ) u_mem (
            .Clk        (Clk),
            .RstN       (RstN),
            .RdEn       (inp_rd_en[m]),
            .RdAddr     (RdAddr[0 +: MACRO_ADDRW]),
            .RdData     (out_rd_mem_data[m]),
            .WrEn       (inp_wr_en[m]),
            .WrAddr     (WrAddr[0 +: MACRO_ADDRW]),
            .WrBitEn    (WrBitEn),
            .WrData     (WrData),
            .i_mem_impl (impl_to_mem[m]),
            .o_mem_impl (impl_from_mem[m])
        );
    end

    // -- Assertions -- //
    if ((MACRO_COUNT != 1) && (2**$clog2(MACRO_DEPTH) != MACRO_DEPTH)) $fatal(1, "Invalid configuration. MACRO_DEPTH (%0d) must be a power of 2 for multiple macro instantiation", MACRO_DEPTH);
    ast_rd_addr_within_range: assert property (@(posedge Clk) disable iff(!RstN) RdEn |-> RdAddr < DEPTH) else $fatal(1, "Read address out of range [0, 0x%0x]", DEPTH-1);
    ast_wr_addr_within_range: assert property (@(posedge Clk) disable iff(!RstN) WrEn |-> WrAddr < DEPTH) else $fatal(1, "Write address out of range [0, 0x%0x]", DEPTH-1);
    ast_wr_bit_en_legal: assert property (@(posedge Clk) disable iff(!RstN) WrEn |-> ((&WrBitEn) === 1) || ((|WrBitEn) === 0)) else $fatal(1, "All WrBitEn bits shall have identical values");
endmodule
