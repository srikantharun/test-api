// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tasos Psarras <anastasios.psarras@axelera.ai>
// Description: Generic Parallel Memory Bank Instantiator
//              Instantiates the right number of Macros of Data Width `MACRO_DATAW`
//              in order to implement a memory of _desired_ Data Width `DATAW`

module noc_common_mem_wrap_data_ext #(
    parameter int unsigned DATAW = 1,
    parameter int unsigned MACRO_DATAW = 0,
    parameter int unsigned MACRO_DEPTH = 1,
    parameter int unsigned ADDRW = $clog2(MACRO_DEPTH)
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
    input  axe_tcl_sram_pkg::impl_inp_t i_mem_impl,
    output axe_tcl_sram_pkg::impl_oup_t o_mem_impl
);
    // -- Memory configuration -- //
    localparam int unsigned MACRO_COUNT = DATAW / MACRO_DATAW + (((DATAW % MACRO_DATAW) > 0) ? 1 : 0);
    localparam int unsigned LAST_MACRO_DATAW = DATAW % MACRO_DATAW;

    // -- Memory impl pins -- //
    axe_tcl_sram_pkg::impl_inp_t[MACRO_COUNT-1:0] impl_to_mem;
    axe_tcl_sram_pkg::impl_oup_t[MACRO_COUNT-1:0] impl_from_mem;

    axe_tcl_sram_cfg #(
        .NUM_SRAMS(MACRO_COUNT)
    ) u_sram_cfg_impl (
        .i_s(i_mem_impl),
        .o_s(o_mem_impl),
        .o_m(impl_to_mem),
        .i_m(impl_from_mem)
    );

    // -- Memory instantiation & wiring -- //
    logic[MACRO_DATAW-1:0] wr_data_macro[MACRO_COUNT];
    logic[MACRO_DATAW-1:0] rd_data_macro[MACRO_COUNT];

    for (genvar m=0; unsigned'(m)<MACRO_COUNT; m++) begin: g_for_m_macro
        if ((LAST_MACRO_DATAW > 0) && (m == (MACRO_COUNT-1))) begin: g_last_m_unbalanced
            assign wr_data_macro[m] = { {(MACRO_DATAW-LAST_MACRO_DATAW){1'b0}}, WrData[m*MACRO_DATAW +: LAST_MACRO_DATAW]};
            assign RdData[m*MACRO_DATAW +: LAST_MACRO_DATAW] = rd_data_macro[m][0 +: LAST_MACRO_DATAW];
        end else begin: g_middle_m
            assign wr_data_macro[m] = WrData[m*MACRO_DATAW +: MACRO_DATAW];
            assign RdData[m*MACRO_DATAW +: MACRO_DATAW] = rd_data_macro[m];
        end

        axe_tcl_ram_1rp_1wp #(
            .NumWords   (MACRO_DEPTH),
            .DataWidth  (MACRO_DATAW),
            .ByteWidth  (MACRO_DATAW),
            .FunctionalClkGate (1'b0), // intentionally _not_ using gate
            .ImplKey    ("HS_RVT")
        ) u_tc_ram (
            .i_wr_clk   (Clk),
            .i_wr_rst_n (RstN),
            .i_wr_req   (WrEn),
            .i_wr_addr  (WrAddr),
            .i_wr_data  (wr_data_macro[m]),
            .i_wr_mask  (1'b1),

            .i_rd_clk   (Clk),
            .i_rd_rst_n (RstN),
            .i_rd_req   (RdEn),
            .i_rd_addr  (RdAddr),
            .o_rd_data  (rd_data_macro[m]),

            .i_impl     (impl_to_mem[m]),
            .o_impl     (impl_from_mem[m])
        );
    end

    // -- Assertions -- //
    ast_wr_bit_en_legal: assert property (@(posedge Clk) disable iff(!RstN) WrEn |-> ((&WrBitEn) === 1) || ((|WrBitEn) === 0)) else $fatal(1, "All WrBitEn bits shall have identical values");
endmodule
