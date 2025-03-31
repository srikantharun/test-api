//
// Copyright (c) 2005-2024 Imperas Software Ltd. All Rights Reserved.
//
// THIS SOFTWARE CONTAINS CONFIDENTIAL INFORMATION AND TRADE SECRETS
// OF IMPERAS SOFTWARE LTD. USE, DISCLOSURE, OR REPRODUCTION IS PROHIBITED
// EXCEPT AS MAY BE PROVIDED FOR IN A WRITTEN AGREEMENT WITH IMPERAS SOFTWARE LTD.
//
//

`ifndef COVER_QUIET
    `define cover_info(s)     $display(s);
`else
    `define cover_info(s)

`endif

// Check that only one COVER_BASE_* is set
`ifdef COVER_BASE_RV32I
    `define COVER_XLEN_32
`else
    `ifdef COVER_BASE_RV32E
        `define COVER_XLEN_32
    `else
        `define COVER_XLEN_64
    `endif
`endif

`ifdef COVER_LEVEL_COMPL_BAS
`endif
`ifdef COVER_LEVEL_COMPL_EXT
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
`endif
`ifdef COVER_LEVEL_DV_UP_BAS
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
  `ifndef COVER_LEVEL_COMPL_EXT
    `define COVER_LEVEL_COMPL_EXT
  `endif
`endif
`ifdef COVER_LEVEL_DV_UP_EXT
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
  `ifndef COVER_LEVEL_COMPL_EXT
    `define COVER_LEVEL_COMPL_EXT
  `endif
  `ifndef COVER_LEVEL_DV_UP_BAS
    `define COVER_LEVEL_DV_UP_BAS
  `endif
`endif
`ifdef COVER_LEVEL_DV_PR_BAS
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
  `ifndef COVER_LEVEL_COMPL_EXT
    `define COVER_LEVEL_COMPL_EXT
  `endif
  `ifndef COVER_LEVEL_DV_UP_BAS
    `define COVER_LEVEL_DV_UP_BAS
  `endif
  `ifndef COVER_LEVEL_DV_UP_EXT
    `define COVER_LEVEL_DV_UP_EXT
  `endif
`endif
`ifdef COVER_LEVEL_DV_PR_EXT
  `ifndef COVER_LEVEL_COMPL_BAS
    `define COVER_LEVEL_COMPL_BAS
  `endif
  `ifndef COVER_LEVEL_COMPL_EXT
    `define COVER_LEVEL_COMPL_EXT
  `endif
  `ifndef COVER_LEVEL_DV_UP_BAS
    `define COVER_LEVEL_DV_UP_BAS
  `endif
  `ifndef COVER_LEVEL_DV_UP_EXT
    `define COVER_LEVEL_DV_UP_EXT
  `endif
  `ifndef COVER_LEVEL_DV_PR_BAS
    `define COVER_LEVEL_DV_PR_BAS
  `endif
`endif

`ifdef COVER_LEVEL_COMPL_BAS
    `define COVER_TYPE_ASM_COUNT
    `define COVER_TYPE_ASSIGNMENTS
    `define COVER_TYPE_CSR_VALUE
    `define COVER_TYPE_FRM
    `define COVER_TYPE_SIGNS
    `define COVER_TYPE_VALUES
    `define COVER_TYPE_ILLEGAL_INST
`endif
`ifdef COVER_LEVEL_COMPL_EXT
    `define COVER_TYPE_EQUAL
    `define COVER_TYPE_FAULTS
    `define COVER_TYPE_MAXVALS
    `define COVER_TYPE_REG_COMPARE
    `define COVER_TYPE_TOGGLE
    `define COVER_TYPE_VECTOR
`endif
`ifdef COVER_LEVEL_DV_UP_BAS
    `define COVER_TYPE_CROSS_VALUES
    `define COVER_TYPE_CSR
    `define COVER_TYPE_METRIC
    `define COVER_TYPE_FPVALUES
    `define COVER_TYPE_HAZARD
`endif
`ifdef COVER_LEVEL_DV_UP_EXT
`endif
`ifdef COVER_LEVEL_DV_PR_BAS
`endif
`ifdef COVER_LEVEL_DV_PR_EXT
`endif

`define SAMPLE_AFTER 0
`define SAMPLE_BEFORE 1

`define SAMPLE_CURRENT 0
`define SAMPLE_PREV 1

`define MCAUSE_ILLEGAL_INST 2

`define NUM_RVVI_DATA 5

`ifdef COVER_XLEN_32
    `define XLEN_INT int
    `define XLEN_UINT int unsigned
`else
    `define XLEN_INT longint
    `define XLEN_UINT longint unsigned
`endif


`ifdef COVER_RV32V
    `define COVER_RV32VB
    `define COVER_RV32VX
    `define COVER_RV32VF
    `define COVER_RV32VI
    `define COVER_RV32VM
    `define COVER_RV32VP
    `define COVER_RV32VR
`endif

`ifdef COVER_RV64V
    `define COVER_RV64VB
    `define COVER_RV64VX
    `define COVER_RV64VF
    `define COVER_RV64VI
    `define COVER_RV64VM
    `define COVER_RV64VP
    `define COVER_RV64VR
`endif

`ifdef COVER_RV32M
    `define COVER_MUL
`endif

`ifdef COVER_RV32ZMMUL
    `define COVER_HAS_MUL
`endif


typedef struct {
    string key;
    string val;
} ops_t;

typedef enum {
    x0,
    x1,
    x2,
    x3,
    x4,
    x5,
    x6,
    x7,
    x8,
    x9,
    x10,
    x11,
    x12,
    x13,
    x14,
    x15
`ifndef COVER_BASE_RV32E
    ,
    x16,
    x17,
    x18,
    x19,
    x20,
    x21,
    x22,
    x23,
    x24,
    x25,
    x26,
    x27,
    x28,
    x29,
    x30,
    x31
`endif
} gpr_name_t;

const gpr_name_t gpr_regs_reduced[] = { x8, x9, x10, x11, x12, x13, x14, x15 };

const gpr_name_t gpr_regs_no_x0[] = { x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31 };

typedef enum {
    f0,
    f1,
    f2,
    f3,
    f4,
    f5,
    f6,
    f7,
    f8,
    f9,
    f10,
    f11,
    f12,
    f13,
    f14,
    f15,
    f16,
    f17,
    f18,
    f19,
    f20,
    f21,
    f22,
    f23,
    f24,
    f25,
    f26,
    f27,
    f28,
    f29,
    f30,
    f31
} fpr_name_t;

const fpr_name_t fpr_regs_reduced[] = { f8, f9, f10, f11, f12, f13, f14, f15 };

`define VECTOR_REG_EMUL1 \
    v0, \
    v1, \
    v2, \
    v3, \
    v4, \
    v5, \
    v6, \
    v7, \
    v8, \
    v9, \
    v10, \
    v11, \
    v12, \
    v13, \
    v14, \
    v15, \
    v16, \
    v17, \
    v18, \
    v19, \
    v20, \
    v21, \
    v22, \
    v23, \
    v24, \
    v25, \
    v26, \
    v27, \
    v28, \
    v29, \
    v30, \
    v31 \

`define VECTOR_REG_EMUL2 \
    v0_v1, \
    v2_v3, \
    v4_v5, \
    v6_v7, \
    v8_v9, \
    v10_v11, \
    v12_v13, \
    v14_v15, \
    v16_v17, \
    v18_v19, \
    v20_v21, \
    v22_v23, \
    v24_v25, \
    v26_v27, \
    v28_v29, \
    v30_v31 \

`define VECTOR_REG_EMUL4 \
    v0_v3, \
    v4_v7, \
    v8_v11, \
    v12_v15, \
    v16_v19, \
    v20_v23, \
    v24_v27, \
    v28_v31 \

`define VECTOR_REG_EMUL8 \
    v0_v7, \
    v8_v15, \
    v16_v23, \
    v24_v31 \


typedef enum {
    `VECTOR_REG_EMUL1,
    `VECTOR_REG_EMUL2,
    `VECTOR_REG_EMUL4,
    `VECTOR_REG_EMUL8
} vdr_name_t;


const vdr_name_t vdr_regs_all[] = {`VECTOR_REG_EMUL1, `VECTOR_REG_EMUL2, `VECTOR_REG_EMUL4, `VECTOR_REG_EMUL8};

const vdr_name_t vdr_regs_nf1[] = {`VECTOR_REG_EMUL1};
const vdr_name_t vdr_regs_nf2[] = {`VECTOR_REG_EMUL2};
const vdr_name_t vdr_regs_nf4[] = {`VECTOR_REG_EMUL4};
const vdr_name_t vdr_regs_nf8[] = {`VECTOR_REG_EMUL8};

const vdr_name_t vdr_regs_no_nf1[] = {`VECTOR_REG_EMUL2,`VECTOR_REG_EMUL4,`VECTOR_REG_EMUL8};
const vdr_name_t vdr_regs_no_nf1_nf2[] = {`VECTOR_REG_EMUL4,`VECTOR_REG_EMUL8};
const vdr_name_t vdr_regs_no_nf4_nf8[] = {`VECTOR_REG_EMUL1, `VECTOR_REG_EMUL2};
const vdr_name_t vdr_regs_no_nf8[] = {`VECTOR_REG_EMUL1, `VECTOR_REG_EMUL2, `VECTOR_REG_EMUL4};


function int get_gpr_num(string key);
    case(key)
        "x0": return 0;
        "zero": return 0;
        "x1": return 1;
        "ra": return 1;
        "x2": return 2;
        "sp": return 2;
        "x3": return 3;
        "gp": return 3;
        "x4": return 4;
        "tp": return 4;
        "x5": return 5;
        "t0": return 5;
        "x6": return 6;
        "t1": return 6;
        "x7": return 7;
        "t2": return 7;
        "x8": return 8;
        "s0": return 8;
        "x9": return 9;
        "s1": return 9;
        "x10": return 10;
        "a0": return 10;
        "x11": return 11;
        "a1": return 11;
        "x12": return 12;
        "a2": return 12;
        "x13": return 13;
        "a3": return 13;
        "x14": return 14;
        "a4": return 14;
        "x15": return 15;
        "a5": return 15;
        "x16": return 16;
        "a6": return 16;
        "x17": return 17;
        "a7": return 17;
        "x18": return 18;
        "s2": return 18;
        "x19": return 19;
        "s3": return 19;
        "x20": return 20;
        "s4": return 20;
        "x21": return 21;
        "s5": return 21;
        "x22": return 22;
        "s6": return 22;
        "x23": return 23;
        "s7": return 23;
        "x24": return 24;
        "s8": return 24;
        "x25": return 25;
        "s9": return 25;
        "x26": return 26;
        "s10": return 26;
        "x27": return 27;
        "s11": return 27;
        "x28": return 28;
        "t3": return 28;
        "x29": return 29;
        "t4": return 29;
        "x30": return 30;
        "t5": return 30;
        "x31": return 31;
        "t6": return 31;
    endcase
    return -1;
endfunction



function int get_fpr_num(string key);
    $display("num fpr key = %0s", key);
    case(key)
        // Floating-point registers f0-f31
        "f0", "ft0": return 0;
        "f1", "ft1": return 1;
        "f2", "ft2": return 2;
        "f3", "ft3": return 3;
        "f4", "ft4": return 4;
        "f5", "ft5": return 5;
        "f6", "ft6": return 6;
        "f7", "ft7": return 7;
        "f8", "fs0": return 8;
        "f9", "fs1": return 9;
        "f10", "fa0": return 10;
        "f11", "fa1": return 11;
        "f12", "fa2": return 12;
        "f13", "fa3": return 13;
        "f14", "fa4": return 14;
        "f15", "fa5": return 15;
        "f16", "fa6": return 16;
        "f17", "fa7": return 17;
        "f18", "fs2": return 18;
        "f19", "fs3": return 19;
        "f20", "fs4": return 20;
        "f21", "fs5": return 21;
        "f22", "fs6": return 22;
        "f23", "fs7": return 23;
        "f24", "fs8": return 24;
        "f25", "fs9": return 25;
        "f26", "fs10": return 26;
        "f27", "fs11": return 27;
        "f28", "ft8": return 28;
        "f29", "ft9": return 29;
        "f30", "ft10": return 30;
        "f31", "ft11": return 31;
    endcase
    return -1;
endfunction

function int get_vdr_num(string key);
    $display("num vdr key = %0s", key);
    case(key)
        "v0": return 0;
        "v1": return 1;
        "v2": return 2;
        "v3": return 3;
        "v4": return 4;
        "v5": return 5;
        "v6": return 6;
        "v7": return 7;
        "v8": return 8;
        "v9": return 9;
        "v10": return 10;
        "v11": return 11;
        "v12": return 12;
        "v13": return 13;
        "v14": return 14;
        "v15": return 15;
        "v16": return 16;
        "v17": return 17;
        "v18": return 18;
        "v19": return 19;
        "v20": return 20;
        "v21": return 21;
        "v22": return 22;
        "v23": return 23;
        "v24": return 24;
        "v25": return 25;
        "v26": return 26;
        "v27": return 27;
        "v28": return 28;
        "v29": return 29;
        "v30": return 30;
        "v31": return 31;
    endcase
    return -1;
endfunction



typedef enum {
    dyn,
    rdn,
    rmm,
    rne,
    rtz,
    rup
} frm_name_t;

function frm_name_t get_frm(string s);
    case (s)
        "rdn": return rdn;
        "rmm": return rmm;
        "rne": return rne;
        "rtz": return rtz;
        "rup": return rup;
        default: return dyn;
    endcase
endfunction
