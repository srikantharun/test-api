// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: CVA6V core settings
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

//-----------------------------------------------------------------------------
// Processor feature configuration
//-----------------------------------------------------------------------------

// XLEN
parameter int XLEN = 64;

// Starting physical address of the program, for Page Table List
bit [XLEN-1:0] start_pa = 'h20_0000_0000;

// Parameter for SATP mode
parameter satp_mode_t SATP_MODE = SV39;

// Supported Privileged mode
privileged_mode_t supported_privileged_mode[] = {MACHINE_MODE, SUPERVISOR_MODE, USER_MODE};

// Unsupported instructions
// keep this list as real unsupported instr by design and not by TB
riscv_instr_name_t unsupported_instr[] = {  };

// Supported by design but currently has TB limitation when it comes to checks
riscv_instr_name_t tb_avoided_instr[] = {
                                         // indexed unordered vector load and stores
                                         VLUXEI_V, VSUXEI_V, VLUXSEGEI_V, VSUXSEGEI_V
                                        };

// ISA supported by the processor
riscv_instr_group_t supported_isa[$] = {RV32I, RV32M, RV64I, RV64M, RV32C, RV64C, RV32A, RV64A,
                                        RV32F, RV64F, RVV, ZFH};
// Interrupt mode support
mtvec_mode_t supported_interrupt_mode[$] = {DIRECT, VECTORED};

// The number of interrupt vectors to be generated, only used if VECTORED interrupt mode is
// supported
int max_interrupt_vector_num = 16;

// Physical memory protection support
// Disabled for the moment. Generates tests that cannot be
// compiled if enabled.
bit support_pmp = 1'b0;

// Enhanced physical memory protection support
bit support_epmp = 1'b0;

// Debug mode support
bit support_debug_mode = 1'b1;

// Support delegate trap to user mode
bit support_umode_trap = 1'b0;

// Support sfence.vma instruction
bit support_sfence = 1'b1;

// Support unaligned load/store
bit support_unaligned_load_store = 1'b0;

// GPR setting
parameter int NUM_FLOAT_GPR = 32;
parameter int NUM_GPR = 32;
parameter int NUM_VEC_GPR = 32;

// ----------------------------------------------------------------------------
// Vector extension configuration
// ----------------------------------------------------------------------------

// Vector Register Length
parameter int VLEN = 4096;

// ----------------------------------------------------------------------------
// Multi-harts configuration
// ----------------------------------------------------------------------------

// Number of harts
parameter int NUM_HARTS = 1;

// ----------------------------------------------------------------------------
// Previleged CSR implementation
// ----------------------------------------------------------------------------

// Implemented privileged CSR list
const privileged_reg_t implemented_csr[] = {
    // Floating point CSR, User Mode
    FFLAGS,     // Floating point Flags,                                side-effect free read/writes
    FRM,        // Floating point rounding mode                         side-effect free read/writes
    FCSR,       // Floating point control and status                    side-effect free read/writes
    // Vector CSR, User Mode but needs V extension enabled in MSTATUS
    VSTART,     // Vector start position                                side-effect free read/writes
    VXSAT,      // Fixed point saturate flag                            side-effect free read/writes
    VXRM,       // Fixed point rounding mode                            side-effect free read/writes
    VCSR,       // Vector control and status register                   side-effect free read/writes
    VL,         // Vector length                                        side-effect free read/writes
    VTYPE,      // Vector data type register
    VLENB,       // VLEN/8 (vector register length in bytes)            side-effect free read/writes
    // Debug Mode CSR
    DCSR,       // Debug Mode CSR
    DPC,        // Debug Program Counter                                side-effect free read/writes
    DSCRATCH0,  // Debug Scratch0                                       side-effect free read/writes
    DSCRATCH1,  // Debug Scratch1                                       side-effect free read/writes
    // Supervisor mode CSR
    SSTATUS,    // Supervisor status
    SIE,        // Supervisor interrupt-enable register                 side-effect free read/writes
    SIP,        // Supervisor interrupt pending
    STVEC,      // Supervisor trap-handler base address
    SCOUNTEREN, // Supervisor counter enable                            side-effect free read/writes
    SSCRATCH,   // Scratch register for supervisor trap handlers        side-effect free read/writes
    SEPC,       // Supervisor exception program counter
    SCAUSE,     // Supervisor trap cause                                side-effect free read/writes
    STVAL,      // Supervisor bad address or instruction                side-effect free read/writes ?
    SATP,       // Supervisor address translation and protection
    SENVCFG,    // Supervisor env cfg
    // Machine mode mode CSR
    MSTATUS,    // Machine status
    MISA,       // ISA and extensions                                   side-effect free read/writes
    MEDELEG,    // Machine exception delegation register
    MIDELEG,    // Machine interrupt delegation register                side-effect free read/writes
    MIE,        // Machine interrupt-enable register                    side-effect free read/writes
    MTVEC,      // Machine trap-handler base address
    MCOUNTEREN, // Machine counter enable                               side-effect free read/writes
    MSCRATCH,   // Scratch register for machine trap handlers           side-effect free read/writes
    MEPC,       // Machine exception program counter
    MCAUSE,     // Machine trap cause
    MTVAL,      // Machine bad address or instruction
    MIP,        // Machine interrupt pending
    MENVCFG,    // Machine Env Config                                   side-effect free read/writes
    MVENDORID,  // Vendor ID                                            side-effect free read/writes
    MARCHID,    // Architecture ID                                      side-effect free read/writes
    MIMPID,     // Implementation ID                                    side-effect free read/writes
    MHARTID,    // Hardware thread ID                                   side-effect free read/writes
    MCONFIGPTR, // Machine Config Pointer                               side-effect free read/writes
    MCOUNTINHIBIT, // Machine Count Inhibit                             side-effect free read/writes
    MCYCLE,        // Machine Cycle                                     side-effect free read/writes
    MINSTRET,      // Machine instructions retired counter              side-effect free read/writes
    MHPMEVENT3,  // Machine High Performance Monitor Event              side-effect free read/writes
    MHPMEVENT4,
    MHPMEVENT5,
    MHPMEVENT6,
    MHPMEVENT7,
    MHPMEVENT8,
    MHPMEVENT9,
    MHPMEVENT10,
    MHPMEVENT11,
    MHPMEVENT12,
    MHPMEVENT13,
    MHPMEVENT14,
    MHPMEVENT15,
    MHPMEVENT16,
    MHPMEVENT17,
    MHPMEVENT18,
    MHPMEVENT19,
    MHPMEVENT20,
    MHPMEVENT21,
    MHPMEVENT22,
    MHPMEVENT23,
    MHPMEVENT24,
    MHPMEVENT25,
    MHPMEVENT26,
    MHPMEVENT27,
    MHPMEVENT28,
    MHPMEVENT29,
    MHPMEVENT30,
    MHPMEVENT31,
    MHPMCOUNTER3,  // Machine High Performance Monitor Counter          side-effect free read/writes
    MHPMCOUNTER4,
    MHPMCOUNTER5,
    MHPMCOUNTER6,
    MHPMCOUNTER7,
    MHPMCOUNTER8,
    MHPMCOUNTER9,
    MHPMCOUNTER10,
    MHPMCOUNTER11,
    MHPMCOUNTER12,
    MHPMCOUNTER13,
    MHPMCOUNTER14,
    MHPMCOUNTER15,
    MHPMCOUNTER16,
    MHPMCOUNTER17,
    MHPMCOUNTER18,
    MHPMCOUNTER19,
    MHPMCOUNTER20,
    MHPMCOUNTER21,
    MHPMCOUNTER22,
    MHPMCOUNTER23,
    MHPMCOUNTER24,
    MHPMCOUNTER25,
    MHPMCOUNTER26,
    MHPMCOUNTER27,
    MHPMCOUNTER28,
    MHPMCOUNTER29,
    MHPMCOUNTER30,
    MHPMCOUNTER31,

    // Supervisor Mode since Supervisor mode is implemented (specified in MCOUNTEREN section of priv spec)
    CYCLE,           // User mode cycle                                 side-effect free read/writes
    INSTRET,         // User mode intruction retired counter            side-effect free read/writes
    HPMCOUNTER3,   // User mode high performance monitor high           side-effect free read/writes
    HPMCOUNTER4,
    HPMCOUNTER5,
    HPMCOUNTER6,
    HPMCOUNTER7,
    HPMCOUNTER8,
    HPMCOUNTER9,
    HPMCOUNTER10,
    HPMCOUNTER11,
    HPMCOUNTER12,
    HPMCOUNTER13,
    HPMCOUNTER14,
    HPMCOUNTER15,
    HPMCOUNTER16,
    HPMCOUNTER17,
    HPMCOUNTER18,
    HPMCOUNTER19,
    HPMCOUNTER20,
    HPMCOUNTER21,
    HPMCOUNTER22,
    HPMCOUNTER23,
    HPMCOUNTER24,
    HPMCOUNTER25,
    HPMCOUNTER26,
    HPMCOUNTER27,
    HPMCOUNTER28,
    HPMCOUNTER29,
    HPMCOUNTER30,
    HPMCOUNTER31,

    // Custom CSR, Machine Mode
    ICACHE,  // Instruction Cache                                       side-effect free read/writes
    DCACHE,  // Data Cache                                               side-effect free read/writes
    PERF_EVENT_PCSEL, // PC / granularity for perf events
    PERF_EVENT_EVSEL // Event selector
};

// Unimplemented privileged CSR list
const privileged_reg_t unimplemented_csr[] = {
    TSELECT,
    TDATA1,
    TDATA2,
    TDATA3,
    VSSTATUS,
    VSIE,
    VSIP,
    VSTVEC,
    VSSCRATCH,
    VSEPC,
    VSCAUSE,
    VSTVAL,
    VSATP,
    HSTATUS,
    HEDELEG,
    HIDELEG,
    HIE,
    HIP,
    HVIP,
    HCOUNTEREN,
    HTVAL,
    HTINST,
    HGEIE,
    HGEIP,
    HENVCFG,
    HENVCFGH,
    HGATP,
    MHPMCOUNTER3H,  // Machine High Performance Monitor Counter
    MHPMCOUNTER4H,
    MHPMCOUNTER5H,
    MHPMCOUNTER6H,
    MHPMCOUNTER7H,
    MHPMCOUNTER8H,
    MHPMCOUNTER9H,
    MHPMCOUNTER10H,
    MHPMCOUNTER11H,
    MHPMCOUNTER12H,
    MHPMCOUNTER13H,
    MHPMCOUNTER14H,
    MHPMCOUNTER15H,
    MHPMCOUNTER16H,
    MHPMCOUNTER17H,
    MHPMCOUNTER18H,
    MHPMCOUNTER19H,
    MHPMCOUNTER20H,
    MHPMCOUNTER21H,
    MHPMCOUNTER22H,
    MHPMCOUNTER23H,
    MHPMCOUNTER24H,
    MHPMCOUNTER25H,
    MHPMCOUNTER26H,
    MHPMCOUNTER27H,
    MHPMCOUNTER28H,
    MHPMCOUNTER29H,
    MHPMCOUNTER30H,
    MHPMCOUNTER31H,
    HPMCOUNTER3H,  //  High Performance Monitor Counter
    HPMCOUNTER4H,
    HPMCOUNTER5H,
    HPMCOUNTER6H,
    HPMCOUNTER7H,
    HPMCOUNTER8H,
    HPMCOUNTER9H,
    HPMCOUNTER10H,
    HPMCOUNTER11H,
    HPMCOUNTER12H,
    HPMCOUNTER13H,
    HPMCOUNTER14H,
    HPMCOUNTER15H,
    HPMCOUNTER16H,
    HPMCOUNTER17H,
    HPMCOUNTER18H,
    HPMCOUNTER19H,
    HPMCOUNTER20H,
    HPMCOUNTER21H,
    HPMCOUNTER22H,
    HPMCOUNTER23H,
    HPMCOUNTER24H,
    HPMCOUNTER25H,
    HPMCOUNTER26H,
    HPMCOUNTER27H,
    HPMCOUNTER28H,
    HPMCOUNTER29H,
    HPMCOUNTER30H,
    HPMCOUNTER31H
};

// Implemented Debug CSR list
const privileged_reg_t implemented_d_csr[] = {
    DCSR,       // Debug Mode CSR
    DPC,        // Debug Program Counter
    DSCRATCH0,  // Debug Scratch0
    DSCRATCH1  // Debug Scratch1
};

const privileged_reg_t implemented_s_csr[] = {
    // Floating point CSR, User Mode
    FFLAGS,     // Floating point Flags,                                side-effect free read/writes
    FRM,        // Floating point rounding mode                         side-effect free read/writes
    FCSR,       // Floating point control and status                    side-effect free read/writes
    // Vector CSR, User Mode but needs V extension enabled in MSTATUS
    VSTART,     // Vector start position                                side-effect free read/writes
    VXSAT,      // Fixed point saturate flag                            side-effect free read/writes
    VXRM,       // Fixed point rounding mode                            side-effect free read/writes
    VCSR,       // Vector control and status register                   side-effect free read/writes
    VL,         // Vector length                                        side-effect free read/writes
    VTYPE,      // Vector data type register
    VLENB,       // VLEN/8 (vector register length in bytes)            side-effect free read/writes
    // Supervisor mode CSR
    SSTATUS,    // Supervisor status
    SIE,        // Supervisor interrupt-enable register                 side-effect free read/writes
    SIP,        // Supervisor interrupt pending
    STVEC,      // Supervisor trap-handler base address
    SCOUNTEREN, // Supervisor counter enable                            side-effect free read/writes
    SSCRATCH,   // Scratch register for supervisor trap handlers        side-effect free read/writes
    SEPC,       // Supervisor exception program counter
    SCAUSE,     // Supervisor trap cause                                side-effect free read/writes
    STVAL,      // Supervisor bad address or instruction                side-effect free read/writes ?
    SATP,       // Supervisor address translation and protection
    SENVCFG ,    // Supervisor env cfg
    CYCLE,         // Supervisor mode cycle                           side-effect free read/writes
    INSTRET,        // Supervisor mode intruction retired counter      side-effect free read/writes
    HPMCOUNTER3,   // User mode high performance monitor high           side-effect free read/writes
    HPMCOUNTER4,
    HPMCOUNTER5,
    HPMCOUNTER6,
    HPMCOUNTER7,
    HPMCOUNTER8,
    HPMCOUNTER9,
    HPMCOUNTER10,
    HPMCOUNTER11,
    HPMCOUNTER12,
    HPMCOUNTER13,
    HPMCOUNTER14,
    HPMCOUNTER15,
    HPMCOUNTER16,
    HPMCOUNTER17,
    HPMCOUNTER18,
    HPMCOUNTER19,
    HPMCOUNTER20,
    HPMCOUNTER21,
    HPMCOUNTER22,
    HPMCOUNTER23,
    HPMCOUNTER24,
    HPMCOUNTER25,
    HPMCOUNTER26,
    HPMCOUNTER27,
    HPMCOUNTER28,
    HPMCOUNTER29,
    HPMCOUNTER30,
    HPMCOUNTER31
};

const privileged_reg_t implemented_u_csr[] = {
    // Floating point CSR, User Mode
    FFLAGS,     // Floating point Flags,                                side-effect free read/writes
    FRM,        // Floating point rounding mode                         side-effect free read/writes
    FCSR,       // Floating point control and status                    side-effect free read/writes
    // Vector CSR, User Mode but needs V extension enabled in MSTATUS
    VSTART,     // Vector start position                                side-effect free read/writes
    VXSAT,      // Fixed point saturate flag                            side-effect free read/writes
    VXRM,       // Fixed point rounding mode                            side-effect free read/writes
    VCSR,       // Vector control and status register                   side-effect free read/writes
    VL,         // Vector length                                        side-effect free read/writes
    VTYPE,      // Vector data type register
    VLENB       // VLEN/8 (vector register length in bytes)            side-effect free read/writes
};

const privileged_reg_t implemented_v_csr[] = {
    // Vector CSR, User Mode but needs V extension enabled in MSTATUS
    VSTART,     // Vector start position                                side-effect free read/writes
    VXSAT,      // Fixed point saturate flag                            side-effect free read/writes
    VXRM,       // Fixed point rounding mode                            side-effect free read/writes
    VCSR,       // Vector control and status register                   side-effect free read/writes
    VL,         // Vector length                                        side-effect free read/writes
    VTYPE,      // Vector data type register
    VLENB       // VLEN/8 (vector register length in bytes)            side-effect free read/writes
};

const privileged_reg_t implemented_f_csr[] = {
    FFLAGS,     // Floating point Flags,                                side-effect free read/writes
    FRM,        // Floating point rounding mode                         side-effect free read/writes
    FCSR       // Floating point control and status                    side-effect free read/writes
};

// CSR's that you do not want to access at all. Write will mess up sim/flow, read is unpredictable

// Implementation-specific custom CSRs
const privileged_reg_t custom_csr[] = {
    ICACHE,
    DCACHE,
    PERF_EVENT_PCSEL,
    PERF_EVENT_EVSEL
};

// Implemented counter CSR list
const privileged_reg_t implemented_counter_csr[] = {
    MCYCLE,        // Machine Cycle                                     side-effect free read/writes
    MINSTRET,      // Machine instructions retired counter              side-effect free read/writes
    MHPMCOUNTER3,  // Machine High Performance Monitor Counter          side-effect free read/writes
    MHPMCOUNTER4,
    MHPMCOUNTER5,
    MHPMCOUNTER6,
    MHPMCOUNTER7,
    MHPMCOUNTER8,
    MHPMCOUNTER9,
    MHPMCOUNTER10,
    MHPMCOUNTER11,
    MHPMCOUNTER12,
    MHPMCOUNTER13,
    MHPMCOUNTER14,
    MHPMCOUNTER15,
    MHPMCOUNTER16,
    MHPMCOUNTER17,
    MHPMCOUNTER18,
    MHPMCOUNTER19,
    MHPMCOUNTER20,
    MHPMCOUNTER21,
    MHPMCOUNTER22,
    MHPMCOUNTER23,
    MHPMCOUNTER24,
    MHPMCOUNTER25,
    MHPMCOUNTER26,
    MHPMCOUNTER27,
    MHPMCOUNTER28,
    MHPMCOUNTER29,
    MHPMCOUNTER30,
    MHPMCOUNTER31,

    // Supervisor Mode since Supervisor mode is implemented (specified in MCOUNTEREN section of priv spec)
    CYCLE,           // User mode cycle                                 side-effect free read/writes
    INSTRET,         // User mode intruction retired counter            side-effect free read/writes
    HPMCOUNTER3,   // User mode high performance monitor high           side-effect free read/writes
    HPMCOUNTER4,
    HPMCOUNTER5,
    HPMCOUNTER6,
    HPMCOUNTER7,
    HPMCOUNTER8,
    HPMCOUNTER9,
    HPMCOUNTER10,
    HPMCOUNTER11,
    HPMCOUNTER12,
    HPMCOUNTER13,
    HPMCOUNTER14,
    HPMCOUNTER15,
    HPMCOUNTER16,
    HPMCOUNTER17,
    HPMCOUNTER18,
    HPMCOUNTER19,
    HPMCOUNTER20,
    HPMCOUNTER21,
    HPMCOUNTER22,
    HPMCOUNTER23,
    HPMCOUNTER24,
    HPMCOUNTER25,
    HPMCOUNTER26,
    HPMCOUNTER27,
    HPMCOUNTER28,
    HPMCOUNTER29,
    HPMCOUNTER30,
    HPMCOUNTER31
};

// Implemented counter CSR list
const privileged_reg_t read_only_counter_csr[] = {
    // Supervisor Mode since Supervisor mode is implemented (specified in MCOUNTEREN section of priv spec)
    CYCLE,           // User mode cycle                                 side-effect free read/writes
    INSTRET,         // User mode intruction retired counter            side-effect free read/writes
    HPMCOUNTER3,   // User mode high performance monitor high           side-effect free read/writes
    HPMCOUNTER4,
    HPMCOUNTER5,
    HPMCOUNTER6,
    HPMCOUNTER7,
    HPMCOUNTER8,
    HPMCOUNTER9,
    HPMCOUNTER10,
    HPMCOUNTER11,
    HPMCOUNTER12,
    HPMCOUNTER13,
    HPMCOUNTER14,
    HPMCOUNTER15,
    HPMCOUNTER16,
    HPMCOUNTER17,
    HPMCOUNTER18,
    HPMCOUNTER19,
    HPMCOUNTER20,
    HPMCOUNTER21,
    HPMCOUNTER22,
    HPMCOUNTER23,
    HPMCOUNTER24,
    HPMCOUNTER25,
    HPMCOUNTER26,
    HPMCOUNTER27,
    HPMCOUNTER28,
    HPMCOUNTER29,
    HPMCOUNTER30,
    HPMCOUNTER31
};

// ----------------------------------------------------------------------------
// Supported interrupt/exception setting, used for functional coverage
// ----------------------------------------------------------------------------

const interrupt_cause_t implemented_interrupt[] = {
    S_SOFTWARE_INTR,
    M_SOFTWARE_INTR,
    S_TIMER_INTR,
    M_TIMER_INTR,
    S_EXTERNAL_INTR,
    M_EXTERNAL_INTR
};

const exception_cause_t implemented_exception[] = {
    INSTRUCTION_ACCESS_FAULT,
    ILLEGAL_INSTRUCTION,
    BREAKPOINT,
    LOAD_ADDRESS_MISALIGNED,
    LOAD_ACCESS_FAULT,
    STORE_AMO_ADDRESS_MISALIGNED,
    STORE_AMO_ACCESS_FAULT,
    ECALL_UMODE,
    ECALL_SMODE,
    ECALL_MMODE,
    INSTRUCTION_PAGE_FAULT,
    LOAD_PAGE_FAULT,
    STORE_AMO_PAGE_FAULT
};

// Temporary code to randomly access list of safe CSR's until constraint is implemented for
// each CSR is implemented

// Implemented previlieged CSR list
const privileged_reg_t safe_m_mode_csr[] = {
    // Supervisor mode CSR
    SIE,
    SIP,
    SCOUNTEREN,
    SSCRATCH,
    SEPC,
    SCAUSE,
    STVAL,
    // Machine mode mode CSR
    MEDELEG,
    MCOUNTEREN,
    MSCRATCH,
    MEPC,
    MCAUSE,
    MTVAL,
    MIP,
    MVENDORID,
    MIMPID,
    MHARTID,
    MARCHID,
    MCONFIGPTR,
    // User mode
    FFLAGS,
    //FRM,
    //FCSR
    VSTART,
    VXSAT,
    VXRM,
    VCSR
};

const privileged_reg_t safe_s_mode_csr[] = {
    // Supervisor mode CSR
    SIE,
    SIP,
    SCOUNTEREN,
    SSCRATCH,
    SEPC,
    SCAUSE,
    STVAL,
    // User mode
    FFLAGS,
    //FRM,
    //FCSR
    VSTART,
    VXSAT,
    VXRM,
    VCSR
};

const privileged_reg_t safe_u_mode_csr[] = {
    // User mode
    FFLAGS,
    SSCRATCH,
    //FRM,
    //FCSR
    VSTART,
    VXSAT,
    VXRM,
    VCSR
};
