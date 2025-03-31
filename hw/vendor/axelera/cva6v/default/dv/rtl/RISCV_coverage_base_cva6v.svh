// Extension of original imperas files : /apps/eda/imperas/20240305/ImpProprietary/source/host/riscvISACOV/source/coverage/RISCV_coverage_base.svh
/**
 * @file RISCV_coverage_cva6v.sv
 * @brief RISCV_coverage class definition and related functions overrrides the Opensource file RISCV_coverage.sv
 *
 * This file contains the definition of the RISCV_coverage class,
 * which is responsible for handling coverage related operations for the RISC-V processor.
 * It includes various coverage modules and extensions, such as RV32I, RV32I_ILLEGAL, and RV32I_IMPTEST.
 * The class also provides functions for loading and processing RISC-V data from a CSV file.
 *
 * @param ILEN   Instruction length in bits
 * @param XLEN   GPR length in bits
 * @param FLEN   FPR length in bits
 * @param VLEN   Vector register size in bits
 * @param NHART  Number of harts reported
 * @param RETIRE Number of instructions that can retire during valid event
 */
class RISCV_coverage_cva6v
#(
    parameter int ILEN   = 32,  // Instruction length in bits
    parameter int XLEN   = 64,  // GPR length in bits
    parameter int FLEN   = 32,  // FPR length in bits
    parameter int VLEN   = 4096, // Vector register size in bits
    parameter int NHART  = 1,   // Number of harts reported
    parameter int RETIRE = 1    // Number of instructions that can retire during valid event
);
    `include "coverage/RISCV_coverage_rvvi.svh"
    `include "RISCV_coverage_csr_cva6v.svh"
    `include "coverage/RISCV_coverage_exceptions.svh"
    `include "coverage/RISCV_coverage_hazards.svh"
    `include "coverage/RISCV_coverage_vectors.svh"

    `ifdef COVER_RV32I_IMPTEST
        `include "coverage/RV32I_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RV32F_IMPTEST
        `include "coverage/RV32F_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RV32C_IMPTEST
        `include "coverage/RV32C_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCF_IMPTEST
        `include "coverage/RV32ZCF_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCMP_IMPTEST
        `include "coverage/RV32ZCMP_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCMT_IMPTEST
        `include "coverage/RV32ZCMT_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RV32VB_IMPTEST
        `include "coverage/RV32VB_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RV32VX_IMPTEST
        `include "coverage/RV32VX_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RVVI_METRICS_IMPTEST
        `include "coverage/RVVI_METRICS_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV32_IMPTEST
        `include "coverage/RSC_MMU_SV32_IMPTEST_coverage.svh"
    `endif
    `ifdef COVER_XPULPV2_IMPTEST
        `include "coverage/XPULPV2_IMPTEST_coverage.svh"
    `endif

    `ifdef COVER_RV32I
        `include "coverage/RV32I_coverage.svh"
    `endif
    `ifdef COVER_RV32I_ILLEGAL
        `include "coverage/RV32I_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32E
        `include "coverage/RV32E_coverage.svh"
    `endif
    `ifdef COVER_RV32E_ILLEGAL
        `include "coverage/RV32E_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32M
        `include "coverage/RV32M_coverage.svh"
    `endif
    `ifdef COVER_RV32M_ILLEGAL
        `include "coverage/RV32M_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZMMUL
        `include "coverage/RV32ZMMUL_coverage.svh"
    `endif
    `ifdef COVER_RV32ZMMUL_ILLEGAL
        `include "coverage/RV32ZMMUL_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32F
        `include "coverage/RV32F_coverage.svh"
    `endif
    `ifdef COVER_RV32F_ILLEGAL
        `include "coverage/RV32F_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZFINX
        `include "coverage/RV32ZFINX_coverage.svh"
    `endif
    `ifdef COVER_RV32ZFINX_ILLEGAL
        `include "coverage/RV32ZFINX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZHINX
        `include "coverage/RV32ZHINX_coverage.svh"
    `endif
    `ifdef COVER_RV32ZHINX_ILLEGAL
        `include "coverage/RV32ZHINX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32A
        `include "coverage/RV32A_coverage.svh"
    `endif
    `ifdef COVER_RV32A_ILLEGAL
        `include "coverage/RV32A_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBA
        `include "coverage/RV32ZBA_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBA_ILLEGAL
        `include "coverage/RV32ZBA_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBB
        `include "coverage/RV32ZBB_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBB_ILLEGAL
        `include "coverage/RV32ZBB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBC
        `include "coverage/RV32ZBC_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBC_ILLEGAL
        `include "coverage/RV32ZBC_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBS
        `include "coverage/RV32ZBS_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBS_ILLEGAL
        `include "coverage/RV32ZBS_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32C
        `include "coverage/RV32C_coverage.svh"
    `endif
    `ifdef COVER_RV32C_ILLEGAL
        `include "coverage/RV32C_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCA
        `include "coverage/RV32ZCA_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCA_ILLEGAL
        `include "coverage/RV32ZCA_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCFZFINX
        `include "coverage/RV32ZCFZFINX_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCFZFINX_ILLEGAL
        `include "coverage/RV32ZCFZFINX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCF
        `include "coverage/RV32ZCF_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCF_ILLEGAL
        `include "coverage/RV32ZCF_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCD
        `include "coverage/RV32ZCD_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCD_ILLEGAL
        `include "coverage/RV32ZCD_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCB
        `include "coverage/RV32ZCB_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCB_ILLEGAL
        `include "coverage/RV32ZCB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCMP
        `include "coverage/RV32ZCMP_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCMP_ILLEGAL
        `include "coverage/RV32ZCMP_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCMT
        `include "coverage/RV32ZCMT_coverage.svh"
    `endif
    `ifdef COVER_RV32ZCMT_ILLEGAL
        `include "coverage/RV32ZCMT_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBKB
        `include "coverage/RV32ZBKB_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBKB_ILLEGAL
        `include "coverage/RV32ZBKB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBKC
        `include "coverage/RV32ZBKC_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBKC_ILLEGAL
        `include "coverage/RV32ZBKC_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBKX
        `include "coverage/RV32ZBKX_coverage.svh"
    `endif
    `ifdef COVER_RV32ZBKX_ILLEGAL
        `include "coverage/RV32ZBKX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKND
        `include "coverage/RV32ZKND_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKND_ILLEGAL
        `include "coverage/RV32ZKND_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKNE
        `include "coverage/RV32ZKNE_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKNE_ILLEGAL
        `include "coverage/RV32ZKNE_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKNH
        `include "coverage/RV32ZKNH_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKNH_ILLEGAL
        `include "coverage/RV32ZKNH_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKSED
        `include "coverage/RV32ZKSED_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKSED_ILLEGAL
        `include "coverage/RV32ZKSED_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKSH
        `include "coverage/RV32ZKSH_coverage.svh"
    `endif
    `ifdef COVER_RV32ZKSH_ILLEGAL
        `include "coverage/RV32ZKSH_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32VB
        `include "coverage/RV32VB_coverage.svh"
    `endif
    `ifdef COVER_RV32VB_ILLEGAL
        `include "coverage/RV32VB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32VX
        `include "coverage/RV32VX_coverage.svh"
    `endif
    `ifdef COVER_RV32VX_ILLEGAL
        `include "coverage/RV32VX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32VF
        `include "coverage/RV32VF_coverage.svh"
    `endif
    `ifdef COVER_RV32VF_ILLEGAL
        `include "coverage/RV32VF_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32VI
        `include "coverage/RV32VI_coverage.svh"
    `endif
    `ifdef COVER_RV32VI_ILLEGAL
        `include "coverage/RV32VI_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32VM
        `include "coverage/RV32VM_coverage.svh"
    `endif
    `ifdef COVER_RV32VM_ILLEGAL
        `include "coverage/RV32VM_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32VP
        `include "coverage/RV32VP_coverage.svh"
    `endif
    `ifdef COVER_RV32VP_ILLEGAL
        `include "coverage/RV32VP_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32VR
        `include "coverage/RV32VR_coverage.svh"
    `endif
    `ifdef COVER_RV32VR_ILLEGAL
        `include "coverage/RV32VR_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32ZICSR
        `include "coverage/RV32ZICSR_coverage.svh"
    `endif
    `ifdef COVER_RV32ZICSR_ILLEGAL
        `include "coverage/RV32ZICSR_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32PRIVM
        `include "coverage/RV32PRIVM_coverage.svh"
    `endif
    `ifdef COVER_RV32PRIVM_ILLEGAL
        `include "coverage/RV32PRIVM_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32PRIVS
        `include "coverage/RV32PRIVS_coverage.svh"
    `endif
    `ifdef COVER_RV32PRIVS_ILLEGAL
        `include "coverage/RV32PRIVS_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64I
        `include "coverage/RV64I_coverage.svh"
    `endif
    `ifdef COVER_RV64I_ILLEGAL
        `include "coverage/RV64I_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64M
        `include "coverage/RV64M_coverage.svh"
    `endif
    `ifdef COVER_RV64M_ILLEGAL
        `include "coverage/RV64M_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZMMUL
        `include "coverage/RV64ZMMUL_coverage.svh"
    `endif
    `ifdef COVER_RV64ZMMUL_ILLEGAL
        `include "coverage/RV64ZMMUL_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64F
        `include "coverage/RV64F_coverage.svh"
    `endif
    `ifdef COVER_RV64F_ILLEGAL
        `include "coverage/RV64F_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64D
        `include "coverage/RV64D_coverage.svh"
    `endif
    `ifdef COVER_RV64D_ILLEGAL
        `include "coverage/RV64D_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZFINX
        `include "coverage/RV64ZFINX_coverage.svh"
    `endif
    `ifdef COVER_RV64ZFINX_ILLEGAL
        `include "coverage/RV64ZFINX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZDINX
        `include "coverage/RV64ZDINX_coverage.svh"
    `endif
    `ifdef COVER_RV64ZDINX_ILLEGAL
        `include "coverage/RV64ZDINX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64A
        `include "coverage/RV64A_coverage.svh"
    `endif
    `ifdef COVER_RV64A_ILLEGAL
        `include "coverage/RV64A_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBA
        `include "coverage/RV64ZBA_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBA_ILLEGAL
        `include "coverage/RV64ZBA_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBB
        `include "coverage/RV64ZBB_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBB_ILLEGAL
        `include "coverage/RV64ZBB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBC
        `include "coverage/RV64ZBC_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBC_ILLEGAL
        `include "coverage/RV64ZBC_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBS
        `include "coverage/RV64ZBS_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBS_ILLEGAL
        `include "coverage/RV64ZBS_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64C
        `include "coverage/RV64C_coverage.svh"
    `endif
    `ifdef COVER_RV64C_ILLEGAL
        `include "coverage/RV64C_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCA
        `include "coverage/RV64ZCA_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCA_ILLEGAL
        `include "coverage/RV64ZCA_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCD
        `include "coverage/RV64ZCD_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCD_ILLEGAL
        `include "coverage/RV64ZCD_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCB
        `include "coverage/RV64ZCB_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCB_ILLEGAL
        `include "coverage/RV64ZCB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCMP
        `include "coverage/RV64ZCMP_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCMP_ILLEGAL
        `include "coverage/RV64ZCMP_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCMT
        `include "coverage/RV64ZCMT_coverage.svh"
    `endif
    `ifdef COVER_RV64ZCMT_ILLEGAL
        `include "coverage/RV64ZCMT_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBKB
        `include "coverage/RV64ZBKB_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBKB_ILLEGAL
        `include "coverage/RV64ZBKB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBKC
        `include "coverage/RV64ZBKC_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBKC_ILLEGAL
        `include "coverage/RV64ZBKC_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBKX
        `include "coverage/RV64ZBKX_coverage.svh"
    `endif
    `ifdef COVER_RV64ZBKX_ILLEGAL
        `include "coverage/RV64ZBKX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKND
        `include "coverage/RV64ZKND_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKND_ILLEGAL
        `include "coverage/RV64ZKND_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKNE
        `include "coverage/RV64ZKNE_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKNE_ILLEGAL
        `include "coverage/RV64ZKNE_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKNH
        `include "coverage/RV64ZKNH_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKNH_ILLEGAL
        `include "coverage/RV64ZKNH_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKSED
        `include "coverage/RV64ZKSED_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKSED_ILLEGAL
        `include "coverage/RV64ZKSED_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKSH
        `include "coverage/RV64ZKSH_coverage.svh"
    `endif
    `ifdef COVER_RV64ZKSH_ILLEGAL
        `include "coverage/RV64ZKSH_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64VB
        `include "coverage/RV64VB_coverage.svh"
    `endif
    `ifdef COVER_RV64VB_ILLEGAL
        `include "coverage/RV64VB_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64VX
        `include "coverage/RV64VX_coverage.svh"
    `endif
    `ifdef COVER_RV64VX_ILLEGAL
        `include "coverage/RV64VX_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64VF
        `include "coverage/RV64VF_coverage.svh"
    `endif
    `ifdef COVER_RV64VF_ILLEGAL
        `include "coverage/RV64VF_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64VI
        `include "coverage/RV64VI_coverage.svh"
    `endif
    `ifdef COVER_RV64VI_ILLEGAL
        `include "coverage/RV64VI_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64VM
        `include "coverage/RV64VM_coverage.svh"
    `endif
    `ifdef COVER_RV64VM_ILLEGAL
        `include "coverage/RV64VM_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64VP
        `include "coverage/RV64VP_coverage.svh"
    `endif
    `ifdef COVER_RV64VP_ILLEGAL
        `include "coverage/RV64VP_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64VR
        `include "coverage/RV64VR_coverage.svh"
    `endif
    `ifdef COVER_RV64VR_ILLEGAL
        `include "coverage/RV64VR_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64ZICSR
        `include "coverage/RV64ZICSR_coverage.svh"
    `endif
    `ifdef COVER_RV64ZICSR_ILLEGAL
        `include "coverage/RV64ZICSR_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64PRIVM
        `include "coverage/RV64PRIVM_coverage.svh"
    `endif
    `ifdef COVER_RV64PRIVM_ILLEGAL
        `include "coverage/RV64PRIVM_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV64PRIVS
        `include "coverage/RV64PRIVS_coverage.svh"
    `endif
    `ifdef COVER_RV64PRIVS_ILLEGAL
        `include "coverage/RV64PRIVS_illegal_coverage.svh"
    `endif
    `ifdef COVER_RVVI_METRICS
        `include "coverage/RVVI_METRICS_coverage.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV32
        `include "coverage/RSC_MMU_SV32_coverage.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV39
        `include "coverage/RSC_MMU_SV39_coverage.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV48
        `include "coverage/RSC_MMU_SV48_coverage.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV57
        `include "coverage/RSC_MMU_SV57_coverage.svh"
    `endif
    `ifdef COVER_XPULPV2
        `include "coverage/XPULPV2_coverage.svh"
    `endif
    `ifdef COVER_XPULPV2_ILLEGAL
        `include "coverage/XPULPV2_illegal_coverage.svh"
    `endif
    `ifdef COVER_XPULPV2C
        `include "coverage/XPULPV2C_coverage.svh"
    `endif
    `ifdef COVER_XPULPV2C_ILLEGAL
        `include "coverage/XPULPV2C_illegal_coverage.svh"
    `endif
    `ifdef COVER_RV32PMP
        `include "coverage/RV32PMP_coverage.svh"
    `endif
    `ifdef COVER_RV64PMP
        `include "coverage/RV64PMP_coverage.svh"
    `endif
    `ifdef COVER_RV32EPMP
        `include "coverage/RV32EPMP_coverage.svh"
    `endif
    `ifdef COVER_RV64EPMP
        `include "coverage/RV64EPMP_coverage.svh"
    `endif

    virtual rvviTrace #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE) rvvi;


    function new(virtual rvviTrace #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE) rvvi);

        this.rvvi = rvvi;
        `cover_info("//  riscvISACOV    ");
        `cover_info("//  Version eng.20241129.0\n//");
        `cover_info("//  Copyright (c) 2005-2024 Imperas Software Ltd. ");
        `cover_info("//  All Rights Reserved.\n//");
        `cover_info("//    Configuration:");

    `ifdef COVER_BASE_RV32I
        `cover_info("//      BASE: RV32I");
    `endif
    `ifdef COVER_BASE_RV32E
        `cover_info("//      BASE: RV32E");
    `endif
    `ifdef COVER_BASE_RV64I
        `cover_info("//      BASE: RV64I");
    `endif
    `ifdef COVER_BASE_RV64E
        `cover_info("//      BASE: RV64E");
    `endif

        `cover_info("//      COVER LEVELS:");
    `ifdef COVER_LEVEL_COMPL_BAS
        `cover_info("//        Compliance Basic - Enabled");
    `else
        `cover_info("//        Compliance Basic - Disabled");
    `endif
    `ifdef COVER_LEVEL_COMPL_EXT
        `cover_info("//        Compliance Extended - Enabled");
    `else
        `cover_info("//        Compliance Extended - Disabled");
    `endif
    `ifdef COVER_LEVEL_DV_UP_BAS
        `cover_info("//        DV Un-privileged Basic - Enabled");
    `else
        `cover_info("//        DV Un-privileged Basic - Disabled");
    `endif
    `ifdef COVER_LEVEL_DV_UP_EXT
        `cover_info("//        DV Un-privileged Extended - Enabled");
    `else
        `cover_info("//        DV Un-privileged Extended - Disabled");
    `endif
    `ifdef COVER_LEVEL_DV_PR_BAS
        `cover_info("//        DV Privileged Basic - Enabled");
    `else
        `cover_info("//        DV Privileged Basic - Disabled");
    `endif
    `ifdef COVER_LEVEL_DV_PR_EXT
        `cover_info("//        DV Privileged Extended - Enabled");
    `else
        `cover_info("//        DV Privileged Extended - Disabled");
    `endif
    `cover_info("//      COVER TYPES:");
    `ifdef COVER_TYPE_ASM_COUNT
        `cover_info("//        ASM_COUNT - Enabled");
    `else
        `cover_info("//        ASM_COUNT - Disabled");
    `endif
    `ifdef COVER_TYPE_ASSIGNMENTS
        `cover_info("//        ASSIGNMENTS - Enabled");
    `else
        `cover_info("//        ASSIGNMENTS - Disabled");
    `endif
    `ifdef COVER_TYPE_CROSS_VALUES
        `cover_info("//        CROSS_VALUES - Enabled");
    `else
        `cover_info("//        CROSS_VALUES - Disabled");
    `endif
    `ifdef COVER_TYPE_CSR
        `cover_info("//        CSR - Enabled");
    `else
        `cover_info("//        CSR - Disabled");
    `endif
    `ifdef COVER_TYPE_CSR_VALUE
        `cover_info("//        CSR_VALUE - Enabled");
    `else
        `cover_info("//        CSR_VALUE - Disabled");
    `endif
    `ifdef COVER_TYPE_EQUAL
        `cover_info("//        EQUAL - Enabled");
    `else
        `cover_info("//        EQUAL - Disabled");
    `endif
    `ifdef COVER_TYPE_FAULTS
        `cover_info("//        FAULTS - Enabled");
    `else
        `cover_info("//        FAULTS - Disabled");
    `endif
    `ifdef COVER_TYPE_FPVALUES
        `cover_info("//        FPVALUES - Enabled");
    `else
        `cover_info("//        FPVALUES - Disabled");
    `endif
    `ifdef COVER_TYPE_FRM
        `cover_info("//        FRM - Enabled");
    `else
        `cover_info("//        FRM - Disabled");
    `endif
    `ifdef COVER_TYPE_HAZARD
        `cover_info("//        HAZARD - Enabled");
    `else
        `cover_info("//        HAZARD - Disabled");
    `endif
    `ifdef COVER_TYPE_ILLEGAL_INST
        `cover_info("//        ILLEGAL_INST - Enabled");
    `else
        `cover_info("//        ILLEGAL_INST - Disabled");
    `endif
    `ifdef COVER_TYPE_MAXVALS
        `cover_info("//        MAXVALS - Enabled");
    `else
        `cover_info("//        MAXVALS - Disabled");
    `endif
    `ifdef COVER_TYPE_METRIC
        `cover_info("//        METRIC - Enabled");
    `else
        `cover_info("//        METRIC - Disabled");
    `endif
    `ifdef COVER_TYPE_REG_COMPARE
        `cover_info("//        REG_COMPARE - Enabled");
    `else
        `cover_info("//        REG_COMPARE - Disabled");
    `endif
    `ifdef COVER_TYPE_SIGNS
        `cover_info("//        SIGNS - Enabled");
    `else
        `cover_info("//        SIGNS - Disabled");
    `endif
    `ifdef COVER_TYPE_TOGGLE
        `cover_info("//        TOGGLE - Enabled");
    `else
        `cover_info("//        TOGGLE - Disabled");
    `endif
    `ifdef COVER_TYPE_VALUES
        `cover_info("//        VALUES - Enabled");
    `else
        `cover_info("//        VALUES - Disabled");
    `endif
    `ifdef COVER_TYPE_VECTOR
        `cover_info("//        VECTOR - Enabled");
    `else
        `cover_info("//        VECTOR - Disabled");
    `endif

    `cover_info("//    EXTENSIONS:");
    `ifdef COVER_RV32I_IMPTEST
        `cover_info("//      RV32I_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RV32I_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RV32F_IMPTEST
        `cover_info("//      RV32F_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RV32F_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RV32C_IMPTEST
        `cover_info("//      RV32C_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RV32C_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCF_IMPTEST
        `cover_info("//      RV32ZCF_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RV32ZCF_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMP_IMPTEST
        `cover_info("//      RV32ZCMP_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RV32ZCMP_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMT_IMPTEST
        `cover_info("//      RV32ZCMT_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RV32ZCMT_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VB_IMPTEST
        `cover_info("//      RV32VB_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RV32VB_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VX_IMPTEST
        `cover_info("//      RV32VX_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RV32VX_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RVVI_METRICS_IMPTEST
        `cover_info("//      RVVI_METRICS_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RVVI_METRICS_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV32_IMPTEST
        `cover_info("//      RSC_MMU_SV32_IMPTEST - Enabled (Dev Only)");
        `include "coverage/RSC_MMU_SV32_IMPTEST_coverage_init.svh"
    `endif
    `ifdef COVER_XPULPV2_IMPTEST
        `cover_info("//      XPULPV2_IMPTEST - Enabled (Dev Only)");
        `include "coverage/XPULPV2_IMPTEST_coverage_init.svh"
    `endif

    `ifdef COVER_RV32I
      `ifdef COVER_BASE_RV32E
        `cover_info("// Warning: RV32I conflicts with BASE_RV32E");
      `else
        `cover_info("//      RV32I - Enabled");
        `include "coverage/RV32I_coverage_init.svh"
      `endif
    `endif
    `ifdef COVER_RV32I_ILLEGAL
        `cover_info("//      RV32I_ILLEGAL - Enabled");
        `include "coverage/RV32I_coverage_init.svh"
    `endif
    `ifdef COVER_RV32E
      `ifdef COVER_BASE_RV32I
        `cover_info("// Warning: RV32E conflicts with BASE_RV32I");
      `else
        `cover_info("//      RV32E - Enabled");
        `include "coverage/RV32E_coverage_init.svh"
      `endif
    `endif
    `ifdef COVER_RV32E_ILLEGAL
        `cover_info("//      RV32E_ILLEGAL - Enabled");
        `include "coverage/RV32E_coverage_init.svh"
    `endif
    `ifdef COVER_RV32M
        `cover_info("//      RV32M - Enabled");
        `include "coverage/RV32M_coverage_init.svh"
    `endif
    `ifdef COVER_RV32M_ILLEGAL
        `cover_info("//      RV32M_ILLEGAL - Enabled");
        `include "coverage/RV32M_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZMMUL
        `cover_info("//      RV32ZMMUL - Enabled");
        `include "coverage/RV32ZMMUL_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZMMUL_ILLEGAL
        `cover_info("//      RV32ZMMUL_ILLEGAL - Enabled");
        `include "coverage/RV32ZMMUL_coverage_init.svh"
    `endif
    `ifdef COVER_RV32F
        `cover_info("//      RV32F - Enabled");
        `include "coverage/RV32F_coverage_init.svh"
    `endif
    `ifdef COVER_RV32F_ILLEGAL
        `cover_info("//      RV32F_ILLEGAL - Enabled");
        `include "coverage/RV32F_coverage_init.svh"
    `endif
    `ifdef COVER_RV32F_COMPARE
        `cover_info("//      RV32F_COMPARE - Enabled");
    `endif
    `ifdef COVER_RV32ZFINX
        `cover_info("//      RV32ZFINX - Enabled");
        `include "coverage/RV32ZFINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZFINX_ILLEGAL
        `cover_info("//      RV32ZFINX_ILLEGAL - Enabled");
        `include "coverage/RV32ZFINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZHINX
        `cover_info("//      RV32ZHINX - Enabled");
        `include "coverage/RV32ZHINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZHINX_ILLEGAL
        `cover_info("//      RV32ZHINX_ILLEGAL - Enabled");
        `include "coverage/RV32ZHINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32A
        `cover_info("//      RV32A - Enabled");
        `include "coverage/RV32A_coverage_init.svh"
    `endif
    `ifdef COVER_RV32A_ILLEGAL
        `cover_info("//      RV32A_ILLEGAL - Enabled");
        `include "coverage/RV32A_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBA
        `cover_info("//      RV32ZBA - Enabled");
        `include "coverage/RV32ZBA_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBA_ILLEGAL
        `cover_info("//      RV32ZBA_ILLEGAL - Enabled");
        `include "coverage/RV32ZBA_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBB
        `cover_info("//      RV32ZBB - Enabled");
        `include "coverage/RV32ZBB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBB_ILLEGAL
        `cover_info("//      RV32ZBB_ILLEGAL - Enabled");
        `include "coverage/RV32ZBB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBC
        `cover_info("//      RV32ZBC - Enabled");
        `include "coverage/RV32ZBC_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBC_ILLEGAL
        `cover_info("//      RV32ZBC_ILLEGAL - Enabled");
        `include "coverage/RV32ZBC_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBS
        `cover_info("//      RV32ZBS - Enabled");
        `include "coverage/RV32ZBS_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBS_ILLEGAL
        `cover_info("//      RV32ZBS_ILLEGAL - Enabled");
        `include "coverage/RV32ZBS_coverage_init.svh"
    `endif
    `ifdef COVER_RV32C
        `cover_info("//      RV32C - Enabled");
        `include "coverage/RV32C_coverage_init.svh"
    `endif
    `ifdef COVER_RV32C_ILLEGAL
        `cover_info("//      RV32C_ILLEGAL - Enabled");
        `include "coverage/RV32C_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCA
      `ifdef COVER_RV32C
        `cover_info("// Warning: RV32ZCA conflicts with RV32C");
      `else
        `cover_info("//      RV32ZCA - Enabled");
        `include "coverage/RV32ZCA_coverage_init.svh"
      `endif
    `endif
    `ifdef COVER_RV32ZCA_ILLEGAL
        `cover_info("//      RV32ZCA_ILLEGAL - Enabled");
        `include "coverage/RV32ZCA_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCFZFINX
        `cover_info("//      RV32ZCFZFINX - Enabled");
        `include "coverage/RV32ZCFZFINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCFZFINX_ILLEGAL
        `cover_info("//      RV32ZCFZFINX_ILLEGAL - Enabled");
        `include "coverage/RV32ZCFZFINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCF
        `cover_info("//      RV32ZCF - Enabled");
        `include "coverage/RV32ZCF_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCF_ILLEGAL
        `cover_info("//      RV32ZCF_ILLEGAL - Enabled");
        `include "coverage/RV32ZCF_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCD
        `cover_info("//      RV32ZCD - Enabled");
        `include "coverage/RV32ZCD_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCD_ILLEGAL
        `cover_info("//      RV32ZCD_ILLEGAL - Enabled");
        `include "coverage/RV32ZCD_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCB
        `cover_info("//      RV32ZCB - Enabled");
        `include "coverage/RV32ZCB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCB_ILLEGAL
        `cover_info("//      RV32ZCB_ILLEGAL - Enabled");
        `include "coverage/RV32ZCB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMP
        `cover_info("//      RV32ZCMP - Enabled");
        `include "coverage/RV32ZCMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMP_ILLEGAL
        `cover_info("//      RV32ZCMP_ILLEGAL - Enabled");
        `include "coverage/RV32ZCMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMT
        `cover_info("//      RV32ZCMT - Enabled");
        `include "coverage/RV32ZCMT_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZCMT_ILLEGAL
        `cover_info("//      RV32ZCMT_ILLEGAL - Enabled");
        `include "coverage/RV32ZCMT_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBKB
      `ifdef COVER_RV32ZBB
        `cover_info("// Warning: RV32ZBKB conflicts with RV32ZBB");
      `else
        `cover_info("//      RV32ZBKB - Enabled");
        `include "coverage/RV32ZBKB_coverage_init.svh"
      `endif
    `endif
    `ifdef COVER_RV32ZBKB_ILLEGAL
        `cover_info("//      RV32ZBKB_ILLEGAL - Enabled");
        `include "coverage/RV32ZBKB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBKC
      `ifdef COVER_RV32ZBC
        `cover_info("// Warning: RV32ZBKC conflicts with RV32ZBC");
      `else
        `cover_info("//      RV32ZBKC - Enabled");
        `include "coverage/RV32ZBKC_coverage_init.svh"
      `endif
    `endif
    `ifdef COVER_RV32ZBKC_ILLEGAL
        `cover_info("//      RV32ZBKC_ILLEGAL - Enabled");
        `include "coverage/RV32ZBKC_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBKX
        `cover_info("//      RV32ZBKX - Enabled");
        `include "coverage/RV32ZBKX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZBKX_ILLEGAL
        `cover_info("//      RV32ZBKX_ILLEGAL - Enabled");
        `include "coverage/RV32ZBKX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKND
        `cover_info("//      RV32ZKND - Enabled");
        `include "coverage/RV32ZKND_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKND_ILLEGAL
        `cover_info("//      RV32ZKND_ILLEGAL - Enabled");
        `include "coverage/RV32ZKND_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKNE
        `cover_info("//      RV32ZKNE - Enabled");
        `include "coverage/RV32ZKNE_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKNE_ILLEGAL
        `cover_info("//      RV32ZKNE_ILLEGAL - Enabled");
        `include "coverage/RV32ZKNE_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKNH
        `cover_info("//      RV32ZKNH - Enabled");
        `include "coverage/RV32ZKNH_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKNH_ILLEGAL
        `cover_info("//      RV32ZKNH_ILLEGAL - Enabled");
        `include "coverage/RV32ZKNH_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKSED
        `cover_info("//      RV32ZKSED - Enabled");
        `include "coverage/RV32ZKSED_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKSED_ILLEGAL
        `cover_info("//      RV32ZKSED_ILLEGAL - Enabled");
        `include "coverage/RV32ZKSED_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKSH
        `cover_info("//      RV32ZKSH - Enabled");
        `include "coverage/RV32ZKSH_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZKSH_ILLEGAL
        `cover_info("//      RV32ZKSH_ILLEGAL - Enabled");
        `include "coverage/RV32ZKSH_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VB
        `cover_info("//      RV32VB - Enabled");
        `include "coverage/RV32VB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VB_ILLEGAL
        `cover_info("//      RV32VB_ILLEGAL - Enabled");
        `include "coverage/RV32VB_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VX
        `cover_info("//      RV32VX - Enabled");
        `include "coverage/RV32VX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VX_ILLEGAL
        `cover_info("//      RV32VX_ILLEGAL - Enabled");
        `include "coverage/RV32VX_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VF
        `cover_info("//      RV32VF - Enabled");
        `include "coverage/RV32VF_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VF_ILLEGAL
        `cover_info("//      RV32VF_ILLEGAL - Enabled");
        `include "coverage/RV32VF_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VI
        `cover_info("//      RV32VI - Enabled");
        `include "coverage/RV32VI_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VI_ILLEGAL
        `cover_info("//      RV32VI_ILLEGAL - Enabled");
        `include "coverage/RV32VI_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VM
        `cover_info("//      RV32VM - Enabled");
        `include "coverage/RV32VM_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VM_ILLEGAL
        `cover_info("//      RV32VM_ILLEGAL - Enabled");
        `include "coverage/RV32VM_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VP
        `cover_info("//      RV32VP - Enabled");
        `include "coverage/RV32VP_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VP_ILLEGAL
        `cover_info("//      RV32VP_ILLEGAL - Enabled");
        `include "coverage/RV32VP_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VR
        `cover_info("//      RV32VR - Enabled");
        `include "coverage/RV32VR_coverage_init.svh"
    `endif
    `ifdef COVER_RV32VR_ILLEGAL
        `cover_info("//      RV32VR_ILLEGAL - Enabled");
        `include "coverage/RV32VR_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZICSR
        `cover_info("//      RV32ZICSR - Enabled");
        `include "coverage/RV32ZICSR_coverage_init.svh"
    `endif
    `ifdef COVER_RV32ZICSR_ILLEGAL
        `cover_info("//      RV32ZICSR_ILLEGAL - Enabled");
        `include "coverage/RV32ZICSR_coverage_init.svh"
    `endif
    `ifdef COVER_RV32PRIVM
        `cover_info("//      RV32PRIVM - Enabled");
        `include "coverage/RV32PRIVM_coverage_init.svh"
    `endif
    `ifdef COVER_RV32PRIVM_ILLEGAL
        `cover_info("//      RV32PRIVM_ILLEGAL - Enabled");
        `include "coverage/RV32PRIVM_coverage_init.svh"
    `endif
    `ifdef COVER_RV32PRIVM_COMPARE
        `cover_info("//      RV32PRIVM_COMPARE - Enabled");
    `endif
    `ifdef COVER_RV32PRIVS
        `cover_info("//      RV32PRIVS - Enabled");
        `include "coverage/RV32PRIVS_coverage_init.svh"
    `endif
    `ifdef COVER_RV32PRIVS_ILLEGAL
        `cover_info("//      RV32PRIVS_ILLEGAL - Enabled");
        `include "coverage/RV32PRIVS_coverage_init.svh"
    `endif
    `ifdef COVER_RV32PRIVS_COMPARE
        `cover_info("//      RV32PRIVS_COMPARE - Enabled");
    `endif
    `ifdef COVER_RV64I
        `cover_info("//      RV64I - Enabled");
        `include "coverage/RV64I_coverage_init.svh"
    `endif
    `ifdef COVER_RV64I_ILLEGAL
        `cover_info("//      RV64I_ILLEGAL - Enabled");
        `include "coverage/RV64I_coverage_init.svh"
    `endif
    `ifdef COVER_RV64M
        `cover_info("//      RV64M - Enabled");
        `include "coverage/RV64M_coverage_init.svh"
    `endif
    `ifdef COVER_RV64M_ILLEGAL
        `cover_info("//      RV64M_ILLEGAL - Enabled");
        `include "coverage/RV64M_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZMMUL
        `cover_info("//      RV64ZMMUL - Enabled");
        `include "coverage/RV64ZMMUL_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZMMUL_ILLEGAL
        `cover_info("//      RV64ZMMUL_ILLEGAL - Enabled");
        `include "coverage/RV64ZMMUL_coverage_init.svh"
    `endif
    `ifdef COVER_RV64F
        `cover_info("//      RV64F - Enabled");
        `include "coverage/RV64F_coverage_init.svh"
    `endif
    `ifdef COVER_RV64F_ILLEGAL
        `cover_info("//      RV64F_ILLEGAL - Enabled");
        `include "coverage/RV64F_coverage_init.svh"
    `endif
    `ifdef COVER_RV64D
        `cover_info("//      RV64D - Enabled");
        `include "coverage/RV64D_coverage_init.svh"
    `endif
    `ifdef COVER_RV64D_ILLEGAL
        `cover_info("//      RV64D_ILLEGAL - Enabled");
        `include "coverage/RV64D_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZFINX
        `cover_info("//      RV64ZFINX - Enabled");
        `include "coverage/RV64ZFINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZFINX_ILLEGAL
        `cover_info("//      RV64ZFINX_ILLEGAL - Enabled");
        `include "coverage/RV64ZFINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZDINX
        `cover_info("//      RV64ZDINX - Enabled");
        `include "coverage/RV64ZDINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZDINX_ILLEGAL
        `cover_info("//      RV64ZDINX_ILLEGAL - Enabled");
        `include "coverage/RV64ZDINX_coverage_init.svh"
    `endif
    `ifdef COVER_RV64A
        `cover_info("//      RV64A - Enabled");
        `include "coverage/RV64A_coverage_init.svh"
    `endif
    `ifdef COVER_RV64A_ILLEGAL
        `cover_info("//      RV64A_ILLEGAL - Enabled");
        `include "coverage/RV64A_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBA
        `cover_info("//      RV64ZBA - Enabled");
        `include "coverage/RV64ZBA_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBA_ILLEGAL
        `cover_info("//      RV64ZBA_ILLEGAL - Enabled");
        `include "coverage/RV64ZBA_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBB
        `cover_info("//      RV64ZBB - Enabled");
        `include "coverage/RV64ZBB_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBB_ILLEGAL
        `cover_info("//      RV64ZBB_ILLEGAL - Enabled");
        `include "coverage/RV64ZBB_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBC
        `cover_info("//      RV64ZBC - Enabled");
        `include "coverage/RV64ZBC_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBC_ILLEGAL
        `cover_info("//      RV64ZBC_ILLEGAL - Enabled");
        `include "coverage/RV64ZBC_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBS
        `cover_info("//      RV64ZBS - Enabled");
        `include "coverage/RV64ZBS_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBS_ILLEGAL
        `cover_info("//      RV64ZBS_ILLEGAL - Enabled");
        `include "coverage/RV64ZBS_coverage_init.svh"
    `endif
    `ifdef COVER_RV64C
        `cover_info("//      RV64C - Enabled");
        `include "coverage/RV64C_coverage_init.svh"
    `endif
    `ifdef COVER_RV64C_ILLEGAL
        `cover_info("//      RV64C_ILLEGAL - Enabled");
        `include "coverage/RV64C_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCA
      `ifdef COVER_RV64C
        `cover_info("// Warning: RV64ZCA conflicts with RV64C");
      `else
        `cover_info("//      RV64ZCA - Enabled");
        `include "coverage/RV64ZCA_coverage_init.svh"
      `endif
    `endif
    `ifdef COVER_RV64ZCA_ILLEGAL
        `cover_info("//      RV64ZCA_ILLEGAL - Enabled");
        `include "coverage/RV64ZCA_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCD
        `cover_info("//      RV64ZCD - Enabled");
        `include "coverage/RV64ZCD_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCD_ILLEGAL
        `cover_info("//      RV64ZCD_ILLEGAL - Enabled");
        `include "coverage/RV64ZCD_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCB
        `cover_info("//      RV64ZCB - Enabled");
        `include "coverage/RV64ZCB_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCB_ILLEGAL
        `cover_info("//      RV64ZCB_ILLEGAL - Enabled");
        `include "coverage/RV64ZCB_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCMP
        `cover_info("//      RV64ZCMP - Enabled");
        `include "coverage/RV64ZCMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCMP_ILLEGAL
        `cover_info("//      RV64ZCMP_ILLEGAL - Enabled");
        `include "coverage/RV64ZCMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCMT
        `cover_info("//      RV64ZCMT - Enabled");
        `include "coverage/RV64ZCMT_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZCMT_ILLEGAL
        `cover_info("//      RV64ZCMT_ILLEGAL - Enabled");
        `include "coverage/RV64ZCMT_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBKB
      `ifdef COVER_RV64ZBB
        `cover_info("// Warning: RV64ZBKB conflicts with RV64ZBB");
      `else
        `cover_info("//      RV64ZBKB - Enabled");
        `include "coverage/RV64ZBKB_coverage_init.svh"
      `endif
    `endif
    `ifdef COVER_RV64ZBKB_ILLEGAL
        `cover_info("//      RV64ZBKB_ILLEGAL - Enabled");
        `include "coverage/RV64ZBKB_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBKC
      `ifdef COVER_RV64ZBC
        `cover_info("// Warning: RV64ZBKC conflicts with RV64ZBC");
      `else
        `cover_info("//      RV64ZBKC - Enabled");
        `include "coverage/RV64ZBKC_coverage_init.svh"
      `endif
    `endif
    `ifdef COVER_RV64ZBKC_ILLEGAL
        `cover_info("//      RV64ZBKC_ILLEGAL - Enabled");
        `include "coverage/RV64ZBKC_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBKX
        `cover_info("//      RV64ZBKX - Enabled");
        `include "coverage/RV64ZBKX_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZBKX_ILLEGAL
        `cover_info("//      RV64ZBKX_ILLEGAL - Enabled");
        `include "coverage/RV64ZBKX_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKND
        `cover_info("//      RV64ZKND - Enabled");
        `include "coverage/RV64ZKND_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKND_ILLEGAL
        `cover_info("//      RV64ZKND_ILLEGAL - Enabled");
        `include "coverage/RV64ZKND_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKNE
        `cover_info("//      RV64ZKNE - Enabled");
        `include "coverage/RV64ZKNE_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKNE_ILLEGAL
        `cover_info("//      RV64ZKNE_ILLEGAL - Enabled");
        `include "coverage/RV64ZKNE_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKNH
        `cover_info("//      RV64ZKNH - Enabled");
        `include "coverage/RV64ZKNH_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKNH_ILLEGAL
        `cover_info("//      RV64ZKNH_ILLEGAL - Enabled");
        `include "coverage/RV64ZKNH_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKSED
        `cover_info("//      RV64ZKSED - Enabled");
        `include "coverage/RV64ZKSED_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKSED_ILLEGAL
        `cover_info("//      RV64ZKSED_ILLEGAL - Enabled");
        `include "coverage/RV64ZKSED_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKSH
        `cover_info("//      RV64ZKSH - Enabled");
        `include "coverage/RV64ZKSH_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZKSH_ILLEGAL
        `cover_info("//      RV64ZKSH_ILLEGAL - Enabled");
        `include "coverage/RV64ZKSH_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VB
        `cover_info("//      RV64VB - Enabled");
        `include "coverage/RV64VB_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VB_ILLEGAL
        `cover_info("//      RV64VB_ILLEGAL - Enabled");
        `include "coverage/RV64VB_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VX
        `cover_info("//      RV64VX - Enabled");
        `include "coverage/RV64VX_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VX_ILLEGAL
        `cover_info("//      RV64VX_ILLEGAL - Enabled");
        `include "coverage/RV64VX_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VF
        `cover_info("//      RV64VF - Enabled");
        `include "coverage/RV64VF_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VF_ILLEGAL
        `cover_info("//      RV64VF_ILLEGAL - Enabled");
        `include "coverage/RV64VF_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VI
        `cover_info("//      RV64VI - Enabled");
        `include "coverage/RV64VI_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VI_ILLEGAL
        `cover_info("//      RV64VI_ILLEGAL - Enabled");
        `include "coverage/RV64VI_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VM
        `cover_info("//      RV64VM - Enabled");
        `include "coverage/RV64VM_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VM_ILLEGAL
        `cover_info("//      RV64VM_ILLEGAL - Enabled");
        `include "coverage/RV64VM_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VP
        `cover_info("//      RV64VP - Enabled");
        `include "coverage/RV64VP_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VP_ILLEGAL
        `cover_info("//      RV64VP_ILLEGAL - Enabled");
        `include "coverage/RV64VP_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VR
        `cover_info("//      RV64VR - Enabled");
        `include "coverage/RV64VR_coverage_init.svh"
    `endif
    `ifdef COVER_RV64VR_ILLEGAL
        `cover_info("//      RV64VR_ILLEGAL - Enabled");
        `include "coverage/RV64VR_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZICSR
        `cover_info("//      RV64ZICSR - Enabled");
        `include "coverage/RV64ZICSR_coverage_init.svh"
    `endif
    `ifdef COVER_RV64ZICSR_ILLEGAL
        `cover_info("//      RV64ZICSR_ILLEGAL - Enabled");
        `include "coverage/RV64ZICSR_coverage_init.svh"
    `endif
    `ifdef COVER_RV64PRIVM
        `cover_info("//      RV64PRIVM - Enabled");
        `include "coverage/RV64PRIVM_coverage_init.svh"
    `endif
    `ifdef COVER_RV64PRIVM_ILLEGAL
        `cover_info("//      RV64PRIVM_ILLEGAL - Enabled");
        `include "coverage/RV64PRIVM_coverage_init.svh"
    `endif
    `ifdef COVER_RV64PRIVM_COMPARE
        `cover_info("//      RV64PRIVM_COMPARE - Enabled");
    `endif
    `ifdef COVER_RV64PRIVS
        `cover_info("//      RV64PRIVS - Enabled");
        `include "coverage/RV64PRIVS_coverage_init.svh"
    `endif
    `ifdef COVER_RV64PRIVS_ILLEGAL
        `cover_info("//      RV64PRIVS_ILLEGAL - Enabled");
        `include "coverage/RV64PRIVS_coverage_init.svh"
    `endif
    `ifdef COVER_RV64PRIVS_COMPARE
        `cover_info("//      RV64PRIVS_COMPARE - Enabled");
    `endif
    `ifdef COVER_RVVI_METRICS
        `cover_info("//      RVVI_METRICS - Enabled");
        `include "coverage/RVVI_METRICS_coverage_init.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV32
        `cover_info("//      RSC_MMU_SV32 - Enabled");
        `include "coverage/RSC_MMU_SV32_coverage_init.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV39
        `cover_info("//      RSC_MMU_SV39 - Enabled");
        `include "coverage/RSC_MMU_SV39_coverage_init.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV48
        `cover_info("//      RSC_MMU_SV48 - Enabled");
        `include "coverage/RSC_MMU_SV48_coverage_init.svh"
    `endif
    `ifdef COVER_RSC_MMU_SV57
        `cover_info("//      RSC_MMU_SV57 - Enabled");
        `include "coverage/RSC_MMU_SV57_coverage_init.svh"
    `endif
    `ifdef COVER_XPULPV2
        `cover_info("//      XPULPV2 - Enabled");
        `include "coverage/XPULPV2_coverage_init.svh"
    `endif
    `ifdef COVER_XPULPV2_ILLEGAL
        `cover_info("//      XPULPV2_ILLEGAL - Enabled");
        `include "coverage/XPULPV2_coverage_init.svh"
    `endif
    `ifdef COVER_XPULPV2C
        `cover_info("//      XPULPV2C - Enabled");
        `include "coverage/XPULPV2C_coverage_init.svh"
    `endif
    `ifdef COVER_XPULPV2C_ILLEGAL
        `cover_info("//      XPULPV2C_ILLEGAL - Enabled");
        `include "coverage/XPULPV2C_coverage_init.svh"
    `endif
    `ifdef COVER_RV32PMP
        `cover_info("//      RV32PMP - Enabled");
        `include "coverage/RV32PMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV32PMP_COMPARE
        `cover_info("//      RV32PMP_COMPARE - Enabled");
    `endif
    `ifdef COVER_RV64PMP
        `cover_info("//      RV64PMP - Enabled");
        `include "coverage/RV64PMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV64PMP_COMPARE
        `cover_info("//      RV64PMP_COMPARE - Enabled");
    `endif
    `ifdef COVER_RV32EPMP
        `cover_info("//      RV32EPMP - Enabled");
        `include "coverage/RV32EPMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV32EPMP_COMPARE
        `cover_info("//      RV32EPMP_COMPARE - Enabled");
    `endif
    `ifdef COVER_RV64EPMP
        `cover_info("//      RV64EPMP - Enabled");
        `include "coverage/RV64EPMP_coverage_init.svh"
    `endif
    `ifdef COVER_RV64EPMP_COMPARE
        `cover_info("//      RV64EPMP_COMPARE - Enabled");
    `endif

        check_config();

    endfunction

    function string get_inst_name(bit trap, int hart, int issue, string disass); // break and move this first bit out
        string insbin, ins_str, ops;
        int num = $sscanf (disass, "%s %s %s", insbin, ins_str, ops);
        $display("get inst name disass = %0s \t insbin = %0s \t, ins_str = %0s \t, ops = %0s \t ", disass, insbin, ins_str, ops);
        return ins_str;
    endfunction


    function void sample_extensions(int hart, int issue);

    `ifdef COVER_RV32I_IMPTEST
        rv32i_sample(hart, issue);
    `endif
    `ifdef COVER_RV32F_IMPTEST
        rv32f_sample(hart, issue);
    `endif
    `ifdef COVER_RV32C_IMPTEST
        rv32c_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCF_IMPTEST
        rv32zcf_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCMP_IMPTEST
        rv32zcmp_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCMT_IMPTEST
        rv32zcmt_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VB_IMPTEST
        rv32vb_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VX_IMPTEST
        rv32vx_sample(hart, issue);
    `endif
    `ifdef COVER_XPULPV2_IMPTEST
        xpulpv2_sample(hart, issue);
    `endif

    `ifdef COVER_RV32I
      `ifdef COVER_BASE_RV32E
      `else
        rv32i_sample(hart, issue);
      `endif
    `endif
    `ifdef COVER_RV32I_ILLEGAL
        rv32i_sample(hart, issue);
    `endif
    `ifdef COVER_RV32E
      `ifdef COVER_BASE_RV32I
      `else
        rv32e_sample(hart, issue);
      `endif
    `endif
    `ifdef COVER_RV32E_ILLEGAL
        rv32e_sample(hart, issue);
    `endif
    `ifdef COVER_RV32M
        rv32m_sample(hart, issue);
    `endif
    `ifdef COVER_RV32M_ILLEGAL
        rv32m_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZMMUL
        rv32zmmul_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZMMUL_ILLEGAL
        rv32zmmul_sample(hart, issue);
    `endif
    `ifdef COVER_RV32F
        rv32f_sample(hart, issue);
    `endif
    `ifdef COVER_RV32F_ILLEGAL
        rv32f_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZFINX
        rv32zfinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZFINX_ILLEGAL
        rv32zfinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZHINX
        rv32zhinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZHINX_ILLEGAL
        rv32zhinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32A
        rv32a_sample(hart, issue);
    `endif
    `ifdef COVER_RV32A_ILLEGAL
        rv32a_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBA
        rv32zba_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBA_ILLEGAL
        rv32zba_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBB
        rv32zbb_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBB_ILLEGAL
        rv32zbb_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBC
        rv32zbc_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBC_ILLEGAL
        rv32zbc_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBS
        rv32zbs_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBS_ILLEGAL
        rv32zbs_sample(hart, issue);
    `endif
    `ifdef COVER_RV32C
        rv32c_sample(hart, issue);
    `endif
    `ifdef COVER_RV32C_ILLEGAL
        rv32c_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCA
      `ifdef COVER_RV32C
      `else
        rv32zca_sample(hart, issue);
      `endif
    `endif
    `ifdef COVER_RV32ZCA_ILLEGAL
        rv32zca_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCFZFINX
        rv32zcfzfinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCFZFINX_ILLEGAL
        rv32zcfzfinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCF
        rv32zcf_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCF_ILLEGAL
        rv32zcf_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCD
        rv32zcd_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCD_ILLEGAL
        rv32zcd_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCB
        rv32zcb_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCB_ILLEGAL
        rv32zcb_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCMP
        rv32zcmp_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCMP_ILLEGAL
        rv32zcmp_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCMT
        rv32zcmt_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZCMT_ILLEGAL
        rv32zcmt_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBKB
      `ifdef COVER_RV32ZBB
      `else
        rv32zbkb_sample(hart, issue);
      `endif
    `endif
    `ifdef COVER_RV32ZBKB_ILLEGAL
        rv32zbkb_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBKC
      `ifdef COVER_RV32ZBC
      `else
        rv32zbkc_sample(hart, issue);
      `endif
    `endif
    `ifdef COVER_RV32ZBKC_ILLEGAL
        rv32zbkc_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBKX
        rv32zbkx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZBKX_ILLEGAL
        rv32zbkx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKND
        rv32zknd_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKND_ILLEGAL
        rv32zknd_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKNE
        rv32zkne_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKNE_ILLEGAL
        rv32zkne_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKNH
        rv32zknh_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKNH_ILLEGAL
        rv32zknh_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKSED
        rv32zksed_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKSED_ILLEGAL
        rv32zksed_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKSH
        rv32zksh_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZKSH_ILLEGAL
        rv32zksh_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VB
        rv32vb_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VB_ILLEGAL
        rv32vb_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VX
        rv32vx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VX_ILLEGAL
        rv32vx_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VF
        rv32vf_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VF_ILLEGAL
        rv32vf_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VI
        rv32vi_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VI_ILLEGAL
        rv32vi_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VM
        rv32vm_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VM_ILLEGAL
        rv32vm_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VP
        rv32vp_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VP_ILLEGAL
        rv32vp_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VR
        rv32vr_sample(hart, issue);
    `endif
    `ifdef COVER_RV32VR_ILLEGAL
        rv32vr_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZICSR
        rv32zicsr_sample(hart, issue);
    `endif
    `ifdef COVER_RV32ZICSR_ILLEGAL
        rv32zicsr_sample(hart, issue);
    `endif
    `ifdef COVER_RV32PRIVM
        rv32privm_sample(hart, issue);
    `endif
    `ifdef COVER_RV32PRIVM_ILLEGAL
        rv32privm_sample(hart, issue);
    `endif
    `ifdef COVER_RV32PRIVS
        rv32privs_sample(hart, issue);
    `endif
    `ifdef COVER_RV32PRIVS_ILLEGAL
        rv32privs_sample(hart, issue);
    `endif
    `ifdef COVER_RV64I
        rv64i_sample(hart, issue);
    `endif
    `ifdef COVER_RV64I_ILLEGAL
        rv64i_sample(hart, issue);
    `endif
    `ifdef COVER_RV64M
        rv64m_sample(hart, issue);
    `endif
    `ifdef COVER_RV64M_ILLEGAL
        rv64m_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZMMUL
        rv64zmmul_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZMMUL_ILLEGAL
        rv64zmmul_sample(hart, issue);
    `endif
    `ifdef COVER_RV64F
        rv64f_sample(hart, issue);
    `endif
    `ifdef COVER_RV64F_ILLEGAL
        rv64f_sample(hart, issue);
    `endif
    `ifdef COVER_RV64D
        rv64d_sample(hart, issue);
    `endif
    `ifdef COVER_RV64D_ILLEGAL
        rv64d_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZFINX
        rv64zfinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZFINX_ILLEGAL
        rv64zfinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZDINX
        rv64zdinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZDINX_ILLEGAL
        rv64zdinx_sample(hart, issue);
    `endif
    `ifdef COVER_RV64A
        rv64a_sample(hart, issue);
    `endif
    `ifdef COVER_RV64A_ILLEGAL
        rv64a_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBA
        rv64zba_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBA_ILLEGAL
        rv64zba_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBB
        rv64zbb_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBB_ILLEGAL
        rv64zbb_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBC
        rv64zbc_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBC_ILLEGAL
        rv64zbc_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBS
        rv64zbs_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBS_ILLEGAL
        rv64zbs_sample(hart, issue);
    `endif
    `ifdef COVER_RV64C
        rv64c_sample(hart, issue);
    `endif
    `ifdef COVER_RV64C_ILLEGAL
        rv64c_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCA
      `ifdef COVER_RV64C
      `else
        rv64zca_sample(hart, issue);
      `endif
    `endif
    `ifdef COVER_RV64ZCA_ILLEGAL
        rv64zca_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCD
        rv64zcd_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCD_ILLEGAL
        rv64zcd_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCB
        rv64zcb_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCB_ILLEGAL
        rv64zcb_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCMP
        rv64zcmp_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCMP_ILLEGAL
        rv64zcmp_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCMT
        rv64zcmt_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZCMT_ILLEGAL
        rv64zcmt_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBKB
      `ifdef COVER_RV64ZBB
      `else
        rv64zbkb_sample(hart, issue);
      `endif
    `endif
    `ifdef COVER_RV64ZBKB_ILLEGAL
        rv64zbkb_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBKC
      `ifdef COVER_RV64ZBC
      `else
        rv64zbkc_sample(hart, issue);
      `endif
    `endif
    `ifdef COVER_RV64ZBKC_ILLEGAL
        rv64zbkc_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBKX
        rv64zbkx_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZBKX_ILLEGAL
        rv64zbkx_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKND
        rv64zknd_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKND_ILLEGAL
        rv64zknd_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKNE
        rv64zkne_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKNE_ILLEGAL
        rv64zkne_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKNH
        rv64zknh_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKNH_ILLEGAL
        rv64zknh_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKSED
        rv64zksed_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKSED_ILLEGAL
        rv64zksed_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKSH
        rv64zksh_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZKSH_ILLEGAL
        rv64zksh_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VB
        rv64vb_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VB_ILLEGAL
        rv64vb_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VX
        rv64vx_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VX_ILLEGAL
        rv64vx_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VF
        rv64vf_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VF_ILLEGAL
        rv64vf_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VI
        rv64vi_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VI_ILLEGAL
        rv64vi_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VM
        rv64vm_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VM_ILLEGAL
        rv64vm_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VP
        rv64vp_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VP_ILLEGAL
        rv64vp_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VR
        rv64vr_sample(hart, issue);
    `endif
    `ifdef COVER_RV64VR_ILLEGAL
        rv64vr_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZICSR
        rv64zicsr_sample(hart, issue);
    `endif
    `ifdef COVER_RV64ZICSR_ILLEGAL
        rv64zicsr_sample(hart, issue);
    `endif
    `ifdef COVER_RV64PRIVM
        rv64privm_sample(hart, issue);
    `endif
    `ifdef COVER_RV64PRIVM_ILLEGAL
        rv64privm_sample(hart, issue);
    `endif
    `ifdef COVER_RV64PRIVS
        rv64privs_sample(hart, issue);
    `endif
    `ifdef COVER_RV64PRIVS_ILLEGAL
        rv64privs_sample(hart, issue);
    `endif
    `ifdef COVER_XPULPV2
        xpulpv2_sample(hart, issue);
    `endif
    `ifdef COVER_XPULPV2_ILLEGAL
        xpulpv2_sample(hart, issue);
    `endif
    `ifdef COVER_XPULPV2C
        xpulpv2c_sample(hart, issue);
    `endif
    `ifdef COVER_XPULPV2C_ILLEGAL
        xpulpv2c_sample(hart, issue);
    `endif
    endfunction

    function void sample_csrs(int hart, int issue);
        int index, num;
        `XLEN_INT mask, value;
        string str;
    `ifdef COVER_RV32F
        rv32f_sample_csrs(hart, issue);
    `endif
    `ifdef COVER_RV32PRIVM
        rv32privm_sample_csrs(hart, issue);
    `endif
    `ifdef COVER_RV32PRIVS
        rv32privs_sample_csrs(hart, issue);
    `endif
    `ifdef COVER_RV64PRIVM
        rv64privm_sample_csrs(hart, issue);
    `endif
    `ifdef COVER_RV64PRIVS
        rv64privs_sample_csrs(hart, issue);
    `endif
    `ifdef COVER_RV32PMP
        rv32pmp_sample_csrs(hart, issue);
    `endif
    `ifdef COVER_RV64PMP
        rv64pmp_sample_csrs(hart, issue);
    `endif
    `ifdef COVER_RV32EPMP
        rv32epmp_sample_csrs(hart, issue);
    `endif
    `ifdef COVER_RV64EPMP
        rv64epmp_sample_csrs(hart, issue);
    `endif

    str = idvRefCoverPointNext("csrCompare");
    while (str != "") begin


        num = $sscanf (str, "%x %x %x %x", hart, index, mask, value);

        if (num != 4) begin
            $display("sample_csrs(): %0s = idvRefCoverPointNext(csrCompare) num=%0d and is should be 4", str, num);
            $finish(-1);
        end
        `ifdef COVER_RV32F_COMPARE
            rv32f_sample_csr_compares(index, mask, value);
        `endif
        `ifdef COVER_RV32PRIVM_COMPARE
            rv32privm_sample_csr_compares(index, mask, value);
        `endif
        `ifdef COVER_RV32PRIVS_COMPARE
            rv32privs_sample_csr_compares(index, mask, value);
        `endif
        `ifdef COVER_RV64PRIVM_COMPARE
            rv64privm_sample_csr_compares(index, mask, value);
        `endif
        `ifdef COVER_RV64PRIVS_COMPARE
            rv64privs_sample_csr_compares(index, mask, value);
        `endif
        `ifdef COVER_RV32PMP_COMPARE
            rv32pmp_sample_csr_compares(index, mask, value);
        `endif
        `ifdef COVER_RV64PMP_COMPARE
            rv64pmp_sample_csr_compares(index, mask, value);
        `endif
        `ifdef COVER_RV32EPMP_COMPARE
            rv32epmp_sample_csr_compares(index, mask, value);
        `endif
        `ifdef COVER_RV64EPMP_COMPARE
            rv64epmp_sample_csr_compares(index, mask, value);
        `endif
        str = idvRefCoverPointNext("csrCompare");
    end
    endfunction

    function void sample_idv_metrics();
    `ifdef COVER_RVVI_METRICS
        rvvi_metrics_sample_idv_metrics();
    `endif
    `ifdef COVER_RSC_MMU_SV32
        rsc_mmu_sv32_sample_idv_metrics();
    `endif
    `ifdef COVER_RSC_MMU_SV39
        rsc_mmu_sv39_sample_idv_metrics();
    `endif
    `ifdef COVER_RSC_MMU_SV48
        rsc_mmu_sv48_sample_idv_metrics();
    `endif
    `ifdef COVER_RSC_MMU_SV57
        rsc_mmu_sv57_sample_idv_metrics();
    `endif
    `ifdef COVER_RVVI_METRICS_IMPTEST
        rvvi_metrics_sample_idv_metrics();
    `endif
    `ifdef COVER_RSC_MMU_SV32_IMPTEST
        rsc_mmu_sv32_sample_idv_metrics();
    `endif
    endfunction

endclass




