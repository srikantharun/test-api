// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Jovin Langenegger <jovin.langenegger@axelera.ai>
//
// This test checks the correct setup of the virtual memory.
// It first prepares the MMU followed by the mret call to switch the privileged mode to supervised mode.
// Later, we execute an ecall to trap and verify the correct setup of the virtual memory.

#include "platform.h"
#include "printf.h"
#include <testutils.h>
#include <nds_csr.h>
#include <trap.h>

// Plenty of space
volatile uint64_t __attribute__((aligned(0x1000))) level4_table_mem[4*1024/8];
volatile uint64_t __attribute__((aligned(0x1000))) level3_table_mem[4*1024/8];
volatile uint64_t __attribute__((aligned(0x1000))) level2_table_mem[4*1024/8];
volatile uint64_t __attribute__((aligned(0x1000))) level1_table_mem[4*1024/8];

long ecall_handler_S_mode(SAVED_CONTEXT* ctx) {
  printf("mepc=0x%x\n", ctx->mepc);
  printf("mtval=0x%x\n", ctx->mtval);

  // We expect an ecall (environment call) from S-mode. See function vfct.
  // ecall is defined as mcause 0x9.
  CHECK_EQUAL_INT(0x9, (ctx->mcause), "Wrong mcause!");
  CHECK_EQUAL_INT(0xC0FEC0FE, (ctx->x11));

  exit(testcase_finalize());

  return 0;
};


// The following functions sits in different sections for each RISC-V
// This function is the start code for supervisor mode
uint64_t __attribute__((aligned(0x1000))) vfct(void)
{

   asm volatile(
          "li	a1, 0xC0FEC0FE\n"
          "ecall\n"
          :
          :
          :"a0"
  );
  return 1;
}

extern trap_func exception_handler[NUM_EXCEPTION_SOURCE];

int main ()
{
  testcase_init();

  exception_handler[EXC_ENVIRONMENT_CALL_FROM_S_MODE] = ecall_handler_S_mode;

  // All cores will run the following test which does the VMA test
  // Set up a PMP to permit access to all of memory.
  // Ignore the illegal-instruction trap if PMPs aren't supported.
  uintptr_t pmpc = PMP_NAPOT | PMP_R | PMP_W | PMP_X;

  asm volatile ("la t0, 1f\n\t"
                "csrrw t0, mtvec, t0\n\t"
                "csrw pmpaddr0, %1\n\t"
                "csrw pmpcfg0, %0\n\t"
                ".align 2\n\t"
                "1: csrw mtvec, t0"
                : : "r" (pmpc), "r" (-1UL) : "t0");

  uintptr_t mstatus = read_csr(NDS_MSTATUS);
  mstatus = INSERT_FIELD(mstatus, MSTATUS_MPP, PRV_S);
  mstatus = INSERT_FIELD(mstatus, MSTATUS_MPIE, 0);
  write_csr(NDS_MSTATUS, mstatus);

  // Build PPNs
  uint64_t virtual_address=0x00000000CD000000;

  uint64_t VPNs[4];
  VPNs[0]=(virtual_address>>12) & 0x1FF;
  VPNs[1]=(virtual_address>>21) & 0x1FF;
  VPNs[2]=(virtual_address>>30) & 0x1FF;
  VPNs[3]=(virtual_address>>39) & 0x1FF;

  level1_table_mem[VPNs[0]]=(((((uint64_t)&vfct)>>12)&0xFFFFFFFFFFFFFFFF)<<10) | PTE_V | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D;
  level2_table_mem[VPNs[1]]=(((((uint64_t)&level1_table_mem[0])>>12)&0xFFFFFFFFFFFFFFFF)<<10) | PTE_V;
  level3_table_mem[VPNs[2]]=(((((uint64_t)&level2_table_mem[0])>>12)&0xFFFFFFFFFFFFFFFF)<<10) | PTE_V;
  level4_table_mem[VPNs[3]]=(((((uint64_t)&level3_table_mem[0])>>12)&0xFFFFFFFFFFFFFFFF)<<10) | PTE_V;

  write_csr(NDS_MEPC, virtual_address);
  write_csr(NDS_SATP,(((uint64_t)SATP_MODE_SV48)<<60)|((uint64_t)&level4_table_mem[0])>>12);

  // Make sure we load VMA and also that we zero the a0 register for the upcoming test
  asm volatile (
        "li a0, 0x00000001\n" // Make sure to not accidently return 0.
        "sfence.vma\n"
        "mret\n"
        : // Output registers
        : // Input registers
        :"a0" //Clobbered registers
  );

  return testcase_finalize();

}
