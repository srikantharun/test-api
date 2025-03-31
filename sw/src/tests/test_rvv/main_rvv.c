// Description: This test demonstrates basic vector processing using RISC-V vector extensions.

#include <printf.h>
#include <riscv_vector.h>
#include <testutils.h>
#include <virtmem_setup.h>
#include <trap.h>
#include <asm.h>
#include <platform.h>

// Second level page table for the L1 memory region
__attribute__((aligned(SV39_PAGESIZE), section(".sys_spm"))) sv39_pt_t root_pt[4];
__attribute__((aligned(SV39_PAGESIZE), section(".sys_spm"))) sv39_pt_t l1_pt[4];

/* We need this expection handler as the default wfi is only available insdie the user space */
long except_handler(SAVED_CONTEXT* ctx) {
  if(ctx->mcause == 2){
    /* Illegal wfi instruction in user mode */
    while (1) {
      asm volatile("wfi");
    }
  }

  printf("\r\n");
  printf("=== UNHANDLED EXCEPTION ===\r\n");
  printf("mcause: 0x%08lx\r\n", ctx->mcause);
  printf("\r\n");
  printf("mepc:   0x%016lx\r\n", ctx->mepc);
  printf("mtval:  0x%016lx\r\n", ctx->mtval);
  printf("\r\n");
  printf("aborting...\r\n");

  exit((0b1 << 16) | ctx->mcause);
  while (1) {
  }
}

int main() {
  testcase_init();

  uint32_t my_page_table = (r_mhartid() - processor_first_hart_id())/PVE_NUM_CORES_PER_CLUSTER;
  setup_virt_l1(root_pt[my_page_table], l1_pt[my_page_table]);

  /* Setup _main as trap return address */
  asm volatile("la t0, run_test");
  asm volatile("csrw mepc, t0");
  /* Set mstatus MPP to user mode */
  asm volatile("la t0, 0x1800");
  asm volatile("csrc mstatus, t0");
  /* Switch to user mode, jumping to _main */
  asm volatile("mret");

  return testcase_finalize();
}
