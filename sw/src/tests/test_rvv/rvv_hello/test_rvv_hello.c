// Description: This test demonstrates basic vector processing using RISC-V vector extensions.

#include <printf.h>
#include <riscv_vector.h>
#include <testutils.h>
#include <virtmem_setup.h>
#include <trap.h>
#include <asm.h>
#include <platform.h>

// Reserve memory in L1
char __attribute__((aligned(8), section(".l1"))) cva6_str[]       = "Hello from CVA6!";
char __attribute__((aligned(64), section(".l1"))) raptor_base_str[] = "Hello from Raptor!";
char __attribute__((aligned(64), section(".l1"))) raptor_output_str[sizeof(raptor_base_str)];

void run_test(){
  printf("%s (hartid #%d)\n", cva6_str, r_uhartid());

  int   avl                   = strlen(raptor_base_str) + 1; // include NUL terminator
  char *raptor_base_str_ptr   = raptor_base_str;
  char *raptor_output_str_ptr = raptor_output_str;

  while (avl > 0) {
    uint32_t     vl = __riscv_vsetvl_e8m2(avl);
    vuint8m2_t   vi = __riscv_vle8_v_u8m2((uint8_t *)raptor_base_str_ptr, vl);
    vfloat16m4_t vf = __riscv_vfwcvt_f_xu_v_f16m4(vi, vl);
    vf              = __riscv_vfadd_vf_f16m4(vf, 1.f, vl);
    vi              = __riscv_vsub_vx_u8m2(__riscv_vfncvt_xu_f_w_u8m2(vf, vl), 1, vl);
    __riscv_vse8_v_u8m2((uint8_t *)raptor_output_str_ptr, vi, vl);
    raptor_base_str_ptr   += vl;
    raptor_output_str_ptr += vl;
    avl                   -= vl;
  }

  printf("%s\n", raptor_output_str);
  // CVA6 str len comparison
  CHECK_EQUAL_INT(sizeof(cva6_str), strlen(cva6_str)+1);
  CHECK_EQUAL_INT(sizeof(raptor_base_str), strlen(raptor_base_str)+1);

  // RVV str len comparison
  uint32_t vl = __riscv_vsetvlmax_e8m1();
  CHECK_EQUAL_INT(sizeof(cva6_str), __riscv_vfirst_m_b8(__riscv_vmseq_vx_i8m1_b8(__riscv_vle8_v_i8m1((const signed char *)cva6_str, vl), 0, vl), vl)+1);
  CHECK_EQUAL_INT(sizeof(raptor_base_str), __riscv_vfirst_m_b8(__riscv_vmseq_vx_i8m1_b8(__riscv_vle8_v_i8m1((const signed char *)raptor_base_str, vl), 0, vl), vl)+1);


  CHECK_TRUE(strcmp(raptor_output_str, raptor_base_str) == 0, "String comparison failed: expected 'Hello from Raptor!' but got '%s'", raptor_output_str);

  exit(testcase_finalize());
}
