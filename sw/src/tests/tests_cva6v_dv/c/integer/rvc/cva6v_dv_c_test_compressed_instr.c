// This is a test file for compressed_instr
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Function to test various RISC-V compressed instructions
void test_compressed_instr() {
    int32_t result, expected;

    // Test c.add (compressed add)
    int32_t c_add_a = rand() % 32;
    int32_t c_add_b = rand() % 32;
    __asm__ volatile("c.add %0, %1" : "=r"(result) : "r"(c_add_a), "r"(c_add_b));
    expected = c_add_a + c_add_b;
    printf("c.add: %d + %d = %d, Expected: %d %s\n", c_add_a, c_add_b, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.addi (compressed add immediate)
    int32_t c_addi_a = rand() % 32;
    int32_t c_addi_imm = rand() % 32;
    __asm__ volatile("c.addi %0, %1, %2" : "=r"(result) : "r"(c_addi_a), "I"(c_addi_imm));
    expected = c_addi_a + c_addi_imm;
    printf("c.addi: %d + %d = %d, Expected: %d %s\n", c_addi_a, c_addi_imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.and (compressed and)
    int32_t c_and_a = rand() % 32;
    int32_t c_and_b = rand() % 32;
    __asm__ volatile("c.and %0, %1" : "=r"(result) : "r"(c_and_a), "r"(c_and_b));
    expected = c_and_a & c_and_b;
    printf("c.and: %d & %d = %d, Expected: %d %s\n", c_and_a, c_and_b, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.beqz (compressed branch if equal to zero)
    int32_t c_beqz_a = rand() % 32;
    int32_t c_beqz_imm = rand() % 32;
    __asm__ volatile("c.beqz %1, %2\n\tc.addi %0, zero, 1" : "=r"(result) : "r"(c_beqz_a), "I"(c_beqz_imm) : "cc");
    expected = (c_beqz_a == 0) ? 1 : 0;
    printf("c.beqz: beqz %d, %d = %d, Expected: %d %s\n", c_beqz_a, c_beqz_imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.bnez (compressed branch if not equal to zero)
    int32_t c_bnez_a = rand() % 32;
    int32_t c_bnez_imm = rand() % 32;
    __asm__ volatile("c.bnez %1, %2\n\tc.addi %0, zero, 1" : "=r"(result) : "r"(c_bnez_a), "I"(c_bnez_imm) : "cc");
    expected = (c_bnez_a != 0) ? 1 : 0;
    printf("c.bnez: bnez %d, %d = %d, Expected: %d %s\n", c_bnez_a, c_bnez_imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.ebreak (compressed ebreak)
    __asm__ volatile("c.ebreak" : "=r"(result));
    printf("c.ebreak: Triggered\n");

    // Test c.j (compressed jump)
    int32_t c_j_imm = rand() % 32;
    __asm__ volatile("c.j %1\n\tc.addi %0, zero, 1" : "=r"(result) : "I"(c_j_imm));
    printf("c.j: jump to %d\n", c_j_imm);

    // Test c.jal (compressed jump and link)
    int32_t c_jal_imm = rand() % 32;
    __asm__ volatile("c.jal %1\n\tc.addi %0, zero, 1" : "=r"(result) : "I"(c_jal_imm));
    printf("c.jal: jump and link to %d\n", c_jal_imm);

    // Test c.jr (compressed jump register)
    int32_t c_jr_a = rand() % 32;
    __asm__ volatile("c.jr %1\n\tc.addi %0, zero, 1" : "=r"(result) : "r"(c_jr_a));
    printf("c.jr: jump register to %d\n", c_jr_a);

    // Test c.ld (compressed load double)
    int64_t* c_ld_ptr = (int64_t*)(rand() % 32);
    int64_t c_ld_val = rand();
    *c_ld_ptr = c_ld_val;
    __asm__ volatile("c.ld %0, 0(%1)" : "=r"(result) : "r"(c_ld_ptr));
    expected = *c_ld_ptr;
    printf("c.ld: ld from %p = %ld, Expected: %ld %s\n", c_ld_ptr, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.lw (compressed load word)
    int32_t* c_lw_ptr = (int32_t*)(rand() % 32);
    int32_t c_lw_val = rand();
    *c_lw_ptr = c_lw_val;
    __asm__ volatile("c.lw %0, 0(%1)" : "=r"(result) : "r"(c_lw_ptr));
    expected = *c_lw_ptr;
    printf("c.lw: lw from %p = %d, Expected: %d %s\n", c_lw_ptr, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.li (compressed load immediate)
    int32_t c_li_imm = rand() % 32;
    __asm__ volatile("c.li %0, %1" : "=r"(result) : "I"(c_li_imm));
    expected = c_li_imm;
    printf("c.li: li %d = %d, Expected: %d %s\n", c_li_imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.lui (compressed load upper immediate)
    int32_t c_lui_imm = rand() % 32;
    __asm__ volatile("c.lui %0, %1" : "=r"(result) : "I"(c_lui_imm));
    expected = c_lui_imm << 12;
    printf("c.lui: lui %d = %d, Expected: %d %s\n", c_lui_imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.mv (compressed move)
    int32_t c_mv_a = rand() % 32;
    __asm__ volatile("c.mv %0, %1" : "=r"(result) : "r"(c_mv_a));
    expected = c_mv_a;
    printf("c.mv: mv %d = %d, Expected: %d %s\n", c_mv_a, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.sd (compressed store double)
    int64_t c_sd_val = rand();
    int64_t* c_sd_ptr = (int64_t*)(rand() % 32);
    __asm__ volatile("c.sd %1, 0(%2)" : : "r"(c_sd_val), "r"(c_sd_ptr));
    expected = *c_sd_ptr;
    printf("c.sd: sd %ld to %p, Expected: %ld %s\n", c_sd_val, c_sd_ptr, expected, *c_sd_ptr == expected ? "PASS" : "FAIL");

    // Test c.sw (compressed store word)
    int32_t c_sw_val = rand();
    int32_t* c_sw_ptr = (int32_t*)(rand() % 32);
    __asm__ volatile("c.sw %1, 0(%2)" : : "r"(c_sw_val), "r"(c_sw_ptr));
    expected = *c_sw_ptr;
    printf("c.sw: sw %d to %p, Expected: %d %s\n", c_sw_val, c_sw_ptr, expected, *c_sw_ptr == expected ? "PASS" : "FAIL");

    // Test c.sub (compressed subtract)
    int32_t c_sub_a = rand() % 32;
    int32_t c_sub_b = rand() % 32;
    __asm__ volatile("c.sub %0, %1" : "=r"(result) : "r"(c_sub_a), "r"(c_sub_b));
    expected = c_sub_a - c_sub_b;
    printf("c.sub: %d - %d = %d, Expected: %d %s\n", c_sub_a, c_sub_b, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.xor (compressed xor)
    int32_t c_xor_a = rand() % 32;
    int32_t c_xor_b = rand() % 32;
    __asm__ volatile("c.xor %0, %1" : "=r"(result) : "r"(c_xor_a), "r"(c_xor_b));
    expected = c_xor_a ^ c_xor_b;
    printf("c.xor: %d ^ %d = %d, Expected: %d %s\n", c_xor_a, c_xor_b, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.or (compressed or)
    int32_t c_or_a = rand() % 32;
    int32_t c_or_b = rand() % 32;
    __asm__ volatile("c.or %0, %1" : "=r"(result) : "r"(c_or_a), "r"(c_or_b));
    expected = c_or_a | c_or_b;
    printf("c.or: %d | %d = %d, Expected: %d %s\n", c_or_a, c_or_b, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.nop (compressed no operation)
    __asm__ volatile("c.nop");
    printf("c.nop: No operation performed\n");

    // Test c.srli (compressed shift right logical immediate)
    int32_t c_srli_a = rand() % 32;
    int32_t c_srli_imm = rand() % 32;
    __asm__ volatile("c.srli %0, %1, %2" : "=r"(result) : "r"(c_srli_a), "I"(c_srli_imm));
    expected = c_srli_a >> c_srli_imm;
    printf("c.srli: %d >> %d = %d, Expected: %d %s\n", c_srli_a, c_srli_imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.srai (compressed shift right arithmetic immediate)
    int32_t c_srai_a = rand() % 32;
    int32_t c_srai_imm = rand() % 32;
    __asm__ volatile("c.srai %0, %1, %2" : "=r"(result) : "r"(c_srai_a), "I"(c_srai_imm));
    expected = c_srai_a >> c_srai_imm;
    printf("c.srai: %d >> %d = %d, Expected: %d %s\n", c_srai_a, c_srai_imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.andi (compressed and immediate)
    int32_t c_andi_a = rand() % 32;
    int32_t c_andi_imm = rand() % 32;
    __asm__ volatile("c.andi %0, %1, %2" : "=r"(result) : "r"(c_andi_a), "I"(c_andi_imm));
    expected = c_andi_a & c_andi_imm;
    printf("c.andi: %d & %d = %d, Expected: %d %s\n", c_andi_a, c_andi_imm, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.lwsp (compressed load word from stack pointer)
    int32_t* c_lwsp_ptr = (int32_t*)(rand() % 32);
    int32_t c_lwsp_val = rand();
    *c_lwsp_ptr = c_lwsp_val;
    __asm__ volatile("c.lwsp %0, 0(%1)" : "=r"(result) : "r"(c_lwsp_ptr));
    expected = *c_lwsp_ptr;
    printf("c.lwsp: lwsp from %p = %d, Expected: %d %s\n", c_lwsp_ptr, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.flw (compressed load floating-point word)
    float* c_flw_ptr = (float*)(rand() % 32);
    float c_flw_val = (float)rand();
    *c_flw_ptr = c_flw_val;
    __asm__ volatile("c.flw %0, 0(%1)" : "=f"(result) : "r"(c_flw_ptr));
    expected = *c_flw_ptr;
    printf("c.flw: flw from %p = %f, Expected: %f %s\n", c_flw_ptr, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.flwsp (compressed load floating-point word from stack pointer)
    float* c_flwsp_ptr = (float*)(rand() % 32);
    float c_flwsp_val = (float)rand();
    *c_flwsp_ptr = c_flwsp_val;
    __asm__ volatile("c.flwsp %0, 0(%1)" : "=f"(result) : "r"(c_flwsp_ptr));
    expected = *c_flwsp_ptr;
    printf("c.flwsp: flwsp from %p = %f, Expected: %f %s\n", c_flwsp_ptr, result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.fsd (compressed store floating-point double)
    double c_fsd_val = (double)rand();
    double* c_fsd_ptr = (double*)(rand() % 32);
    __asm__ volatile("c.fsd %1, 0(%2)" : : "f"(c_fsd_val), "r"(c_fsd_ptr));
    expected = *c_fsd_ptr;
    printf("c.fsd: fsd %lf to %p, Expected: %lf %s\n", c_fsd_val, c_fsd_ptr, expected, *c_fsd_ptr == expected ? "PASS" : "FAIL");

    // Test c.fsdsp (compressed store floating-point double from stack pointer)
    double c_fsdsp_val = (double)rand();
    double* c_fsdsp_ptr = (double*)(rand() % 32);
    __asm__ volatile("c.fsdsp %1, 0(%2)" : : "f"(c_fsdsp_val), "r"(c_fsdsp_ptr));
    expected = *c_fsdsp_ptr;
    printf("c.fsdsp: fsdsp %lf to %p, Expected: %lf %s\n", c_fsdsp_val, c_fsdsp_ptr, expected, *c_fsdsp_ptr == expected ? "PASS" : "FAIL");

    // Test c.fsw (compressed store floating-point word)
    float c_fsw_val = (float)rand();
    float* c_fsw_ptr = (float*)(rand() % 32);
    __asm__ volatile("c.fsw %1, 0(%2)" : : "f"(c_fsw_val), "r"(c_fsw_ptr));
    expected = *c_fsw_ptr;
    printf("c.fsw: fsw %f to %p, Expected: %f %s\n", c_fsw_val, c_fsw_ptr, expected, *c_fsw_ptr == expected ? "PASS" : "FAIL");

    // Test c.fswsp (compressed store floating-point word from stack pointer)
    float c_fswsp_val = (float)rand();
    float* c_fswsp_ptr = (float*)(rand() % 32);
    __asm__ volatile("c.fswsp %1, 0(%2)" : : "f"(c_fswsp_val), "r"(c_fswsp_ptr));
    expected = *c_fswsp_ptr;
    printf("c.fswsp: fswsp %f to %p, Expected: %f %s\n", c_fswsp_val, c_fswsp_ptr, expected, *c_fswsp_ptr == expected ? "PASS" : "FAIL");
}

int main() {
    printf("Running test: compressed_instr\n");
    initialize_registers();
    test_compressed_instr();
    return 0;
}
