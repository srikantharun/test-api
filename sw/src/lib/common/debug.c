#include <stdint.h>

#include <debug.h>
#include <printf.h>

#define NUM_REGS 32

void debug_dump_registers_impl(uint64_t registers[NUM_REGS]) {
    printf("=== BEGIN REGISTER DUMP ===\r\n");
    for (size_t i = 0; i < NUM_REGS; i++) {
        uint64_t hi = registers[i] >> 32;
        uint64_t lo = registers[i] & ((1ULL << 32) - 1);
        printf("  reg %2d:  0x%08lx %08lx (%lld)\r\n", i, hi, lo, registers[i]);
    }
    printf("=== END REGISTER DUMP ===\r\n");
}

__attribute__((naked)) void debug_dump_registers() {
    asm volatile (
        "addi sp, sp, -256\n"
        "sd  x0,   0(sp)\n"
        "sd  x1,   8(sp)\n"
        "sd  x2,  16(sp)\n"
        "sd  x3,  24(sp)\n"
        "sd  x4,  32(sp)\n"
        "sd  x5,  40(sp)\n"
        "sd  x6,  48(sp)\n"
        "sd  x7,  56(sp)\n"
        "sd  x8,  64(sp)\n"
        "sd  x9,  72(sp)\n"
        "sd x10,  80(sp)\n"
        "sd x11,  88(sp)\n"
        "sd x12,  96(sp)\n"
        "sd x13, 104(sp)\n"
        "sd x14, 112(sp)\n"
        "sd x15, 120(sp)\n"
        "sd x16, 128(sp)\n"
        "sd x17, 136(sp)\n"
        "sd x18, 144(sp)\n"
        "sd x19, 152(sp)\n"
        "sd x20, 160(sp)\n"
        "sd x21, 168(sp)\n"
        "sd x22, 176(sp)\n"
        "sd x23, 184(sp)\n"
        "sd x24, 192(sp)\n"
        "sd x25, 200(sp)\n"
        "sd x26, 208(sp)\n"
        "sd x27, 216(sp)\n"
        "sd x28, 224(sp)\n"
        "sd x29, 232(sp)\n"
        "sd x30, 240(sp)\n"
        "sd x31, 248(sp)\n"

        "mv a0, sp\n"
        "jal ra, debug_dump_registers_impl\n"

        // skipping x0 (zero)
        "ld  x1,   8(sp)\n"
        "ld  x2,  16(sp)\n"
        "ld  x3,  24(sp)\n"
        "ld  x4,  32(sp)\n"
        "ld  x5,  40(sp)\n"
        "ld  x6,  48(sp)\n"
        "ld  x7,  56(sp)\n"
        "ld  x8,  64(sp)\n"
        "ld  x9,  72(sp)\n"
        "ld x10,  80(sp)\n"
        "ld x11,  88(sp)\n"
        "ld x12,  96(sp)\n"
        "ld x13, 104(sp)\n"
        "ld x14, 112(sp)\n"
        "ld x15, 120(sp)\n"
        "ld x16, 128(sp)\n"
        "ld x17, 136(sp)\n"
        "ld x18, 144(sp)\n"
        "ld x19, 152(sp)\n"
        "ld x20, 160(sp)\n"
        "ld x21, 168(sp)\n"
        "ld x22, 176(sp)\n"
        "ld x23, 184(sp)\n"
        "ld x24, 192(sp)\n"
        "ld x25, 200(sp)\n"
        "ld x26, 208(sp)\n"
        "ld x27, 216(sp)\n"
        "ld x28, 224(sp)\n"
        "ld x29, 232(sp)\n"
        "ld x30, 240(sp)\n"
        "ld x31, 248(sp)\n"
        "addi sp, sp, 256\n"
        "ret\n"
    );
}
