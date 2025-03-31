// To test a gtihub issue
// Author : Abhilash
#include <common.h>
#include <stdint.h>

// Function prototype for the misaligned jump handler
void handle_misaligned_jump(void);

int main(void) {
    printf("=== RISC-V CVA6 Misaligned Jump Test ===\n");

    // Define the misaligned address (e.g., 0x80000005)
    uintptr_t misaligned_address = 0x80000005;
    void (*misaligned_jump)() = (void (*)())misaligned_address;

    printf("Attempting to jump to misaligned address: 0x%lx\n", misaligned_address);

    // Attempt the misaligned jump using inline assembly
    // This uses the JALR instruction to jump to the specified address
    asm volatile (
        "jalr x0, 0(%1)"        // Jump to the address in register %1 with an offset of 0
        :
        : "r" (misaligned_jump) // Input operand: address to jump to
        : "memory"              // Clobbers
    );

    // If no exception is triggered, the following line will execute
    printf("No exception triggered. Potential CVA6 misaligned fetch exception bug detected.\n");

    return 0;
}


