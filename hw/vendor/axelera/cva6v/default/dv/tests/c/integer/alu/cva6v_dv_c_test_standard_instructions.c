// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Define the number of registers (assuming 32 general-purpose registers)
#define NUM_REGISTERS 32

// Global register array
int64_t registers[NUM_REGISTERS];

// Function prototypes
void coverBaseInstructions(void);
void coverPrivilegedInstructions(void);
void coverAllTrapsAndInterrupts(void);
void coverAllRegisterValues(void);
void coverMemoryOperations(void);

int getRandomRegister(void);
int getRandomImmediate(int bits);
void printRTypeInstruction(const char *name);
void printITypeInstruction(const char *name);
void printSTypeInstruction(const char *name);
void printBTypeInstruction(const char *name);
void printUTypeInstruction(const char *name);
void printJTypeInstruction(const char *name);

void test_trap(void);
void test_interrupt(void);
void test_register_values(void);
void test_memory_operations(void);

void handle_trap(int trap_code);
void handle_interrupt(int interrupt_code);

// Main function
int main(void) {
    srand(get_time()); // Seed the random number generator

    // Cover base instructions
    coverBaseInstructions();

    // Cover privileged instructions
    coverPrivilegedInstructions();

    // Cover traps and interrupts
    coverAllTrapsAndInterrupts();

    // Cover all register values
    coverAllRegisterValues();

    // Cover memory operations
    coverMemoryOperations();

    return 0;
}

void coverBaseInstructions(void) {
    const char *rTypeInstructions[] = {"ADD", "SUB", "SLL", "SLT", "SLTU", "XOR", "SRL", "SRA", "OR", "AND"};
    const char *iTypeInstructions[] = {"ADDI", "SLTI", "SLTIU", "XORI", "ORI", "ANDI", "LB", "LH", "LW", "LBU", "LHU"};
    const char *sTypeInstructions[] = {"SB", "SH", "SW"};
    const char *bTypeInstructions[] = {"BEQ", "BNE", "BLT", "BGE", "BLTU", "BGEU"};
    const char *uTypeInstructions[] = {"LUI", "AUIPC"};
    const char *jTypeInstructions[] = {"JAL", "JALR"};

    for (size_t i = 0; i < sizeof(rTypeInstructions) / sizeof(rTypeInstructions[0]); ++i) {
        printRTypeInstruction(rTypeInstructions[i]);
    }

    for (size_t i = 0; i < sizeof(iTypeInstructions) / sizeof(iTypeInstructions[0]); ++i) {
        printITypeInstruction(iTypeInstructions[i]);
    }

    for (size_t i = 0; i < sizeof(sTypeInstructions) / sizeof(sTypeInstructions[0]); ++i) {
        printSTypeInstruction(sTypeInstructions[i]);
    }

    for (size_t i = 0; i < sizeof(bTypeInstructions) / sizeof(bTypeInstructions[0]); ++i) {
        printBTypeInstruction(bTypeInstructions[i]);
    }

    for (size_t i = 0; i < sizeof(uTypeInstructions) / sizeof(uTypeInstructions[0]); ++i) {
        printUTypeInstruction(uTypeInstructions[i]);
    }

    for (size_t i = 0; i < sizeof(jTypeInstructions) / sizeof(jTypeInstructions[0]); ++i) {
        printJTypeInstruction(jTypeInstructions[i]);
    }
}

void coverPrivilegedInstructions(void) {
    // Add privileged instruction tests here
    // This is an example placeholder, as privileged instructions depend on the specific implementation
    printf("Covering privileged instructions (example placeholder)...\n");
}

void coverAllTrapsAndInterrupts(void) {
    test_trap();
    test_interrupt();
}

void coverAllRegisterValues(void) {
    test_register_values();
}

void coverMemoryOperations(void) {
    test_memory_operations();
}

int getRandomRegister(void) {
    return rand() % NUM_REGISTERS;
}

int getRandomImmediate(int bits) {
    return rand() & ((1 << bits) - 1);
}

void printRTypeInstruction(const char *name) {
    int rd = getRandomRegister();
    int rs1 = getRandomRegister();
    int rs2 = getRandomRegister();
    printf("%s x%d, x%d, x%d\n", name, rd, rs1, rs2);
}

void printITypeInstruction(const char *name) {
    int rd = getRandomRegister();
    int rs1 = getRandomRegister();
    int imm = getRandomImmediate(12);
    printf("%s x%d, x%d, %d\n", name, rd, rs1, imm);
}

void printSTypeInstruction(const char *name) {
    int rs1 = getRandomRegister();
    int rs2 = getRandomRegister();
    int imm = getRandomImmediate(12);
    printf("%s x%d, %d(x%d)\n", name, rs2, imm, rs1);
}

void printBTypeInstruction(const char *name) {
    int rs1 = getRandomRegister();
    int rs2 = getRandomRegister();
    int imm = getRandomImmediate(13);
    printf("%s x%d, x%d, %d\n", name, rs1, rs2, imm);
}

void printUTypeInstruction(const char *name) {
    int rd = getRandomRegister();
    int imm = getRandomImmediate(20);
    printf("%s x%d, %d\n", name, rd, imm);
}

void printJTypeInstruction(const char *name) {
    int rd = getRandomRegister();
    int imm = getRandomImmediate(21);
    printf("%s x%d, %d\n", name, rd, imm);
}

void test_trap(void) {
    printf("Testing traps...\n");

    // Example: Division by zero trap
    int rs1 = getRandomRegister();
    int rs2 = getRandomRegister();
    registers[rs1] = rand();
    registers[rs2] = 0;

    printf("Division by zero trap with x%d / x%d\n", rs1, rs2);

    // This should trigger a trap for division by zero
    if (registers[rs2] == 0) {
        handle_trap(1); // Trap code 1 for division by zero
    }
}

void test_interrupt(void) {
    printf("Testing interrupts...\n");

    // Example: Timer interrupt
    int interrupt_code = 2; // Interrupt code 2 for timer interrupt
    handle_interrupt(interrupt_code);
}

void handle_trap(int trap_code) {
    printf("Handling trap with code %d\n", trap_code);

    // Implement trap handling logic here
    switch (trap_code) {
        case 1:
            printf("Trap: Division by zero\n");
            // Handle division by zero trap
            break;
        // Add more cases for other trap codes
        default:
            printf("Unknown trap code: %d\n", trap_code);
            break;
    }
}

void handle_interrupt(int interrupt_code) {
    printf("Handling interrupt with code %d\n", interrupt_code);

    // Implement interrupt handling logic here
    switch (interrupt_code) {
        case 2:
            printf("Interrupt: Timer\n");
            // Handle timer interrupt
            break;
        // Add more cases for other interrupt codes
        default:
            printf("Unknown interrupt code: %d\n", interrupt_code);
            break;
    }
}

void test_register_values(void) {
    // Test all register values
    for (int i = 0; i < NUM_REGISTERS; i++) {
        registers[i] = i;
        printf("Register x%d set to %ld\n", i, registers[i]);
    }
}

void test_memory_operations(void) {
    // Add memory operation tests here
    // This is an example placeholder
    printf("Testing memory operations (example placeholder)...\n");
}
