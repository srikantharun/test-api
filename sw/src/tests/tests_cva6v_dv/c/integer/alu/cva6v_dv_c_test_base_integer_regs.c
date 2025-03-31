// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"


// Define the number of registers (assuming 32 general-purpose registers)
#define NUM_REGISTERS 32

// Global register array
int64_t registers[NUM_REGISTERS];

// Function prototypes
void printf(const char *str);
void initialize_registers();
void print_registers();
void test_arithmetic_operations();
void test_logical_operations();
void test_shift_operations();
void test_bitwise_operations();
void test_random_operations();
void test_complex_patterns();
void test_branching_and_loops();
void test_memory_access_patterns();
void test_pipelining_and_hazards();
void test_nested_loops_and_conditionals();

// Main function
int main() {
    printf("Initializing Registers...\n");
    initialize_registers();
    print_registers();

    test_arithmetic_operations();
    test_logical_operations();
    test_shift_operations();
    test_bitwise_operations();
    test_random_operations();
    test_complex_patterns();
    test_branching_and_loops();
    test_memory_access_patterns();
    test_pipelining_and_hazards();
    test_nested_loops_and_conditionals();

    printf("Final Register State:\n");
    print_registers();

    return 0;
}


void initialize_registers() {
    for (int i = 0; i < NUM_REGISTERS; i++) {
        registers[i] = i + 1;  // Initialize registers with values 1, 2, 3, ..., 32
    }
}

void print_registers() {
    for (int i = 0; i < NUM_REGISTERS; i++) {
        printf("x%d: 0x%lx\n", i, registers[i]);
    }
}

void test_arithmetic_operations() {
    for (int rd = 0; rd < NUM_REGISTERS; rd++) {
        for (int rs1 = 0; rs1 < NUM_REGISTERS; rs1++) {
            for (int rs2 = 0; rs2 < NUM_REGISTERS; rs2++) {
                registers[rd] = registers[rs1] + registers[rs2];
                registers[rd] = registers[rs1] - registers[rs2];
                registers[rd] = registers[rs1] * registers[rs2];
                if (registers[rs2] != 0) {
                    registers[rd] = registers[rs1] / registers[rs2];
                    registers[rd] = registers[rs1] % registers[rs2];
                }
            }
        }
    }
}

void test_logical_operations() {
    for (int rd = 0; rd < NUM_REGISTERS; rd++) {
        for (int rs1 = 0; rs1 < NUM_REGISTERS; rs1++) {
            for (int rs2 = 0; rs2 < NUM_REGISTERS; rs2++) {
                registers[rd] = registers[rs1] & registers[rs2];
                registers[rd] = registers[rs1] | registers[rs2];
                registers[rd] = registers[rs1] ^ registers[rs2];
            }
        }
    }
}

void test_shift_operations() {
    for (int rd = 0; rd < NUM_REGISTERS; rd++) {
        for (int rs1 = 0; rs1 < NUM_REGISTERS; rs1++) {
            for (int rs2 = 0; rs2 < NUM_REGISTERS; rs2++) {
                registers[rd] = registers[rs1] << (registers[rs2] % 64);
                registers[rd] = registers[rs1] >> (registers[rs2] % 64);
            }
        }
    }
}

void test_bitwise_operations() {
    for (int rd = 0; rd < NUM_REGISTERS; rd++) {
        for (int rs1 = 0; rs1 < NUM_REGISTERS; rs1++) {
            registers[rd] = ~registers[rs1];
        }
    }
}

void test_random_operations() {
    // Initialize the random number generator
    srand(get_time());

    // Test random combinations of operations
    for (int i = 0; i < 100; i++) {
        int rd = rand() % NUM_REGISTERS;
        int rs1 = rand() % NUM_REGISTERS;
        int rs2 = rand() % NUM_REGISTERS;
        int operation = rand() % 10;

        switch (operation) {
            case 0: registers[rd] = registers[rs1] + registers[rs2]; break;
            case 1: registers[rd] = registers[rs1] - registers[rs2]; break;
            case 2: registers[rd] = registers[rs1] * registers[rs2]; break;
            case 3: if (registers[rs2] != 0) registers[rd] = registers[rs1] / registers[rs2]; break;
            case 4: if (registers[rs2] != 0) registers[rd] = registers[rs1] % registers[rs2]; break;
            case 5: registers[rd] = registers[rs1] & registers[rs2]; break;
            case 6: registers[rd] = registers[rs1] | registers[rs2]; break;
            case 7: registers[rd] = registers[rs1] ^ registers[rs2]; break;
            case 8: registers[rd] = registers[rs1] << (registers[rs2] % 64); break;
            case 9: registers[rd] = registers[rs1] >> (registers[rs2] % 64); break;
        }
    }
}

void test_complex_patterns() {
    // Implement complex patterns to test ALU behavior
    for (int i = 0; i < NUM_REGISTERS; i++) {
        for (int j = 0; j < NUM_REGISTERS; j++) {
            registers[i] += registers[j] * 2;
            registers[i] -= (registers[j] << 1) / 3;
        }
    }
}

void test_branching_and_loops() {
    for (int i = 0; i < NUM_REGISTERS; i++) {
        for (int j = 0; j < NUM_REGISTERS; j++) {
            if (registers[j] % 2 == 0) {
                registers[i] += registers[j];
            } else {
                registers[i] -= registers[j];
            }
        }
    }
}

void test_memory_access_patterns() {
    // Assuming memory access simulation functions are available
    int64_t memory[NUM_REGISTERS];
    for (int i = 0; i < NUM_REGISTERS; i++) {
        memory[i] = registers[i];
    }
    for (int i = 0; i < NUM_REGISTERS; i++) {
        registers[i] = memory[i];
    }
}

void test_pipelining_and_hazards() {
    // Simulate pipelining and hazards by introducing dependencies
    for (int i = 1; i < NUM_REGISTERS; i++) {
        registers[i] = registers[i-1] + 1;
        registers[i-1] = registers[i] - 1;
    }
}

void test_nested_loops_and_conditionals() {
    for (int i = 0; i < NUM_REGISTERS / 2; i++) {
        for (int j = i; j < NUM_REGISTERS - i; j++) {
            if (registers[j] % 3 == 0) {
                registers[j] += registers[i];
            } else {
                registers[j] -= registers[i];
            }
        }
    }
}
