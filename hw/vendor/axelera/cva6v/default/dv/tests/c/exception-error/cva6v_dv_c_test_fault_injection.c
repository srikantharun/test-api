// This is a test file for fault_injection
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to inject a fault in a register
void inject_register_fault(uint64_t *reg) {
    uint64_t fault_mask = ((uint64_t)1 << (rand() % 64)); // Create a mask to flip a random bit
    *reg ^= fault_mask; // Inject the fault by flipping a bit
}

// Function to inject a fault in memory
void inject_memory_fault(uint64_t *memory, size_t size) {
    size_t fault_address = rand() % size; // Choose a random address in memory
    uint64_t fault_mask = ((uint64_t)1 << (rand() % 64)); // Create a mask to flip a random bit
    memory[fault_address] ^= fault_mask; // Inject the fault by flipping a bit
}

// Function to inject a fault in the bus (simulated as a memory location here)
void inject_bus_fault(uint64_t *bus) {
    uint64_t fault_mask = ((uint64_t)1 << (rand() % 64)); // Create a mask to flip a random bit
    *bus ^= fault_mask; // Inject the fault by flipping a bit
}

// Function to test fault injection
void test_fault_injection() {
    printf("Testing Fault Injection...\n");
    int pass = 1; // Flag to indicate if the test passes

    uint64_t reg = 0xFFFFFFFFFFFFFFFF; // Initialize a register with all bits set
    inject_register_fault(&reg);
    printf("Injected register fault: 0x%016lx\n", reg);

    size_t mem_size = 1024;
    uint64_t *memory = (uint64_t *)malloc(mem_size * sizeof(uint64_t)); // Allocate memory
    if (!memory) {
        printf("Memory allocation failed\n");
        return;
    }
    for (size_t i = 0; i < mem_size; i++) {
        memory[i] = 0xFFFFFFFFFFFFFFFF; // Initialize memory with all bits set
    }
    inject_memory_fault(memory, mem_size);
    printf("Injected memory fault at address %zu: 0x%016lx\n", rand() % mem_size, memory[rand() % mem_size]);

    uint64_t bus = 0xFFFFFFFFFFFFFFFF; // Initialize a bus with all bits set
    inject_bus_fault(&bus);
    printf("Injected bus fault: 0x%016lx\n", bus);

    // Check if any injected faults caused an expected failure
    // Here we assume any deviation from the initial value is a failure for simplicity
    if (reg == 0xFFFFFFFFFFFFFFFF) {
        printf("Register fault injection FAILED\n");
        pass = 0;
    }

    if (bus == 0xFFFFFFFFFFFFFFFF) {
        printf("Bus fault injection FAILED\n");
        pass = 0;
    }

    for (size_t i = 0; i < mem_size; i++) {
        if (memory[i] == 0xFFFFFFFFFFFFFFFF) {
            printf("Memory fault injection FAILED at address %zu\n", i);
            pass = 0;
        }
    }

    if (pass) {
        printf("Fault Injection Test PASSED\n");
    } else {
        printf("Fault Injection Test FAILED\n");
    }

    free(memory); // Free allocated memory
}

int main() {
    printf("Running test: fault_injection\n");
    initialize_registers();
    test_fault_injection();
    return 0;
}
