// Common header file content
// Author: Abhilash Chadhar

#ifndef COMMON_H
#define COMMON_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdarg.h>  // For va_list, va_start, and va_end in printf
#include <printf.h>
#include <string.h>
#include <math.h>    // Include math.h for expected results
#include <signal.h>
#include <unistd.h>
#include <fcntl.h>   // For open()
#include <errno.h>   // For errno
#include <encoding.h>   // For encoding-related definitions
#include "stack.h"
#include "testutils.h"
// Constants for mathematical calculations
#define FLOAT_TOLERANCE 0.000001f        // Tolerance for floating-point comparison
#define HALF_FLOAT_TOLERANCE 0.0001f     // Tolerance for half-precision comparison

// Special floating-point values
#define POS_INFINITY 0x7F800000U
#define NEG_INFINITY 0xFF800000U
#define NAN_VALUE 0x7FC00000U

// Define bit masks and helper macros
#define SEW_32         (2 << 0)  // SEW = 32 bits (e32)
#define LMUL_1         (0 << 3)  // LMUL = 1 (m1)
#define VSETVLI_IMM    (SEW_32 | LMUL_1)

#define MSTATUS_MPP_SHIFT      11
#define MSTATUS_MPP_MASK       (0x3 << MSTATUS_MPP_SHIFT)
#define MSTATUS_MPP_MACHINE    (0x3 << MSTATUS_MPP_SHIFT) // 11 for Machine mode

#define MSTATUS_XS_SHIFT       14
#define MSTATUS_XS_MASK        (0x3 << MSTATUS_XS_SHIFT)
#define MSTATUS_XS_V           (0x1 << MSTATUS_XS_SHIFT) // Enable Vector Extension

// Define CSR addresses and bit masks
#define MSTATUS_MPP_M       (3 << 11)  // 0x1800
#define MSTATUS_MPP_S       (1 << 11)  // 0x0800
#define MSTATUS_MPP_U       (0 << 11)  // 0x0000

#define SSTATUS_SPP_MASK    (1 << 8)   // 0x0100
#define SSTATUS_SPP_S       (1 << 8)   // 0x0100
#define SSTATUS_SPP_U       (0 << 8)   // 0x0000
// Mathematical constants
const float pi = 3.1415926535897932384626433832795f;
const float twopi = 6.283185307179586476925286766559f;
const float piover2 = 1.5707963267948966192313216916398f;
const float piover4 = 0.78539816339744830961566084581988f;
const float fouroverpi = 1.2732395447351626861510701069801f;
const float half_pi = 1.5707963267948966192313216916398f;

// Cache and memory management
#define CACHE_SIZE 64
#define MEMORY_POOL_SIZE 1024

// Utility macros for printing results in a formatted manner
#define PRINT_HEADER() \
    printf("\n%-100s %-25s %-25s %-10s\n", "Scenario", "dest_val", "expected", "Result");

#define PRINT_RESULT(scenario, dest_val_str, expected_str, result) \
    printf("%-100s %-25s %-25s %-10s\n", scenario, dest_val_str, expected_str, result)

#define PRINT_LOAD_STORE_RESULT(idx, scenario, original_val, stored_val, result) \
    do {                                                                         \
        char original_str[25], stored_str[25];                                   \
        float_to_str(original_val, original_str, 6);                             \
        float_to_str(stored_val, stored_str, 6);                                 \
        printf("%-100s %-25s %-25s %-10s\n", scenario, original_str, stored_str, result); \
    } while(0)

/* Macro to mark a variable as used to prevent compiler warnings */
#define MARK_USED(x) ((void)(x))

// Simulated cache and interrupt handling
uint64_t cache[CACHE_SIZE];
volatile uint32_t interrupt_handled = 0;
uint64_t expected_tval;                              // Expected tval register value after trap
int trap_occurred = 0;                                // Trap flag to check if a trap occurred
static int trap_count = 0;
// Seed for random number generation
static uint32_t seed = 1;

// Function Prototypes
__attribute__((section(".text"), aligned(64))) float round_float_to_n(float a, int n);
__attribute__((section(".text"), aligned(64))) float get_special_value(uint32_t value);
__attribute__((section(".text"), aligned(64))) void print_float(float num, int n);
__attribute__((section(".text"), aligned(64))) void int_to_str(int num, char *str);
__attribute__((section(".text"), aligned(64))) void float_to_str(float num, char *str, int precision);
__attribute__((section(".text"), aligned(64))) float half_to_float(uint16_t h);
__attribute__((section(".text"), aligned(64))) void half_float_to_str(uint16_t half, char *str, int precision);
__attribute__((section(".text"), aligned(64))) void str_append(char *dest, const char *src);
__attribute__((section(".text"), aligned(64))) void srand(uint32_t new_seed);
__attribute__((section(".text"), aligned(64))) uint32_t rand(void);
__attribute__((section(".text"), aligned(64))) uint16_t rand_half_float(void);
__attribute__((section(".text"), aligned(64))) uint32_t get_time(void);
__attribute__((section(".text"), aligned(64))) void trap_handler(void) __attribute__((interrupt, aligned(64)));
__attribute__((section(".text"), aligned(64))) void setup_trap_handler(void);
__attribute__((section(".text"), aligned(64))) void initialize_registers(void);
__attribute__((section(".text"), aligned(64))) uint32_t float_to_uint32(float f);
__attribute__((section(".text"), aligned(64))) uint32_t float_to_bits(float f);
__attribute__((section(".text"), aligned(64))) void int_to_hex(uint32_t value, char *output);
__attribute__((section(".text"), aligned(64))) int atoi(const char *str);
__attribute__((section(".text"), aligned(64))) float aint(float x);
__attribute__((section(".text"), aligned(64))) float fabsf(float x);
__attribute__((section(".text"), aligned(64))) float sqrtf(float number);
__attribute__((section(".text"), aligned(64))) float atanf(float x);
__attribute__((section(".text"), aligned(64))) float atan2f(float y, float x);
__attribute__((section(".text"), aligned(64))) void error(const char *message);
__attribute__((section(".text"), aligned(64))) float asinf(float x);
__attribute__((section(".text"), aligned(64))) void memory_init(void);
__attribute__((section(".text"), aligned(64))) char *farmalloc(long s);
__attribute__((section(".text"), aligned(64))) void free(void *ptr);
__attribute__((section(".text"), aligned(64))) char *fgets(char *buffer, int size);
__attribute__((section(".text"), aligned(64))) void terminate(void);





// Round a float to n decimal places
__attribute__((unused, noinline))
float round_float_to_n(float a, int n) {
    float scale = powf(10, n);
    return roundf(a * scale) / scale;
}

// Convert uint32_t to float
float get_special_value(uint32_t value) {
    float result;
    memcpy(&result, &value, sizeof(result));
    return result;
}

// Print float with specified decimal places
void print_float(float num, int n) {
    float    rnum         = round_float_to_n(num, n);
    float    scale_float  = powf(10, n);
    uint32_t scale_int    = (uint32_t)scale_float;
    float    scaled_float = rnum*scale_float;
    uint32_t scaled_int   = (uint32_t)(scaled_float);

    printf("%0d.%0*d", (uint32_t)(num), n, (uint32_t)(scaled_int%scale_int));
}

// Convert integer to string
void int_to_str(int num, char *str) {
    int i = 0, sign = num;
    char temp;

    if (sign < 0) num = -num;

    // Generate digits in reverse order
    do {
        str[i++] = num % 10 + '0';
    } while ((num /= 10) > 0);

    if (sign < 0) str[i++] = '-';

    str[i] = '\0';

    // Reverse the string
    for (int j = 0, k = i - 1; j < k; j++, k--) {
        temp = str[j];
        str[j] = str[k];
        str[k] = temp;
    }
}


// Function to convert uint64_t to a string representation
void uint64_to_str(uint64_t value, char *buffer) {
    char temp[21]; // Temporary buffer to hold digits in reverse order
    int index = 0;

    // Handle the special case when the value is zero
    if (value == 0) {
        buffer[0] = '0';
        buffer[1] = '\0';
        return;
    }

    // Extract digits and store them in reverse order
    while (value > 0) {
        temp[index++] = '0' + (value % 10); // Convert digit to character
        value /= 10;
    }

    // Reverse the order of digits and copy to the output buffer
    for (int i = 0; i < index; i++) {
        buffer[i] = temp[index - i - 1];
    }

    // Null-terminate the string
    buffer[index] = '\0';
}

// Convert float to string with fixed precision
void float_to_str(float num, char *str, int precision) {
    if (num < 0) {
        *str++ = '-';
        num = -num;
    }

    int int_part = (int)num;
    float frac_part = num - (float)int_part;
    char int_str[20];
    char frac_str[20];
    int i;

    // Convert integer part
    int_to_str(int_part, int_str);

    // Convert fractional part
    for (i = 0; i < precision; i++) {
        frac_part *= 10;
    }
    int frac_int = (int)frac_part;
    int_to_str(frac_int, frac_str);

    // Copy integer part
    strcpy(str, int_str);

    // Append decimal point
    str += strlen(int_str);
    *str++ = '.';

    // Add leading zeros to fractional part if necessary
    int frac_len = strlen(frac_str);
    for (i = 0; i < precision - frac_len; i++) {
        *str++ = '0';
    }

    // Copy fractional part
    strcpy(str, frac_str);
}

// Convert half-precision float to single-precision float
float half_to_float(uint16_t h) {
    // Extract sign, exponent, and mantissa from the half-precision float
    uint16_t sign = (h >> 15) & 0x1;
    uint16_t exponent = (h >> 10) & 0x1F;
    uint16_t mantissa = h & 0x3FF;

    // Handle special cases
    if (exponent == 0) {
        if (mantissa == 0) {
            // Zero (both +0 and -0)
            return sign ? -0.0f : 0.0f;
        } else {
            // Subnormal numbers
            return ldexpf(mantissa * powf(2, -10), -14) * (sign ? -1.0f : 1.0f);
            //return ldexpf(mantissa, -24) * (sign ? -1.0f : 1.0f);
        }
    } else if (exponent == 31) {
        // Inf or NaN
        if (mantissa == 0) {
            return get_special_value(sign ? NEG_INFINITY : POS_INFINITY);
        } else {
            return get_special_value(NAN_VALUE); // NaN (regardless of sign)
        }
    }

    // Normalized numbers
    float result = ldexpf(mantissa / 1024.0f + 1.0f, exponent - 15);
    return sign ? -result : result;
}

// Convert half-precision float to string with specified precision
void half_float_to_str(uint16_t half, char *str, int precision) {
    // Convert the half-precision float to single-precision float
    float num = half_to_float(half);

    // Handle negative numbers
    if (num < 0) {
        *str++ = '-';
        num = -num;
    }

    // Integer and fractional parts
    int int_part = (int)num;
    float frac_part = num - (float)int_part;
    char int_str[20];
    char frac_str[20];
    int i;

    // Convert integer part
    int_to_str(int_part, int_str);

    // Convert fractional part
    for (i = 0; i < precision; i++) {
        frac_part *= 10;
    }
    int frac_int = (int)(frac_part + 0.5f); // Round the fractional part
    sprintf(frac_str, "%d", frac_int);

    // Copy integer part to the final string
    strcpy(str, int_str);

    // Move the pointer forward for appending the fractional part
    str += strlen(int_str);

    // Add decimal point
    *str++ = '.';

    // Add leading zeros to fractional part if necessary
    int frac_len = strlen(frac_str);
    for (i = 0; i < precision - frac_len; i++) {
        *str++ = '0';
    }

    // Copy fractional part to the final string
    strcpy(str, frac_str);
}

// Append src string to dest string
void str_append(char *dest, const char *src) {
    while (*src) {
        *dest = *src;
        dest++;
        src++;
    }
}
// Function to concatenate two strings
char* strcat(char* destination, const char* source) {
    // Find the end of the destination string
    char* ptr = destination + strlen(destination);

    // Append source to the destination
    while (*source != '\0') {
        *ptr++ = *source++;
    }

    // Null-terminate the destination string
    *ptr = '\0';

    return destination;
}
// Seed random number generator
void srand(uint32_t new_seed) {
    seed = new_seed;
}

// Generate random number
uint32_t rand(void) {
    seed = seed * 1103515245 + 12345;
    return (seed / 65536) % 32768;
}

// Generate random half-precision floating-point value
uint16_t rand_half_float() {
    uint32_t rand_value = rand();
    uint16_t sign = (rand_value >> 15) & 0x1;            // 1-bit sign
    uint16_t exponent = (rand_value >> 10) & 0x1F;       // 5-bit exponent
    uint16_t fraction = rand_value & 0x3FF;              // 10-bit fraction

    uint16_t half_float = (sign << 15) | (exponent << 10) | fraction;
    return half_float;
}

// Get current time (RISC-V specific)
uint32_t get_time(void) {
    uint32_t val;
    asm volatile ("rdtime %0" : "=r"(val));
    return val;
}


// Function to set an instruction breakpoint at a specific address
void set_instruction_breakpoint(uint64_t *addr) {
    asm volatile("csrw mtvec, %0" : : "r"(trap_handler));  // Set the trap handler
    asm volatile("csrw mstatus, %0" : : "r"(0x8));         // Set MIE (Machine Interrupt Enable)
    asm volatile("csrw mie, %0" : : "r"(0x800));           // Enable machine-mode software interrupt

    expected_tval = (uint64_t)addr;  // Set expected tval for breakpoint

    // Set the breakpoint at the desired address
    asm volatile("csrw tdata1, %0" : : "r"(addr));
    asm volatile("csrw tdata2, %0" : : "r"(0x0000000000000003));  // Type set to instruction breakpoint

    printf("Instruction breakpoint set at address: 0x%llx\n", addr);
}

// Function to set a data breakpoint at a specific address
void set_data_breakpoint(uint64_t *addr) {
    asm volatile("csrw mtvec, %0" : : "r"(trap_handler));  // Set the trap handler
    asm volatile("csrw mstatus, %0" : : "r"(0x8));         // Set MIE (Machine Interrupt Enable)
    asm volatile("csrw mie, %0" : : "r"(0x800));           // Enable machine-mode software interrupt

    expected_tval = (uint64_t)addr;  // Set expected tval for data breakpoint

    // Set the data breakpoint at the desired address
    asm volatile("csrw tdata1, %0" : : "r"(addr));
    asm volatile("csrw tdata2, %0" : : "r"(0x0000000000000003));  // Type set to data breakpoint

    printf("Data breakpoint set at address: 0x%llx\n", addr);
}

// Trap handler implementation
void terminate() {
    while (1) {
        asm volatile ("wfi");  // Wait for interrupt (or an appropriate halt instruction)
    }
}

// Set up the trap handler
void setup_trap_handler() {
    // Set the trap handler address to mtvec
    uintptr_t handler_addr = (uintptr_t)trap_handler;
    asm volatile("csrw mtvec, %0" :: "r"(handler_addr)); // Set mtvec to the handler's address

    // Ensure interrupts and exceptions are enabled
    asm volatile("csrsi mstatus, 0x8"); // Set MIE (machine interrupt enable) bit in mstatus
}
// Define exception cause codes
#define CAUSE_FETCH_GUEST_PAGE_FAULT    0x14
#define CAUSE_LOAD_GUEST_PAGE_FAULT     0x15
#define CAUSE_VIRTUAL_INSTRUCTION       0x16
#define CAUSE_STORE_GUEST_PAGE_FAULT    0x17

// Declare flags to indicate which traps occurred
volatile bool trap_misaligned_fetch = false;
volatile bool trap_fetch_access = false;
volatile bool trap_illegal_instruction = false;
volatile bool trap_breakpoint = false;
volatile bool trap_misaligned_load = false;
volatile bool trap_load_access = false;
volatile bool trap_misaligned_store = false;
volatile bool trap_store_access = false;
volatile bool trap_user_ecall = false;
volatile bool trap_supervisor_ecall = false;
volatile bool trap_machine_ecall = false;
volatile bool trap_fetch_page_fault = false;
volatile bool trap_load_page_fault = false;
volatile bool trap_store_page_fault = false;
// Add more flags as needed for other exception causes


// Trap handler implementation
void trap_handler(void) __attribute__((interrupt, aligned(64)));
void trap_handler() {
    uint64_t mcause, mepc, mstatus, mip, mtval;
    uint32_t instruction;

    trap_count++;

    // Limit trap handler invocations to avoid infinite loops
    if (trap_count > 5) {
        ASSERT(0, "Trap handler triggered more than 5 times. Terminating...");
        terminate();
    }

    // Read CSR registers to determine the cause of the trap
    asm volatile("csrr %0, mcause" : "=r"(mcause));
    asm volatile("csrr %0, mepc" : "=r"(mepc));
    asm volatile("csrr %0, mstatus" : "=r"(mstatus));
    asm volatile("csrr %0, mip" : "=r"(mip));
    asm volatile("csrr %0, mtval" : "=r"(mtval));

    printf("Trap Handler Triggered:\n");
    printf("mcause: 0x%lx\n", mcause);
    printf("mepc: 0x%lx\n", mepc);
    printf("mstatus: 0x%lx\n", mstatus);
    printf("mip: 0x%lx\n", mip);
    printf("mtval: 0x%lx\n", mtval);

    // Handle different trap causes
    switch (mcause) {
        case CAUSE_MISALIGNED_FETCH:
            printf("Exception: Instruction address misaligned.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_misaligned_fetch = true;
            // Adjust mepc to point to the next instruction
            mepc = (mepc + 2) & ~0x1;  // Assuming compressed instructions are allowed
            break;

        case CAUSE_FETCH_ACCESS:
            printf("Exception: Instruction access fault.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_fetch_access = true;
            mepc += 4;  // Skip the faulting instruction
            break;

        case CAUSE_ILLEGAL_INSTRUCTION:
            printf("Exception: Illegal instruction.\n");
            printf("Faulting instruction at address: 0x%lx\n", mepc);
            trap_illegal_instruction = true;
            mepc += 4;  // Skip the illegal instruction
            break;

        case CAUSE_BREAKPOINT:
            printf("Exception: Breakpoint.\n");
            trap_breakpoint = true;
            mepc += 4;  // Skip the breakpoint instruction
            break;

        case CAUSE_MISALIGNED_LOAD:
            printf("Exception: Load address misaligned.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_misaligned_load = true;
            mepc += 4;  // Skip the faulting instruction
            break;

        case CAUSE_LOAD_ACCESS:
            printf("Exception: Load access fault.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_load_access = true;
            mepc += 4;  // Skip the faulting instruction
            break;

        case CAUSE_MISALIGNED_STORE:
            printf("Exception: Store address misaligned.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_misaligned_store = true;
            mepc += 4;  // Skip the faulting instruction
            break;

        case CAUSE_STORE_ACCESS:
            printf("Exception: Store access fault.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_store_access = true;
            mepc += 4;  // Skip the faulting instruction
            break;

        case CAUSE_USER_ECALL:
            printf("Exception: Environment call from U-mode.\n");
            trap_user_ecall = true;
            mepc += 4;  // Skip the ecall instruction
            break;

        case CAUSE_SUPERVISOR_ECALL:
            printf("Exception: Environment call from S-mode.\n");
            trap_supervisor_ecall = true;
            mepc += 4;  // Skip the ecall instruction
            break;

        case CAUSE_MACHINE_ECALL:
            printf("Exception: Environment call from M-mode.\n");
            trap_machine_ecall = true;
            mepc += 4;  // Skip the ecall instruction
            break;

        case CAUSE_FETCH_PAGE_FAULT:
            printf("Exception: Instruction page fault.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_fetch_page_fault = true;
            mepc += 4;  // Skip the faulting instruction
            break;

        case CAUSE_LOAD_PAGE_FAULT:
            printf("Exception: Load page fault.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_load_page_fault = true;
            mepc += 4;  // Skip the faulting instruction
            break;

        case CAUSE_STORE_PAGE_FAULT:
            printf("Exception: Store page fault.\n");
            printf("Faulting address: 0x%lx\n", mtval);
            trap_store_page_fault = true;
            mepc += 4;  // Skip the faulting instruction
            break;

        default:
            if ((mcause & (1UL << 63)) != 0) {  // Interrupts
                uint64_t interrupt_cause = mcause & ~(1UL << 63);
                printf("Interrupt occurred. Cause: 0x%lx\n", interrupt_cause);
                // Handle interrupts based on cause
                // For simplicity, we'll just skip over interrupts in this example
            } else {
                printf("Exception: Unknown cause 0x%lx\n", mcause);
                // Skip the faulting instruction to prevent infinite trap loops
                mepc += 4;
            }
            break;
    }

    // Correct `mepc` for instruction size (compressed or standard)
    // Read the instruction at `mepc` to determine its length
    asm volatile("lhu %0, 0(%1)" : "=r"(instruction) : "r"(mepc));

    // Check if the instruction is compressed (16-bit) or standard (32-bit)
    if ((instruction & 0x3) != 0x3) {
        // Compressed instruction (16-bit), increment mepc by 2
        mepc += 2;
    } else {
        // Standard instruction (32-bit), increment mepc by 4
        mepc += 4;
    }

    // Write the updated mepc value back to the CSR
    asm volatile("csrw mepc, %0" :: "r"(mepc));
}

static inline unsigned long read_mstatus(void) {
    unsigned long value;
    __asm__ volatile ("csrr %0, mstatus" : "=r" (value));
    return value;
}

static inline void write_mstatus(unsigned long value) {
    __asm__ volatile ("csrw mstatus, %0" : : "r" (value));
}


// Implement configure_privilege_and_vector_extension
void configure_privilege_and_vector_extension() {
    unsigned long mstatus = read_csr(mstatus); // Read current mstatus

    // Set MPP to Machine mode
    mstatus &= ~MSTATUS_MPP_MASK;       // Clear MPP bits (11-12)
    mstatus |= MSTATUS_MPP_MACHINE;     // Set MPP to Machine mode (11)

    // Enable Vector Extension by setting XS field
    mstatus &= ~MSTATUS_XS_MASK;        // Clear XS bits (15-14)
    mstatus |= MSTATUS_XS_V;            // Set XS to enable Vector Extension (01)

    write_csr(mstatus, mstatus);      // Write back the modified mstatus
}

// Implement initialize_vector_registers
void initialize_vector_registers() {
    uint64_t vl = 4096; // Vector length to 4096

    __asm__ volatile (
        "vsetvli t0, %0, e32, m1, tu, mu\n"  // Set vector configuration for 32-bit elements
        // Reset vector registers v0 to v31 to zero using x0 (which is always zero)
        "vmv.v.x v0, x0\n"
        "vmv.v.x v1, x0\n"
        "vmv.v.x v2, x0\n"
        "vmv.v.x v3, x0\n"
        "vmv.v.x v4, x0\n"
        "vmv.v.x v5, x0\n"
        "vmv.v.x v6, x0\n"
        "vmv.v.x v7, x0\n"
        "vmv.v.x v8, x0\n"
        "vmv.v.x v9, x0\n"
        "vmv.v.x v10, x0\n"
        "vmv.v.x v11, x0\n"
        "vmv.v.x v12, x0\n"
        "vmv.v.x v13, x0\n"
        "vmv.v.x v14, x0\n"
        "vmv.v.x v15, x0\n"
        "vmv.v.x v16, x0\n"
        "vmv.v.x v17, x0\n"
        "vmv.v.x v18, x0\n"
        "vmv.v.x v19, x0\n"
        "vmv.v.x v20, x0\n"
        "vmv.v.x v21, x0\n"
        "vmv.v.x v22, x0\n"
        "vmv.v.x v23, x0\n"
        "vmv.v.x v24, x0\n"
        "vmv.v.x v25, x0\n"
        "vmv.v.x v26, x0\n"
        "vmv.v.x v27, x0\n"
        "vmv.v.x v28, x0\n"
        "vmv.v.x v29, x0\n"
        "vmv.v.x v30, x0\n"
        "vmv.v.x v31, x0\n"
        :
        : "r" (vl)
        : "t0", "memory"
    );
}

// Initialize registers for the RISC-V processor
void initialize_registers() {
    asm volatile (
        // Initialize general-purpose registers
        //"li sp, 0x2000000000200000 \n"   // Stack pointer within .runtime.stack section (aligned to 64 bytes)
        "li ra, 0x2000000000002000 \n"   // Return address within .text.init section (aligned to 64 bytes)
        //"li gp, 0x2000000000003000 \n"   // Global pointer within .text.init section (aligned to 64 bytes)
        //"li tp, 0x2000000000104000 \n"   // Thread pointer within .tdata section (aligned to 64 bytes)
        "li t0, 4 \n"                    // Temporary registers
        "li t1, 5 \n"
        "li t2, 6 \n"
        "li s0, 0x2000000000105000 \n"   // Saved registers within .data section (aligned to 64 bytes)
        "li s1, 0x2000000000106000 \n"   // Aligned within .data section
        "li a0, 0x2000000000107000 \n"   // Function arguments / return values within .data section (aligned to 64 bytes)
        "li a1, 0x2000000000108000 \n"   // Aligned within .data section
        "li a2, 0x2000000000109000 \n"   // Aligned within .data section
        "li a3, 0x200000000010A000 \n"   // Aligned within .data section
        "li a4, 0x200000000010B000 \n"   // Aligned within .data section
        "li a5, 0x200000000010C000 \n"   // Aligned within .data section
        "li a6, 0x200000000010D000 \n"   // Aligned within .data section
        "li a7, 0x200000000010E000 \n"   // Aligned within .data section
        "li s2, 0x200000000010F000 \n"   // Saved registers (aligned within .data section)
        "li s3, 0x2000000000110000 \n"   // Aligned within .data section
        "li s4, 0x2000000000111000 \n"   // Aligned within .data section
        "li s5, 0x2000000000112000 \n"   // Aligned within .data section
        "li s6, 0x2000000000113000 \n"   // Aligned within .data section
        "li s7, 0x2000000000114000 \n"   // Aligned within .data section
        "li s8, 0x2000000000115000 \n"   // Aligned within .data section
        "li s9, 0x2000000000116000 \n"   // Aligned within .data section
        "li s10, 0x2000000000117000 \n"  // Aligned within .data section
        "li s11, 0x2000000000118000 \n"  // Aligned within .data section
        "li t3, 0x2000000000119000 \n"   // Temporary registers (aligned within .data section)
        "li t4, 0x200000000011A000 \n"   // Aligned within .data section
        "li t5, 0x200000000011B000 \n"   // Aligned within .data section
        "li t6, 0x200000000011C000 \n"   // Aligned within .data section

        // Enable FPU, vector, and accelerator if present
        "mv t0, %[status_flags] \n"
        "csrs mstatus, t0 \n"

        // Initialize FPU if present
        "la t0, 1f \n"
        "csrw mtvec, t0 \n"

        "fssr x0 \n"
        "fmv.s.x f0, x0 \n"
        "fmv.s.x f1, x0 \n"
        "fmv.s.x f2, x0 \n"
        "fmv.s.x f3, x0 \n"
        "fmv.s.x f4, x0 \n"
        "fmv.s.x f5, x0 \n"
        "fmv.s.x f6, x0 \n"
        "fmv.s.x f7, x0 \n"
        "fmv.s.x f8, x0 \n"
        "fmv.s.x f9, x0 \n"
        "fmv.s.x f10, x0 \n"
        "fmv.s.x f11, x0 \n"
        "fmv.s.x f12, x0 \n"
        "fmv.s.x f13, x0 \n"
        "fmv.s.x f14, x0 \n"
        "fmv.s.x f15, x0 \n"
        "fmv.s.x f16, x0 \n"
        "fmv.s.x f17, x0 \n"
        "fmv.s.x f18, x0 \n"
        "fmv.s.x f19, x0 \n"
        "fmv.s.x f20, x0 \n"
        "fmv.s.x f21, x0 \n"
        "fmv.s.x f22, x0 \n"
        "fmv.s.x f23, x0 \n"
        "fmv.s.x f24, x0 \n"
        "fmv.s.x f25, x0 \n"
        "fmv.s.x f26, x0 \n"
        "fmv.s.x f27, x0 \n"
        "fmv.s.x f28, x0 \n"
        "fmv.s.x f29, x0 \n"
        "fmv.s.x f30, x0 \n"
        "fmv.s.x f31, x0 \n"
    "1: \n"
        :
        : [status_flags] "r" (MSTATUS_FS | MSTATUS_XS | MSTATUS_VS)
        : "t0", "memory"
    );

    printf("Initialized vector registers v0 to v31 to zero.\n");
}


// Convert float to uint32_t representation
uint32_t float_to_uint32(float f) {
    union { float f; uint32_t u; } temp;
    temp.f = f;
    return temp.u;
}

// Convert float to bit representation as uint32_t
uint32_t float_to_bits(float f) {
    uint32_t result;
    memcpy(&result, &f, sizeof(result));
    return result;
}

// Convert integer to hexadecimal string
void int_to_hex(uint32_t value, char *output) {
    const char hex_chars[] = "0123456789ABCDEF";
    for (int i = 7; i >= 0; i--) {
        output[i] = hex_chars[value & 0xF];
        value >>= 4;
    }
    output[8] = '\0';
}

// Convert string to integer
int atoi(const char *str) {
    int num = 0;
    while (*str >= '0' && *str <= '9') {
        num = num * 10 + (*str - '0');
        str++;
    }
    return num;
}

// Get integer part of float
float aint(float x) {
    return (x > 0) ? (float)((int)x) : (float)((int)(x - 1));
}

// Compute absolute value of float
float fabsf(float x) {
    return (x < 0.0f) ? -x : x;
}

// Compute square root using Newton-Raphson method
float sqrtf(float number) {
    float x = number * 0.5f;
    float y = number;
    const float epsilon = 0.000001f;
    while (fabsf(x - y) > epsilon) {
        y = x;
        x = 0.5f * (x + number / x);
    }
    return x;
}

// Compute arctangent using polynomial approximation
float atanf(float x) {
    const float a = 0.9998660f;
    const float b = -0.3302995f;
    const float c = 0.1801410f;
    const float d = -0.0851330f;
    const float e = 0.0208351f;

    float x2 = x * x;
    return x * (a + x2 * (b + x2 * (c + x2 * (d + x2 * e))));
}

// Compute arctangent of y/x using polynomial approximation
float atan2f(float y, float x) {
    if (x > 0.0f) {
        return atanf(y / x);
    } else if (x < 0.0f) {
        if (y >= 0.0f) {
            return atanf(y / x) + pi;
        } else {
            return atanf(y / x) - pi;
        }
    } else {
        if (y > 0.0f) {
            return half_pi;
        } else if (y < 0.0f) {
            return -half_pi;
        } else {
            return 0.0f; // undefined, but we return 0
        }
    }
}

// Custom error handling function to support open source package
void error(const char *message) {
    // In a real application, you might handle the error differently
    // Here we just print the message and return an error code
    ASSERT(0, "Error: %s", message);
}

// Custom implementation of asin using only floats
float asinf(float x) {
    if (fabsf(x) > 1.0f) {
        error("Inverse trig functions lose much of their gloss when their arguments are greater than 1.");
        return 0.0f; // Return an error value
    }
    return atan2f(x, sqrtf(1.0f - x * x));
}

// Function to compute arctangent using a polynomial approximation
#define cotf(x) (1.f / tanf(x))

// Memory pool
static char memory_pool[MEMORY_POOL_SIZE];

// Block metadata structure
typedef struct Block {
    size_t size;
    int free;
    struct Block *next;
} Block;

// Pointer to the first block in the memory pool
static Block *free_list = (Block *)memory_pool;

// Initialize the memory pool
void memory_init() {
    free_list->size = MEMORY_POOL_SIZE - sizeof(Block);
    free_list->free = 1;
    free_list->next = NULL;
}

static size_t memory_used = 0;

// Custom farmalloc function
char *farmalloc(long s) {
    // Ensure requested size is positive and doesn't exceed the remaining pool size
    if (s <= 0 || memory_used + s > MEMORY_POOL_SIZE) {
        return NULL;  // Not enough memory or invalid size
    }

    // Allocate memory by returning a pointer to the current position in the pool
    char *allocated_memory = memory_pool + memory_used;
    memory_used += s;  // Increment memory used by the size of the allocation

    return allocated_memory;
}

// Free allocated memory
void free(void *ptr) {
    if (ptr == NULL) {
        return;
    }

    Block *block = (Block *)((uint8_t *)ptr - sizeof(Block));
    block->free = 1;

    // Merge adjacent free blocks
    Block *current = free_list;
    while (current != NULL) {
        if (current->free && current->next && current->next->free) {
            current->size += sizeof(Block) + current->next->size;
            current->next = current->next->next;
        }
        current = current->next;
    }
}
// Global variable to simulate input (as if it were from stdin)
const char *input_data = "This is a simulated input.\nAnother line.\n";
int input_position = 0;

// Simulated fgets function
char *fgets(char *buffer, int size) {
    if (size <= 0 || !buffer) {
        return NULL; // Handle invalid size or null buffer
    }

    int i = 0;
    char ch;

    // Simulate reading characters from the input_data "stream"
    while (i < size - 1) {
        if (input_data[input_position] == '\0') {
            // Simulate end-of-file (EOF)
            if (i == 0) {
                return NULL; // No characters read, return NULL
            }
            break;
        }

        ch = input_data[input_position++];
        buffer[i++] = ch;

        if (ch == '\n') {
            break; // Stop at newline
        }
    }

    buffer[i] = '\0';  // Null-terminate the string

    return buffer;
}

#endif // COMMON_H

