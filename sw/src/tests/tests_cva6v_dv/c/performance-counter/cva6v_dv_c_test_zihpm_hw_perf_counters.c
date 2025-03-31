// This is a test file for zihpm_hw_perf_counters
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test hardware performance counters
void test_zihpm_hw_perf_counters() {
    uint64_t start_cycles, end_cycles;
    uint64_t start_instrs, end_instrs;
    uint64_t perf_counter_start[58];
    uint64_t perf_counter_end[58];
    int i;

    // Array to hold the names of performance counters
    const char* perf_counter_names[58] = {
        "hpmcounter3", "hpmcounter4", "hpmcounter5", "hpmcounter6",
        "hpmcounter7", "hpmcounter8", "hpmcounter9", "hpmcounter10",
        "hpmcounter11", "hpmcounter12", "hpmcounter13", "hpmcounter14",
        "hpmcounter15", "hpmcounter16", "hpmcounter17", "hpmcounter18",
        "hpmcounter19", "hpmcounter20", "hpmcounter21", "hpmcounter22",
        "hpmcounter23", "hpmcounter24", "hpmcounter25", "hpmcounter26",
        "hpmcounter27", "hpmcounter28", "hpmcounter29", "hpmcounter30",
        "hpmcounter31", "hpmcounter3h", "hpmcounter4h", "hpmcounter5h",
        "hpmcounter6h", "hpmcounter7h", "hpmcounter8h", "hpmcounter9h",
        "hpmcounter10h", "hpmcounter11h", "hpmcounter12h", "hpmcounter13h",
        "hpmcounter14h", "hpmcounter15h", "hpmcounter16h", "hpmcounter17h",
        "hpmcounter18h", "hpmcounter19h", "hpmcounter20h", "hpmcounter21h",
        "hpmcounter22h", "hpmcounter23h", "hpmcounter24h", "hpmcounter25h",
        "hpmcounter26h", "hpmcounter27h", "hpmcounter28h", "hpmcounter29h",
        "hpmcounter30h", "hpmcounter31h"
    };

    // Read initial cycle and instruction counts
    __asm__ volatile("rdcycle %0" : "=r"(start_cycles));
    __asm__ volatile("rdinstret %0" : "=r"(start_instrs));

    // Read initial values of performance counters
    for (i = 0; i < 29; i++) {
        switch(i) {
            case 0:
                __asm__ volatile("csrr %0, hpmcounter3" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter3h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 1:
                __asm__ volatile("csrr %0, hpmcounter4" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter4h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 2:
                __asm__ volatile("csrr %0, hpmcounter5" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter5h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 3:
                __asm__ volatile("csrr %0, hpmcounter6" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter6h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 4:
                __asm__ volatile("csrr %0, hpmcounter7" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter7h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 5:
                __asm__ volatile("csrr %0, hpmcounter8" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter8h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 6:
                __asm__ volatile("csrr %0, hpmcounter9" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter9h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 7:
                __asm__ volatile("csrr %0, hpmcounter10" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter10h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 8:
                __asm__ volatile("csrr %0, hpmcounter11" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter11h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 9:
                __asm__ volatile("csrr %0, hpmcounter12" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter12h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 10:
                __asm__ volatile("csrr %0, hpmcounter13" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter13h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 11:
                __asm__ volatile("csrr %0, hpmcounter14" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter14h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 12:
                __asm__ volatile("csrr %0, hpmcounter15" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter15h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 13:
                __asm__ volatile("csrr %0, hpmcounter16" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter16h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 14:
                __asm__ volatile("csrr %0, hpmcounter17" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter17h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 15:
                __asm__ volatile("csrr %0, hpmcounter18" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter18h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 16:
                __asm__ volatile("csrr %0, hpmcounter19" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter19h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 17:
                __asm__ volatile("csrr %0, hpmcounter20" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter20h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 18:
                __asm__ volatile("csrr %0, hpmcounter21" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter21h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 19:
                __asm__ volatile("csrr %0, hpmcounter22" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter22h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 20:
                __asm__ volatile("csrr %0, hpmcounter23" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter23h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 21:
                __asm__ volatile("csrr %0, hpmcounter24" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter24h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 22:
                __asm__ volatile("csrr %0, hpmcounter25" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter25h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 23:
                __asm__ volatile("csrr %0, hpmcounter26" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter26h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 24:
                __asm__ volatile("csrr %0, hpmcounter27" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter27h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 25:
                __asm__ volatile("csrr %0, hpmcounter28" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter28h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 26:
                __asm__ volatile("csrr %0, hpmcounter29" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter29h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 27:
                __asm__ volatile("csrr %0, hpmcounter30" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter30h" : "=r"(perf_counter_start[i + 29]));
                break;
            case 28:
                __asm__ volatile("csrr %0, hpmcounter31" : "=r"(perf_counter_start[i]));
                __asm__ volatile("csrr %0, hpmcounter31h" : "=r"(perf_counter_start[i + 29]));
                break;
        }
    }

    // Perform a CPU-intensive task to increment performance counters
    for (volatile int j = 0; j < 1000000; j++);

    // Read final cycle and instruction counts
    __asm__ volatile("rdcycle %0" : "=r"(end_cycles));
    __asm__ volatile("rdinstret %0" : "=r"(end_instrs));

    // Read final values of performance counters
    for (i = 0; i < 29; i++) {
        switch(i) {
            case 0:
                __asm__ volatile("csrr %0, hpmcounter3" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter3h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 1:
                __asm__ volatile("csrr %0, hpmcounter4" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter4h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 2:
                __asm__ volatile("csrr %0, hpmcounter5" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter5h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 3:
                __asm__ volatile("csrr %0, hpmcounter6" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter6h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 4:
                __asm__ volatile("csrr %0, hpmcounter7" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter7h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 5:
                __asm__ volatile("csrr %0, hpmcounter8" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter8h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 6:
                __asm__ volatile("csrr %0, hpmcounter9" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter9h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 7:
                __asm__ volatile("csrr %0, hpmcounter10" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter10h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 8:
                __asm__ volatile("csrr %0, hpmcounter11" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter11h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 9:
                __asm__ volatile("csrr %0, hpmcounter12" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter12h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 10:
                __asm__ volatile("csrr %0, hpmcounter13" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter13h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 11:
                __asm__ volatile("csrr %0, hpmcounter14" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter14h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 12:
                __asm__ volatile("csrr %0, hpmcounter15" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter15h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 13:
                __asm__ volatile("csrr %0, hpmcounter16" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter16h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 14:
                __asm__ volatile("csrr %0, hpmcounter17" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter17h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 15:
                __asm__ volatile("csrr %0, hpmcounter18" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter18h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 16:
                __asm__ volatile("csrr %0, hpmcounter19" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter19h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 17:
                __asm__ volatile("csrr %0, hpmcounter20" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter20h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 18:
                __asm__ volatile("csrr %0, hpmcounter21" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter21h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 19:
                __asm__ volatile("csrr %0, hpmcounter22" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter22h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 20:
                __asm__ volatile("csrr %0, hpmcounter23" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter23h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 21:
                __asm__ volatile("csrr %0, hpmcounter24" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter24h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 22:
                __asm__ volatile("csrr %0, hpmcounter25" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter25h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 23:
                __asm__ volatile("csrr %0, hpmcounter26" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter26h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 24:
                __asm__ volatile("csrr %0, hpmcounter27" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter27h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 25:
                __asm__ volatile("csrr %0, hpmcounter28" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter28h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 26:
                __asm__ volatile("csrr %0, hpmcounter29" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter29h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 27:
                __asm__ volatile("csrr %0, hpmcounter30" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter30h" : "=r"(perf_counter_end[i + 29]));
                break;
            case 28:
                __asm__ volatile("csrr %0, hpmcounter31" : "=r"(perf_counter_end[i]));
                __asm__ volatile("csrr %0, hpmcounter31h" : "=r"(perf_counter_end[i + 29]));
                break;
        }
    }

    // Print the performance counter results
    printf("Performance Counters Results:\n");
    printf("Cycles: Start = %llu, End = %llu, Difference = %llu\n", start_cycles, end_cycles, end_cycles - start_cycles);
    printf("Instructions: Start = %llu, End = %llu, Difference = %llu\n", start_instrs, end_instrs, end_instrs - start_instrs);

    for (i = 0; i < 58; i++) {
        printf("%s: Start = %llu, End = %llu, Difference = %llu\n",
               perf_counter_names[i],
               perf_counter_start[i],
               perf_counter_end[i],
               perf_counter_end[i] - perf_counter_start[i]);
    }
}

int main() {
    printf("Running test: zihpm_hw_perf_counters\n");
    initialize_registers();
    test_zihpm_hw_perf_counters();
    return 0;
}
