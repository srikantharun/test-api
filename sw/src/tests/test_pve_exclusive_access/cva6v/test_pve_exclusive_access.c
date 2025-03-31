// Copyright (C) 2024, Andes Technology Corp. Confidential Proprietary


#include "platform.h"
#include "testutils.h"
#include <trap.h>
#include "interrupt.h"
#include "asm.h"
#include "hw_defines.h"
#include <barrier.h>
#include <platform_common.h>

#define TEST_NUM 50


volatile uint32_t cri_sec_flag      __attribute__((section(".sys_spm"))) = {0};
volatile uint32_t test_result[10]    __attribute__((section(".sys_spm"))) = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

// Barrier structure
barrier_t __attribute__((section(".sys_spm"))) t_barrier;

int func_exclusive_access(void *arg){
    UNUSED(arg);

    volatile uint32_t test_result_sum = 0, hart_id_offset = 0;
	volatile uint32_t data = 0;
    volatile uint32_t sc_result = 0;
    volatile uint32_t test_cnt = 0;
    volatile uint32_t hart_num = 0;
    volatile uint32_t delay_cnt = 0;
    volatile uint32_t delay_num = 0;

    hart_id_offset = r_mhartid() - processor_first_hart_id();

    if (r_mhartid() <= PVE_0_CLUSTER_3_CORE_1){
        hart_num  = HW_DEFINES_PVE_0_CORE_NUMBER;
    }
    else{
        hart_num  = HW_DEFINES_PVE_1_CORE_NUMBER;
    }

    test_cnt = TEST_NUM;

    barrier_wait(&t_barrier);

    __asm__ __volatile__("li %5, 7\n\t"
                "load_delay_cnt1:\n\t"
                "add %5, %5, %6\n\t"
                "mv %4, %5\n\t"
                "delay_loop1:"
                "addi %4, %4, -1\n\t"
                "bnez %4, delay_loop1\n\t"

                "test1_loop:\n\t"
                            "lr.w %0, (%2)\n\t"
                            "addi %0, %0, 1\n\t"
                            "sc.w %1, %0, (%2)\n\t"
                            "bnez %1, load_delay_cnt1\n\t"
                "li %5, 7\n\t"

                "addi %3, %3, -1\n\t"
                            "bnez %3, test1_loop\n\t"
                            :"=&r"(data), "=&r"(sc_result):"r" (test_result), "r"(test_cnt), "r"(delay_cnt), "r"(delay_num), "r"(hart_id_offset)
                            );

    barrier_wait(&t_barrier);

    test_result_sum = test_result[0];
    CHECK_EQUAL_INT((hart_num * TEST_NUM), test_result_sum, ".");

    if (test_result_sum != (hart_num * TEST_NUM)) {
        return TEST_FAILURE;
    }

    barrier_wait(&t_barrier);

	int tmp;
    __asm__ __volatile__("addi %[tmp], %[hart_id_offset], 1\n\t"
                            "slli %[tmp], %[tmp], 2\n\t"
                            "add  %[tmp], %[test_result], %[tmp]\n\t"
                "li %[delay_num], 7\n\t"

                "load_delay_cnt2:\n\t"
                "add %[delay_num], %[delay_num], %[hart_id_offset]\n\t"
                "mv %[delay_cnt], %[delay_num]\n\t"
                "delay_loop2:\n\t"
                "addi %[delay_cnt], %[delay_cnt], -1\n\t"
                "bnez %[delay_cnt], delay_loop2\n\t"

                            "test2_loop:\n\t"
                            "lr.w %[data], (%[tmp])\n\t"
                            "addi %[data], %[data], 1\n\t"
                            "sc.w %[sc_result], %[data], (%[tmp])\n\t"
                            "bnez %[sc_result], load_delay_cnt2\n\t"

                "li %[delay_num], 7\n\t"
                            "addi %[test_cnt], %[test_cnt], -1\n\t"
                            "bnez %[test_cnt], test2_loop\n\t"
                            :[data]"=&r"(data), [sc_result]"=&r"(sc_result), [tmp]"=&r"(tmp)
                :[test_result]"r" (test_result), [test_cnt]"r"(test_cnt), [hart_id_offset]"r"(hart_id_offset),
                [delay_cnt]"r"(delay_cnt), [delay_num]"r"(delay_num)
                );

    barrier_wait(&t_barrier);

    test_result_sum = test_result[1] + test_result[2] + test_result[3] + test_result[4]  + test_result[5]  + test_result[6]  + test_result[7]  + test_result[8];
    CHECK_EQUAL_INT((hart_num * TEST_NUM), test_result_sum, "..");

    if (test_result_sum != (hart_num * TEST_NUM)) {
        return TEST_FAILURE;
    }

    barrier_wait(&t_barrier);

    __asm__ __volatile__("addi %3, %2, 36\n\t"
                            "test3_loop:\n\t"
                            "li %0, 1\n\t"
                            "amoswap.w.aqrl %0, %0, (%1)\n\t"
                            "bnez %0, test3_loop\n\t"
                            "lw %0, 0(%3)\n\t"
                            "addi %0, %0, 1\n\t"
                            "sw %0, 0(%3)\n\t"
                            "fence\n\t"
                            "li %0, 0\n\t"
                            "sw %0, 0(%1)\n\t"
                            :"=&r"(data): "r"(&cri_sec_flag), "r" (test_result), "r"(test_cnt)
                );

    barrier_wait(&t_barrier);

    test_result_sum = test_result[9];
    CHECK_EQUAL_INT(hart_num, test_result_sum, "...");

    if (test_result_sum != hart_num) {
        return TEST_FAILURE;
    }

    return TEST_SUCCESS;
}

int main() {
    testcase_init();

    uint64_t core_id = r_mhartid();

    if (core_id == PVE_0_CLUSTER_0_CORE_0 || core_id == PVE_1_CLUSTER_0_CORE_0){
      // Initialize the barrier with the number of cores
      barrier_init(&t_barrier, HW_DEFINES_PVE_0_CORE_NUMBER );
  }

    CHECK_EQUAL_INT(TEST_SUCCESS, func_exclusive_access(NULL));

	return testcase_finalize();
}
