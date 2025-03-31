#pragma once

#include <testutils.h>
// -------- Interrupt override -----------------
volatile static bool expect_bwe_irq;
volatile static uint32_t expected_cnt;
volatile static uint32_t real_cnt;

//---------- common functions -------------------
void update_irq_aux_var(uint32_t allow_access);

void test_addr_32b(uint32_t addr, uint32_t allow_wr, uint32_t allow_rd, char *tag_name, uint32_t ro_expected_data);
