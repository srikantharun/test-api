// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#include "dma_test_utils.h"
#include <printf.h>
#include <rng.h>


// 32kB random data, used as first source and as reference to compare against
const char __attribute__((aligned(4096))) arrRef[DATA_SIZE_32KB] = {RANDOM_DATA_32KB};

// 16kB of 0x55 to reset memory
const char __attribute__((aligned(4096))) arr55[DATA_SIZE_16KB] = {INIT_DATA_16KB};
