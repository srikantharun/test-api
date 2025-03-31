#pragma once

#include "platform_common.h"

int main();

__attribute__((noreturn)) void exit(int code);
__attribute__((noreturn)) void abort();

void _init();

#define IRQ_PRIORITY_DISABLED 0
#define IRQ_PRIORITY_DEFAULT 1
