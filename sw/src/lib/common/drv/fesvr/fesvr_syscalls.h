#pragma once

#include <stdint.h>
#include <stddef.h>

#define SYS_write 64

uintptr_t fesvr_syscall(uintptr_t which, uint64_t arg0, uint64_t arg1, uint64_t arg2);
