#pragma once

#include <stdint.h>
#include <printf.h>
#include <testutils.h>
#include <util.h>

volatile __thread uint64_t dummy = 0xdeadbeef;

int test_thread_local_storage(void *arg) {
  UNUSED(arg);
  testcase_init();

  printf("thread pointer: 0x%010x\n", __builtin_thread_pointer());
  printf("dummy:          0x%016x\n", dummy);
  printf("&dummy:         0x%010x\n", &dummy);
  CHECK_EQUAL_INT(0xdeadbeef, dummy, "thread-local variable does not contain correct value");

  printf("checking thread-local variable is stored in correct memory...\n");
  extern char _tls_begin, _tls_end;
  CHECK_TRUE((uintptr_t)&dummy >= (uintptr_t)&_tls_begin, "thread-local variable stored outside intended memory");
  CHECK_TRUE((uintptr_t)&dummy < (uintptr_t)&_tls_end, "thread-local variable stored outside intended memory");

  return testcase_finalize();
}
