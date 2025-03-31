#pragma once

#include <stdint.h>
#include <string.h>
#include <util.h>
#include <asm.h>
#include <reentrant_lock.h>
#include <log_levels.h>

// The maximum number of __VA_ARGS__ is equal to 64. Thus we support up to 64
#define _CV_VA_NUM_ARGS_HELPER(_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,_11,_12,_13,_14,_15,_16,_17,_18,_19,_20,_21,_22,_23,_24,_25,_26,_27,_28,_29,_30,_31,_32,_33,_34,_35,_36,_37,_38,_39,_40,_41,_42,_43,_44,_45,_46,_47,_48,_49,_50,_51,_52,_53,_54,_55,_56,_57,_58,_59,_60,_61,_62,_63,_64,N,...) N
#define _CV_VA_NUM_ARGS(...)      _CV_VA_NUM_ARGS_HELPER(__VA_ARGS__ __VA_OPT__(,) 64,63,62,61,60,59,58,57,56,55,54,53,52,51,50,49,48,47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,32,31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0)
#define _printf_wrapper(fmt, ...) _printf(_CV_VA_NUM_ARGS(__VA_ARGS__) + 1, "#%02u: " fmt, r_uhartid() __VA_OPT__(, __VA_ARGS__))

// Printf magic to remove prints if COMPILE_LOG_LEVEL < LOG_LEVEL_INF
#if !defined(COMPILE_LOG_LEVEL) || (COMPILE_LOG_LEVEL >= LOG_LEVEL_INF)
#define printf(...) _printf_wrapper(__VA_ARGS__)
#else
#define printf(...) _printf_dummy(__VA_ARGS__)
#endif

static inline int _printf_dummy(const char *fmt, ...) {
    UNUSED(fmt);
    return 0; // Always return 0 as in your original function
}

typedef enum {
  PRINTF_INVALID = 0, // unused
  PRINTF_IDLE,        // waiting for a new printf
  PRINTF_FILLING,     // printf is filling the buffer
  PRINTF_EXITED,      // printf has finished, buffer ready to print
} PRINTF_STATUS;

typedef struct {
  volatile int status;
  volatile char buf[256];
  reentrant_lock_t lock;
} printf_t;
