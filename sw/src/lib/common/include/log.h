#pragma once

#include <stdint.h>
#include <printf.h>
#include <stdbool.h>
#include <log_levels.h>

extern int config_log_level;

void log_set_level(int level);

bool is_valid_log_level(int log_level);

#define IMPL_LOG(_level, fmt, ...)            \
  do {                                        \
    if(config_log_level >= (int)_level){      \
      _printf_wrapper(fmt "\n", __VA_ARGS__);     \
    }                                         \
  } while (0)

#define _IMPL_LOG_WRAPPER(_level, ...)                              \
  do {                                                              \
    if (COMPILE_LOG_LEVEL >= _level) IMPL_LOG(_level, __VA_ARGS__); \
  } while (0)

#define LOG_ERR(...) _IMPL_LOG_WRAPPER(LOG_LEVEL_ERR, __VA_ARGS__)
#define LOG_WRN(...) _IMPL_LOG_WRAPPER(LOG_LEVEL_WRN, __VA_ARGS__)
#define LOG_INF(...) _IMPL_LOG_WRAPPER(LOG_LEVEL_INF, __VA_ARGS__)
#define LOG_DBG(...) _IMPL_LOG_WRAPPER(LOG_LEVEL_DBG, __VA_ARGS__)
#define LOG_TRC(...) _IMPL_LOG_WRAPPER(LOG_LEVEL_TRC, __VA_ARGS__)
