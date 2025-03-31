#pragma once

#define LOG_LEVEL_NON 0U
#define LOG_LEVEL_ERR 1U
#define LOG_LEVEL_WRN 2U
#define LOG_LEVEL_INF 3U
#define LOG_LEVEL_DBG 4U
#define LOG_LEVEL_TRC 5U

#define NUM_LOG_LEVELS 6

#ifndef COMPILE_LOG_LEVEL
#define COMPILE_LOG_LEVEL LOG_LEVEL_INF
#endif
