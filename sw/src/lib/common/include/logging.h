#pragma once

//--------------------------------------------------
// INCLUDES
//--------------------------------------------------

#include <printf.h>
#include <string.h>

//--------------------------------------------------
// DEFINITIONS
//--------------------------------------------------

#define LOG_LEVEL_DEBUG   0
#define LOG_LEVEL_INFO    1
#define LOG_LEVEL_WARNING 2
#define LOG_LEVEL_ERROR   3
#define LOG_LEVEL_NONE    4

// Define the logging level
#ifndef LOG_LEVEL
// Change this definition to increase/decrease log verbosity
#define LOG_LEVEL LOG_LEVEL_NONE
#endif

//--------------------------------------------------
// MACROS
//--------------------------------------------------

#define __FILENAME__ (strrchr(__FILE__, '/') ? strrchr(__FILE__, '/') + 1 : __FILE__)

// Logging macro
#if LOG_LEVEL <= LOG_LEVEL_DEBUG
#define LOG_DEBUG(fmt, ...) \
  do { \
    printf("[DEBUG] (%-15.15s:%4d): " fmt "\n", __FILENAME__, __LINE__, ##__VA_ARGS__); \
  } while (0)
#else
#define LOG_DEBUG(fmt, ...) do {} while (0)
#endif

#if LOG_LEVEL <= LOG_LEVEL_INFO
#define LOG_INFO(fmt, ...) \
  do { \
    printf("[INFO] (%-15.15s:%4d): " fmt "\n", __FILENAME__, __LINE__, ##__VA_ARGS__); \
  } while (0)
#else
#define LOG_INFO(fmt, ...) do {} while (0)
#endif

#if LOG_LEVEL <= LOG_LEVEL_WARNING
#define LOG_WARNING(fmt, ...) \
  do { \
    printf("[WARNING] (%-15.15s:%4d): " fmt "\n", __FILENAME__, __LINE__, ##__VA_ARGS__); \
  } while (0)
#else
#define LOG_WARNING(fmt, ...) do {} while (0)
#endif

#if LOG_LEVEL <= LOG_LEVEL_ERROR
#define LOG_ERROR(fmt, ...) \
  do { \
    printf("[ERROR] (%-15.15s:%4d): " fmt "\n", __FILENAME__, __LINE__, ##__VA_ARGS__); \
  } while (0)
#else
#define LOG_ERROR(fmt, ...) do {} while (0)
#endif
