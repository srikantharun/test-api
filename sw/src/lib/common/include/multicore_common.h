#pragma once

#include <platform.h>

typedef enum {
  STATUS_INVALID = 0, // unused
  STATUS_IDLE,        // waiting for a new job
  STATUS_READY,       // job is ready to be run by the worker (set by manager)
  STATUS_RUNNING,     // job is currently running (set by worker)
  STATUS_EXITED,      // job has exited
} CORE_STATUS;

#define SIGABRT (6)

typedef struct {
  int status;
  int ret;
} core_t;
