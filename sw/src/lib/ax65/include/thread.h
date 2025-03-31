#pragma once

#include <stdint.h>
#include <multicore_common.h>

typedef struct {
  int status;
  int (*fp)(void *);
  void *arg;
  int ret;
} thread_t;

#define STATUS_INVALID 0 // unused
#define STATUS_IDLE    1 // waiting for a new job
#define STATUS_READY   2 // job is ready to be run by the worker (set by manager)
#define STATUS_RUNNING 3 // job is currently running (set by worker)
#define STATUS_EXITED  4 // job has exited

/*
 * Simple "threading" implementation.
 *
 * The primary core/thread/hardware thread (hart) is considered the manager. It
 * can offload execution of functions to other cores (workers).
 */

// Initializes the threading data. Called by the primary (manager) thread.
void _thread_init();

// Main function for worker threads.
__attribute__((noreturn)) void _thread_worker_main();

// Launches (*fp) on the specified core, optionally providing an argument to the function call.
void thread_launch(tid_t id, int (*fp)(void *), void *arg);
// Joins the specified thread. Returns its exit code.
int thread_join(tid_t id);
// Joins all threads. Returns the logical OR of all threads' exit codes.
int thread_join_all();
// Start a second thread on core ID
void enable_simple_multicore_printf(tid_t id);
// Waits for the core to finish
void disable_simple_multicore_printf(tid_t id);
