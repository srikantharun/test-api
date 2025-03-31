#include <asm.h>
#include <platform.h>
#include <stddef.h>
#include <testutils.h>
#include "uvm_sw_ipc.h"
#include <critical_section.h>

// Memory for UVM SW IPC is "allocated" in linker script.
extern char _uvm_sw_ipc_mem;

static volatile uvm_sw_ipc_st *__get_uvm_sw_ipc_ptr() {
  volatile uvm_sw_ipc_st *uvm_sw_ipc = (volatile uvm_sw_ipc_st*)&_uvm_sw_ipc_mem;
  uint64_t idx = r_mhartid();
  return &uvm_sw_ipc[-idx];
}

#define pUVM_SW_IPC __get_uvm_sw_ipc_ptr()

static __thread uint64_t key = 0;
static __thread int irq_lock_nested = 0;

// Acquire Interrupt Lock
static inline void irq_lock() {
  if (irq_lock_nested == 0) {
    key = arch_irq_lock();
  }
  irq_lock_nested++;
}

// Release Interrupt Lock
static inline void irq_unlock() {
  if(irq_lock_nested > 0){
    irq_lock_nested--;
    if (irq_lock_nested == 0) {
      arch_irq_unlock(key);
    }
  }
}

// send command for this hart
static inline void send_cmd(uint64_t cmd)
{
  pUVM_SW_IPC->cmd = cmd;
}


static inline void push_cmd_data(uint64_t data)
{
  uvm_sw_ipc_push_data(UVM_SW_IPC_CMD_ARGS_FIFO_IDX, data);
}


static inline bool pull_cmd_data(uint64_t *data)
{
  return uvm_sw_ipc_pull_data(UVM_SW_IPC_CMD_ARGS_FIFO_IDX, data);
}


void uvm_sw_ipc_quit()
{
  send_cmd(SYS_uvm_quit);
}


void uvm_sw_ipc_gen_event(uint32_t event_idx)
{
  send_cmd(SYS_uvm_gen_event | (event_idx<<16));
}


void uvm_sw_ipc_wait_event(uint32_t event_idx)
{
  uint64_t data = 0u;
  send_cmd(SYS_uvm_wait_event | (event_idx<<16));
  while (!pull_cmd_data(&data) || (data != event_idx))
    ;
}


void uvm_sw_ipc_push_data(uint32_t fifo_idx, uint64_t data)
{
  pUVM_SW_IPC->fifo_data_to_uvm[fifo_idx] = data;
}


bool uvm_sw_ipc_pull_data(uint32_t fifo_idx, uint64_t *data)
{
  bool empty;
  irq_lock();
  empty = (bool) ((pUVM_SW_IPC->fifo_data_to_sw_empty >> fifo_idx) & 0x1);
  if (!empty) {
    *data = pUVM_SW_IPC->fifo_data_to_sw[fifo_idx];
  }
  irq_unlock();
  return !empty;
}


#ifndef SKIP_PRINTF
static inline void uvm_sw_ipc_va(int log_level, uint32_t arg_cnt, char const *const str, va_list args) {
  push_cmd_data((uint64_t)str);
  for (uint32_t i = 0; i < arg_cnt; i++) {
    push_cmd_data((uint64_t)va_arg(args, uint64_t));
  }
  send_cmd(SYS_uvm_print | (log_level << 16));
}
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-function"
static inline void uvm_sw_ipc_va(int log_level, uint32_t arg_cnt, char const *const str, va_list args) {}
#pragma GCC diagnostic pop
#endif


void uvm_sw_ipc_printf_va_list(uint32_t arg_cnt, char const *const str, va_list args) {
  irq_lock();
  uvm_sw_ipc_va(UVM_PRINTF, arg_cnt, str, args);
  irq_unlock();
}


void uvm_sw_ipc_print_info(uint32_t arg_cnt, char const *const str,  ...) {
  va_list args;
  irq_lock();
  va_start(args, str);
  uvm_sw_ipc_va(UVM_LOG_LEVEL_INFO, arg_cnt, str, args);
  va_end(args);
  irq_unlock();
}


void uvm_sw_ipc_print_warning(uint32_t arg_cnt, char const *const str,  ...) {
  va_list args;
  irq_lock();
  va_start(args, str);
  uvm_sw_ipc_va(UVM_LOG_LEVEL_WARNING, arg_cnt, str, args);
  va_end(args);
  irq_unlock();
}


void uvm_sw_ipc_print_error(uint32_t arg_cnt, char const *const str,  ...) {
  va_list args;
  irq_lock();
  va_start(args, str);
  uvm_sw_ipc_va(UVM_LOG_LEVEL_ERROR, arg_cnt, str, args);
  va_end(args);
  irq_unlock();
}


void uvm_sw_ipc_print_fatal(uint32_t arg_cnt, char const *const str,  ...) {
  va_list args;
  irq_lock();
  va_start(args, str);
  uvm_sw_ipc_va(UVM_LOG_LEVEL_FATAL, arg_cnt, str, args);
  va_end(args);
  irq_unlock();
}


uint64_t uvm_sw_ipc_rand() {
  uint64_t random_data;
  irq_lock();
  send_cmd(SYS_uvm_rand);
  // pull data from cmd fifo
  while (!pull_cmd_data(&random_data)) {}
  irq_unlock();
  return random_data;
}


void uvm_sw_ipc_hdl_deposit(const char *path, uint64_t value) {
  irq_lock();
  push_cmd_data((uint64_t)path);
  push_cmd_data(value);
  send_cmd(SYS_uvm_hdl_deposit);
  irq_unlock();
}


void uvm_sw_ipc_hdl_force(const char *path, uint64_t value) {
  irq_lock();
  push_cmd_data((uint64_t)path);
  push_cmd_data(value);
  send_cmd(SYS_uvm_hdl_force);
  irq_unlock();
}


void uvm_sw_ipc_hdl_release(const char *path) {
  irq_lock();
  push_cmd_data((uint64_t)path);
  send_cmd(SYS_uvm_hdl_release);
  irq_unlock();
}


uint64_t uvm_sw_ipc_hdl_read(const char *path) {
  uint64_t read_data;
  irq_lock();
  push_cmd_data((uint64_t)path);
  send_cmd(SYS_uvm_hdl_read);
  // pull data from cmd fifo
  while (!pull_cmd_data(&read_data)) {}
  irq_unlock();
  return read_data;
}

int uvm_sw_ipc_memcmp(const void *s1, const void *s2, size_t n) {
  uint64_t ret;
  irq_lock();
  push_cmd_data((uint64_t)s1);
  push_cmd_data((uint64_t)s2);
  push_cmd_data((uint64_t)n);
  send_cmd(SYS_uvm_memcmp);
  while (!pull_cmd_data(&ret))
    ;
  irq_unlock();
  return (int)ret;
}

void *uvm_sw_ipc_memcpy(void *dst, const void *src, size_t n) {
  irq_lock();
  push_cmd_data((uint64_t)dst);
  push_cmd_data((uint64_t)src);
  push_cmd_data((uint64_t)n);
  send_cmd(SYS_uvm_memcpy);
  __sync_synchronize();
  irq_unlock();
  // no return value from UVM
  return dst;
}

void *uvm_sw_ipc_memset(void *s, int c, size_t n) {
  irq_lock();
  push_cmd_data((uint64_t)s);
  push_cmd_data((uint64_t)c);
  push_cmd_data((uint64_t)n);
  send_cmd(SYS_uvm_memset);
  __sync_synchronize();
  irq_unlock();
  // no return value from UVM
  return s;
}

void uvm_sw_ipc_disable_all_other_cpu_ipc() {
#ifndef APU
  uvm_sw_ipc_hdl_deposit("hdl_top.uvm_sw_ipc_apu_disable", 1);
#endif
}

void uvm_sw_ipc_udelay(uint32_t usec) {
  uint64_t read_data;
  send_cmd(SYS_uvm_udelay | (usec << 16));
  // Reserved delay event
  while (!pull_cmd_data(&read_data)) {}
  ASSERT(read_data == usec);
}
