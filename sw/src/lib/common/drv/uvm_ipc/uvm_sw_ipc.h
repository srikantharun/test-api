#ifndef UVM_SW_IPC_H
#define UVM_SW_IPC_H

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

//#include <cache.h>
//#include <core_v5.h>

// Values taken from uvm_sw_ipc_pkg.sv
#define UVM_SW_IPC_DATA_FIFO_NB 2
#define UVM_SW_IPC_FIFO_NB (UVM_SW_IPC_DATA_FIFO_NB + 1)
#define UVM_SW_IPC_CMD_ARGS_FIFO_IDX (UVM_SW_IPC_FIFO_NB - 1)

// see: https://github.com/bminor/newlib/blob/master/libgloss/riscv/machine/syscall.h
// UVM syscalls
#define SYS_uvm_print 32
#define SYS_uvm_gen_event 33
#define SYS_uvm_wait_event 34
#define SYS_uvm_quit 35
#define SYS_uvm_rand 36
#define SYS_uvm_hdl_deposit 37
#define SYS_uvm_hdl_force 38
#define SYS_uvm_hdl_release 39
#define SYS_uvm_hdl_read 40
#define SYS_uvm_memcmp 41
#define SYS_uvm_memcpy 42
#define SYS_uvm_memset 43
#define SYS_uvm_udelay 44

#define UVM_LOG_LEVEL_INFO     0
#define UVM_LOG_LEVEL_WARNING  1
#define UVM_LOG_LEVEL_ERROR    2
#define UVM_LOG_LEVEL_FATAL    3
#define UVM_PRINTF             4

// low-level API
typedef struct {
  uint64_t cmd;
  uint64_t fifo_data_to_uvm[UVM_SW_IPC_FIFO_NB]; // write: push in   fifo_data_to_uvm[k]
  uint64_t fifo_data_to_sw[UVM_SW_IPC_FIFO_NB];  // read:  pull from fifo_data_to_sw[k]
  uint64_t fifo_data_to_sw_empty;                // [k]:   fifo_data_to_sw[k] is empty
} uvm_sw_ipc_st;

// high-level API
void uvm_sw_ipc_quit(void);
void uvm_sw_ipc_gen_event(uint32_t event_idx);
void uvm_sw_ipc_wait_event(uint32_t event_idx); // interruptable
void uvm_sw_ipc_push_data(uint32_t fifo_idx, uint64_t data);
bool uvm_sw_ipc_pull_data(uint32_t fifo_idx, uint64_t *data);
void uvm_sw_ipc_print_info(uint32_t arg_cnt, char const *const str,  ...);
void uvm_sw_ipc_print_warning(uint32_t arg_cnt, char const *const str,  ...);
void uvm_sw_ipc_print_error(uint32_t arg_cnt, char const *const str,  ...);
void uvm_sw_ipc_print_fatal(uint32_t arg_cnt, char const *const str,  ...);
void uvm_sw_ipc_printf_va_list(uint32_t arg_cnt, char const *const str, va_list args);
uint64_t uvm_sw_ipc_rand();

// sets the given hdl ~path~ to the specified ~value~
void uvm_sw_ipc_hdl_deposit(const char *path, uint64_t value);
// forces the ~value~ on the given ~path~
void uvm_sw_ipc_hdl_force(const char *path, uint64_t value);
// releases a value previously set with <uvm_sw_ipc_hdl_force>
void uvm_sw_ipc_hdl_release(const char *path);
// gets the value at the given ~path~
uint64_t uvm_sw_ipc_hdl_read(const char *path);

// memcmp: requires 8-byte alignment of pointers and length
int uvm_sw_ipc_memcmp(const void *s1, const void *s2, size_t n);
// memcpy: requires 8-byte alignment of pointers and length
void *uvm_sw_ipc_memcpy(void *dst, const void *src, size_t n);
// memset: requires 8-byte alignment of pointer and length
void *uvm_sw_ipc_memset(void *s, int c, size_t n);

// disable all other CPU's uvm_sw_ipc, usefull when accessing DLM of other CPU
void uvm_sw_ipc_disable_all_other_cpu_ipc();
// Use the UVM to halt the program's execution for a set amount of time
void uvm_sw_ipc_udelay(uint32_t udelay); // interruptable

#endif
