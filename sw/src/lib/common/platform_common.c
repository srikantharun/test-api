#include <stddef.h>
#include <stdint.h>

#include <asm.h>
#include <platform.h>
#include <string.h>

// initialize BSS
void _init_bss()
{
  extern char _bss_begin, _bss_end;
  size_t bss_size = &_bss_end - &_bss_begin;
  memset(&_bss_begin, 0, bss_size);
}

// initialize thread-local storage
//
// Linkers require that ELFs only contain a single TLS segment, i.e., that all
// thread-local data is stored contiguously in memory. This is required, as the
// linker needs to know what offset (relative to the thread pointer) each
// thread-local symbol has.
//
// This poses a problem for us, as the .tdata/.tbss sections for the different
// processes would naturally end up in different places (next to the other code
// and data in the respective SPMs).
//
// To resolve this problem, the following setup is used:
//   - All .tdata and .tbss sections are stored contiguously in Sys-SPM.
//   - At startup, each core copies their .tdata/.tbss sections to their local
//     SPM memory.
//   - The thread pointers are offset such that the offset between thread
//     pointer and TLS symbols (both in local memory) matches the offset between
//     the start of the TLS segment and the symbols in .tdata/.tbss (both in
//     Sys-SPM).
void _init_tls()
{
  // find runtime TLS area
  extern char _tls_begin, _tls_alloc_size;
#ifdef SYSTEM_CVA6V
  uint64_t hart_offset = 0; // assume single core
#else
  // for AICORE/PVE standalone, the correct hart IDs are used, meaning this
  // general solution still works
  uint64_t hart_offset = r_mhartid() - processor_first_hart_id();
#endif
  void *tls = &_tls_begin + hart_offset * (size_t)&_tls_alloc_size;

  // prepare .tdata
  extern char _tdata_begin, _tdata_end;
  size_t tdata_size = &_tdata_end - &_tdata_begin;
  memcpy(tls, &_tdata_begin, tdata_size);

  // prepare .tbss
#ifndef NO_INIT_BSS_AND_TLS
  extern char _tbss_end;
  size_t tbss_size = &_tbss_end - &_tdata_end;
  memset(tls + tdata_size, 0, tbss_size);
#endif

  // set thread pointer
#ifdef SYSTEM_TOP
  // NOTE: The linker assumes the thread pointer to be set to the start of APU
  //       thread-local storage. This means that the start of this processor's
  //       .tdata is not expected at (tp + 0), but expected to be offset by
  //       ((this processor's .tdata) - (APU .tdata)).
  extern char _thread_pointer;
  size_t tp_offset = &_tdata_begin - &_thread_pointer;
#else
  // non-top systems only have one .tdata, meaning the offset is always zero
  size_t tp_offset = 0;
#endif
  void *tp = tls - tp_offset;
  asm volatile ("mv tp, %0" :: "r" (tp));
}
