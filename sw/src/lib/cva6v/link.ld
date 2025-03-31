/*
 * Linker script for CVA6V standalone platform (cva6v.*).
 *
 * This uses a generic Spike-style memory map.
 *
 * WARNING: This file is also used by a build flow in
 *          $REPO_ROOT/hw/vendor/axelera/cva6v/default/dv.
 */
OUTPUT_ARCH( "riscv" )

MEMORY
{
  cacheable     : ORIGIN = 0x2000000000, LENGTH = 0x1000000
  uncacheable   : ORIGIN = 0x3000000000, LENGTH = 0x10000
}

SECTIONS
{
  .text.init : ALIGN(64) {
    *(.text.init)
    /* rvtest are based on a single assembly file and require a custom entry */
    start = DEFINED(rvtest_entry_point) ? rvtest_entry_point : _start;
  } > cacheable
  .tohost : ALIGN(0x1000) {
    *(.tohost)
    . = ALIGN(0x1000); /* ensure proper alignment of next section */
  } > cacheable
  /* code */
  .text : ALIGN(64) {
    *(.text .text.*)
  } > cacheable
  /* data */
  .rodata : ALIGN(64) {
    *(.rodata .rodata.*)
  } > cacheable
  .data : ALIGN(64) {
    *(.data .data.*)
  } > cacheable
  .sdata : ALIGN(64) {
    __global_pointer$ = . + 0x800;
    *(.srodata .srodata.*)
    *(.sdata .sdata.*)
    *(.gnu.linkonce.s.*)
  } > cacheable
  .bss : ALIGN(0x1000) {
    _bss_begin = .;
    *(.sbss .sbss.*) /* store .sbss into .bss. oss test suite has some problem storing global variables into the small bss */
    *(.scommon .scommon.*)
    *(.gnu.linkonce.sb.*)
    *(.bss .bss.*)
    . = ALIGN(64); /* ensure _bss_end is 64-byte aligned */
    _bss_end = .;
  } > cacheable
  /* 64-byte aligned as this is the same alignment that will be used at runtime */
  . = ALIGN(64);
  _thread_pointer = .;
  .tdata : ALIGN(64) {
    _tdata_begin = .;
    *(.tdata .tdata.*)
    . = ALIGN(64); /* required to ensure proper alignment at runtime as .tbss
                    * will be place immediately after .tdata at runtime */
    _tdata_end = .;
  } > cacheable
  .tbss : ALIGN(64) {
    _tbss_begin = .;
    *(.tbss .tbss.*)
    _tbss_end = .;
  } > cacheable
  _tls_alloc_size = _tbss_end - _tdata_begin;

  .runtime.tls : ALIGN(64) {
    _tls_begin = .;
    . = . + _tls_alloc_size;
    _tls_end = .;
  } > cacheable
  .runtime.stack : ALIGN(64) {
    _stack_begin = .;
    . = . + 128K; /* CVA6V_STANDALONE_STACK_SIZE as defined in stack.h */
    _stack_end = .;
  } > cacheable
  _end = .;

  /* Breker Mailboxes */
  .breker : ALIGN(0x1000) {
    *(.breker)
    . = ALIGN(0x1000); /* ensure proper alignment of next section */
  } > uncacheable

}
