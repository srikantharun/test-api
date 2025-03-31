/// Description: Package file containing top level parameter definitions for the APU Boot ROM
///
package apu_bootrom_pkg;

  parameter int unsigned APU_BOOTROM_NUM_WORDS = 8192;
  parameter int unsigned APU_BOOTROM_DATA_W = 64;
  parameter int unsigned APU_BOOTROM_STRB_W = APU_BOOTROM_DATA_W / 8;

  parameter int unsigned APU_BOOTROM_ADDR_W = $clog2(APU_BOOTROM_NUM_WORDS);

endpackage
