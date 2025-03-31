namespace eval Axelera {
  set DUT __DUT__
  set INTERRUPTABLE_TEST 1
}
source common.tcl

fast_printf __FAST_PRINTF__

if {"__TEST_BINARY_BASEPATH__" != ""} {
  download_binaries "__TEST_BINARY_BASEPATH__"
}

if {"__EMMC_HEX_FILE__" != ""} {
  download_emmc_binaries "__EMMC_HEX_FILE__"
}
init_emmc_softmodel

if {"__SPI_HEX_FILE__" != ""} {
  init_spi_softmodel "__SPI_HEX_FILE__"
}

dump_cpu_instructions "ax65" __ENABLE_DUMP_AX65_INSTRUCTIONS__
dump_cpu_instructions "cva6v" __ENABLE_DUMP_CVA6V_INSTRUCTIONS__
download_kse_bootrom __KSE_BOOTROM_FILES__ __TEST_NAME__

run_reset_sequence
clock_set_config "__CLOCK_CONFIG__" "__PLATFORM_NAME__"

puts "start: __TEST_NAME__"
run_until_completion
report_test_status "__TEST_NAME__"

# close cpu instructions
if {__ENABLE_DUMP_AX65_INSTRUCTIONS__} {close_cpu_instructions "ax65"}
if {__ENABLE_DUMP_CVA6V_INSTRUCTIONS__} {close_cpu_instructions "cva6v"}
