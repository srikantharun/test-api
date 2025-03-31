## Top IO

Following table describes top level IO pad list.

| IO Name | Direction | Width | Comments |
|--------------------------------|-----|----|---|
| i_ref_clk                      | in  | 1  ||
| i_clk_32k                      | in  | 0  ||
| i_tck                          | in  | 1  ||
| i_test_clk                     | in  | 1  ||
| i_spi_clk                      | in  | 1  ||
| o_spi_clk                      | out | 1  ||
| i_i2c_clk_0                    | in  | 1  ||
| i_i2c_clk_1                    | in  | 1  ||
| sd_emmc_clk                    | out | 1  ||
| i_por_rst_n                    | in  | 1  ||
| i_button_rst_n                 | in  | 1  ||
| i_pcie_perst_n                 | in  | 1  ||
| i_pcie_button_rst_n            | in  | 1  ||
| i_trst_n                       | in  | 1  ||
| i_uart_rx                      | in  | 1  ||
| o_uart_tx                      | out | 1  ||
| i_uart_cts_n                   | in  | 1  ||
| o_uart_rts_n                   | out | 1  ||
| o_spi_n[3:0]                   | out | 4  ||
| io_spi_sd[3:0]                 | bi  | 4  ||
| i_i2c_data_0                   | in  | 1  ||
| i_i2c_data_1                   | in  | 1  ||
| io_gpio[15:0]                  | bi  | 16 ||
| io_sd_emmc_cmd                 | bi  | 1  ||
| io_sd_emmc_data[7:0]           | bi  | 8  ||
| i_sd_emmc_strobe               | in  | 1  ||
| o_emmc_reset                   | out | 1  ||
| o_emmc_power                   | out | 1  ||
| i_sd_emmc_detect               | in  | 1  ||
| o_sd_emmc_wp                   | out | 1  ||
| o_sd_emmc_pu_pd                | out | 1  ||
| Observability[15:0]            | out | 16 ||
| o_thermal_warning              | out | 1  ||
| o_thermal_shutdown             | out | 1  ||
| i_throttle                     | in  | 1  ||
| i_boot_mode[2:0]               | in  | 3  ||
| i_security_tamper              | in  | 1  ||
| i_tms                          | in  | 1  ||
| i_td                           | in  | 1  ||
| o_td                           | out | 1  ||
| i_jtag_bscan_compliance_enable | in  | 1  ||
| dft_test                       | bi  | 45 ||
| efuse_vqps                     | bi  | 1  ||
| efuse_vddw                     | bi  | 1  ||


[comment]: # (add link to pads spreadsheet)
