Top-level clock interface:

|clock|freq|description|
|-----|----|-----------|
|i_ref_clk| 20 MHz | reference clock |
|i_clk_32k| RTC |
|i_ref_pad_clk_n|pcie differential pair N reference clock|
|i_ref_pad_clk_p|pcie differential pair P reference clock|
|tck|100 MHz|JTAG clock|
|i_ssn_clk| for scan test |
|i_ssn_clk (test_clk) | for pcie macro test |


Generated clocks:

|src clock|generated clock|Freq|description|
|---------|---------------|----|-----------|
|i_ref_clk|fast_clk|1200MHz|||
|i_ref_clk|codec_clk|600MHz|||
|i_ref_clk|emmc_clk|200MHz|||
|i_ref_clk|periph_clk|100MHz|||
|i_ref_clk|ddr_east_ref_clk|800MHz|||
|i_ref_clk|ddr_west_ref_clk|800MHz|||

Pad clock connections:

|Blocks|i_ref_clk|i_clk_32k|tck|i_ref_pad_clk_n|i_ref_pad_clk_p|i_ssn_clk|i_ssn_clk_2|
|------|---------|---------|---|---------------|---------------|---------|-----------|
|APU|x||x|||x||
|AIC|x||x|||x||
|DECODER|x||x|||x||
|L2|x||x|||x||
|LPDDR|x||x|||x||
|NOC|x||x|||x||
|PCIE|x||x|||x||
|PVE|x||x|||x||
|SOC MGMT|x||x|||x||
|SOC PERIPH|x||x|||x||
|SOC SPM|x||x|||x||

Generated clock connections:

|Blocks|fast_clk|codec_clk|emmc_clk|periph_clk|ddr_east_ref_clk|ddr_west_ref_clk|
|------|--------|---------|--------|----------|----------------|----------------|
|APU|x|||x|||
|AIC|x|||x|||
|DECODER|x|x||x|||
|L2|x|||x|||
|LPDDR|x|||x|x|x|
|NOC|x|||x|||
|PCIE|x|||x|||
|PVE|x|||x|||
|SOC MGMT|x|||x|||
|SOC PERIPH|x|||x|||
|SOC SPM|x|||x|||
