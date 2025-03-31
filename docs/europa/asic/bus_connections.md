# Top level AMBA bus connections

Top level AMBA buses are connected between sub-systems and NoC.

## AXI-4

| sub_system | Bus on sub-system | Bus on NoC | clk | description |
| ---------- |-------------------|------------|-----|-------------|
| AIC [0 .. 7] | ht_axi_m | aic_[0 .. 7]_init_ht_axi_s | fast_clk |  |
| AIC [0 .. 7] | lt_axi_m | aic_[0 .. 7]_init_lt_axi_s | fast_clk |  |
| AIC [0 .. 7] | lt_axi_s | aic_[0 .. 7]_targ_lt_axi_m | fast_clk |  |
| APU | mt_axi_m | apu_init_mt_axi_s | fast_clk |  |
| APU | lt_axi_m | apu_init_lt_axi_s | fast_clk |  |
| APU | lt_axi_s | apu_targ_lt_axi_m | fast_clk |  |
| DECODER | dec_0_axi_m | decoder_dec_0_init_mt_axi_s | fast_clk |  |
| DECODER | dec_1_axi_m | decoder_dec_1_init_mt_axi_s | fast_clk |  |
| DECODER | mcu_axi_m | decoder_mcu_init_mt_axi_s | fast_clk |  |
| L2 module [0 .. 7] | ht_axi_s | l2_[0 .. 7]_targ_ht_axi_m | fast_clk |  |
| LPDDR_PPP [0 .. 3] | ht_axi_s | lpddr_ppp_[0 .. 3]_targ_mt_axi_m | fast_clk |  |
| LPDDR_GRAPH [0 .. 3] | ht_axi_s | lpddr_graph_[0 .. 3]_targ_mt_axi_m | fast_clk |  |
| PCIE | mt_axi_m | pcie_init_mt_axi_s | fast_clk |  |
| PCIE | mt_axi_s | pcie_targ_mt_axi_m | fast_clk |  |
| PCIE | lt_axi_s | pcie_targ_lt_axi_m | fast_clk |  |
| PVE [0,1] | ctrlo_axi_m | pve_[0,1]_init_lt_axi_s | fast_clk |  |
| PVE [0,1] | ctrli_axi_s | pve_[0,1]_targ_lt_axi_m | fast_clk |  |
| PVE [0,1] | dma_axi_m | pve_[0,1]_init_ht_axi_s | fast_clk |  |
| SOC MGMT | lt_axi_m | soc_mgmt_init_lt_axi_s | fast_clk |  |
| SOC MGMT | lt_axi_s | soc_mgmt_targ_lt_axi_m | fast_clk |  |
| SOC PERIPH | lt_axi_s | soc_periph_targ_lt_axi_m | fast_clk |  |
| SOC SPM | lt_axi_s | soc_spm_targ_lt_axi_m | fast_clk |  |

## APB

| sub_system | Bus on sub-system | Bus on NoC | clk | description |
| ---------- |-------------------|------------|-----|-------------|
| AIC [0 .. 7] | cfg_apb4_s | aic_[0 .. 7]_targ_syscfg_apb_m | ref_clk |  |
| APU |  |  |  |  |
| DECODER | cfg_apb4_s | decoder_targ_cfg_apb_m | ref_clk |  |
| DECODER | syscfg_apb4_s | decoder_targ_syscfg_apb_m | ref_clk |  |
| L2 module [0 .. 7] | cfg_apb4_s | l2_[0 .. 7]_targ_syscfg_apb_m | ref_clk |  |
| LPDDR_PPP [0 .. 3] | cfg_apb3_s | lpddr_ppp_[0 .. 3]_targ_phy_cfg_apb3_m | ref_clk |  |
| LPDDR_PPP [0 .. 3] | syscfg_apb4_s | lpddr_ppp_[0 .. 3]_targ_syscfg_apb_m | ref_clk |  |
| LPDDR_GRAPH [0 .. 3] | cfg_apb3_s | lpddr_graph_[0 .. 3]_targ_phy_cfg_apb3_m | ref_clk |  |
| LPDDR_GRAPH [0 .. 3] | syscfg_apb4_s | lpddr_graph_[0 .. 3]_targ_syscfg_apb_m | ref_clk |  |
| PCIE | cfg_apb4_s | pcie_targ_syscfg_apb_m | ref_clk |  |
| PVE [0,1] |  |  |  |  |
| SOC MGMT | sys_cfg_apb_m | soc_mgmt_init_syscfg_apb_s | ref_clk |  |
| SOC PERIPH | cfg_apb4_s | soc_periph_targ_syscfg_apb_m | ref_clk |  |
| SOC SPM | cfg_apb4_s | sys_spm_targ_syscfg_apb_m | ref_clk |  |
