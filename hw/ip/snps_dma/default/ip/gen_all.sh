coreConsultant -shell -f ../data/aic_ht_dma.cc.cfg
coreConsultant -shell -f ../data/aic_lt_dma.cc.cfg
coreConsultant -shell -f ../data/apu_dma.cc.cfg

ralf_to_hjson -o ../data/aic_ht_dw_axi_dmac.hjson aic_ht_dma/export/DW_axi_dmac_uvm.ralf
ralf_to_hjson -o ../data/aic_lt_dw_axi_dmac.hjson aic_lt_dma/export/DW_axi_dmac_uvm.ralf
ralf_to_hjson -o ../data/apu_dw_axi_dmac.hjson apu_dma/export/DW_axi_dmac_uvm.ralf
