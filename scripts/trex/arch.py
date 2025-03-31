# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

""" Define the architecture of Europa ."""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------
# Dict to indicate the initiators (CPUs) in the system and the DMAs they are allowed to configure
Arch = {
    'APU':  {"LP_DMA_APU" : "SNPS_DW","SDMA0" : "AXE", 'SDMA1': "AXE" ,'PCIE': "SNPS_PCIE"},
    'AI0':  {"LP_DMA_AI0" : "SNPS_DW","HP_DMA_AI0": "AXE", "SDMA0": "AXE", "SDMA1": "AXE"},
    'AI1':  {"LP_DMA_AI1" : "SNPS_DW","HP_DMA_AI1": "AXE", "SDMA0": "AXE", "SDMA1": "AXE"},
    'AI2':  {"LP_DMA_AI2" : "SNPS_DW","HP_DMA_AI2": "AXE", "SDMA0": "AXE", "SDMA1": "AXE"},
    'AI3':  {"LP_DMA_AI3" : "SNPS_DW","HP_DMA_AI3": "AXE", "SDMA0": "AXE", "SDMA1": "AXE"},
    'AI4':  {"LP_DMA_AI4" : "SNPS_DW","HP_DMA_AI4": "AXE", "SDMA0": "AXE", "SDMA1": "AXE"},
    'AI5':  {"LP_DMA_AI5" : "SNPS_DW","HP_DMA_AI5": "AXE", "SDMA0": "AXE", "SDMA1": "AXE"},
    'AI6':  {"LP_DMA_AI6" : "SNPS_DW","HP_DMA_AI6": "AXE", "SDMA0": "AXE", "SDMA1": "AXE"},
    'AI7':  {"LP_DMA_AI7" : "SNPS_DW","HP_DMA_AI7": "AXE", "SDMA0": "AXE", "SDMA1": "AXE"},
    'PVE0': {'HP_DMA0_PVE0':"AXE",'HP_DMA1_PVE0':"AXE"},
    'PVE1': {'HP_DMA0_PVE1':"AXE",'HP_DMA1_PVE1':"AXE"}
}
