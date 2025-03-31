## Copied from SNPS FC read design setup.
##==============================================================================
## Use change_link here to select either _NS or _EW (or maybe both).
## You must use the -force option since some outputs (e.g. atpg_so)
## are unconnected in the source RTL.
## These unconnected outputs causes design_compiler to complain.
##==============================================================================
##-- Example: map ZCAL instances to EW
change_link  [get_cells -hierarchical -filter "ref_name == dwc_lpddr5xphyzcal_top"] dwc_lpddr5xphyzcal_top_ew

##-- Example: map MASTER instances to EW
change_link  [get_cells -hierarchical -filter "ref_name == dwc_lpddr5xphymaster_top"] dwc_lpddr5xphymaster_top_ew

##-- Example: map CMOSX2 instances to EW
change_link  [get_cells -hierarchical -filter "ref_name == dwc_lpddr5xphycmosx2_top"] dwc_lpddr5xphycmosx2_top_ew

##-- Example: map DX4 instances to EW
change_link  [get_cells -hierarchical -filter "ref_name == dwc_lpddr5xphydx4_top"] dwc_lpddr5xphydx4_top_ew

##-- Example: map DX5 instances to EW
change_link  [get_cells -hierarchical -filter "ref_name == dwc_lpddr5xphydx5_top"] dwc_lpddr5xphydx5_top_ew

##-- Example: map acx2 instances to EW
change_link  [get_cells -hierarchical -filter "ref_name == dwc_lpddr5xphyacx2_top"] dwc_lpddr5xphyacx2_top_ew

##-- Example: map CKX2 instances to EW
change_link  [get_cells -hierarchical -filter "ref_name == dwc_lpddr5xphyckx2_top"] dwc_lpddr5xphyckx2_top_ew

##-- Example: map CSX2 instances to EW
change_link  [get_cells -hierarchical -filter "ref_name == dwc_lpddr5xphycsx2_top"] dwc_lpddr5xphycsx2_top_ew


link -incremental -verbose
