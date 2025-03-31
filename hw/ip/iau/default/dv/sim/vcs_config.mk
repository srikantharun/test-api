
#Waiting more cycles because in the parameter it only waits for 16 cycles
VCS_ELAB_OPTS_EXT += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.AWREADY_MAXWAITS=1000
VCS_ELAB_OPTS_EXT += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.ARREADY_MAXWAITS=1000
VCS_ELAB_OPTS_EXT += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.WREADY_MAXWAITS=1000
VCS_ELAB_OPTS_EXT += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.BREADY_MAXWAITS=1000
VCS_ELAB_OPTS_EXT += -pvalue+hdl_top.dut.AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER.RREADY_MAXWAITS=1000

ifeq ($(DUMP_ENABLE),1)
  VCS_ELAB_OPTS_EXT += -debug_access+all
  VCS_RUN_OPTS += -ucli -do ../../dump.tcl
endif

