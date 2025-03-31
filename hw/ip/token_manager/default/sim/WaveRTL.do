onerror resume
wave tags sim 
wave update off
wave zoom range 0 184824
wave add hdl_top.dut.i_cid -tag sim -radix hexadecimal
wave add hdl_top.dut.i_clk -tag sim -radix hexadecimal
wave add hdl_top.dut.i_rst_n -tag sim -radix hexadecimal
wave add hdl_top.dut.i_swep_is_acd -tag sim -radix hexadecimal
wave add hdl_top.dut.i_sync_mvm_exe_swep -tag sim -radix hexadecimal
wave add hdl_top.dut.i_sync_mvm_exe_swep_en -tag sim -radix hexadecimal -select
wave add hdl_top.dut.i_uid_to_vuid -tag sim -radix hexadecimal
wave add hdl_top.dut.i_vuid_to_uid -tag sim -radix hexadecimal
wave add hdl_top.dut.o_irq -tag sim -radix hexadecimal
wave group AXI -backgroundcolor #004466
wave add -group AXI hdl_top.dut.i_axi_s_ar -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.i_axi_s_aw -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.i_axi_s_b_ready -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.i_axi_s_r_ready -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.i_axi_s_w -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.o_axi_s_ar_ready -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.o_axi_s_aw_ready -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.o_axi_s_b -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.o_axi_s_r -tag sim -radix hexadecimal
wave add -group AXI hdl_top.dut.o_axi_s_w_ready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group DEV_TKN -backgroundcolor #006666
wave add -group DEV_TKN hdl_top.dut.i_dev_cons_ready -tag sim -radix hexadecimal
wave add -group DEV_TKN hdl_top.dut.i_dev_prod_valid -tag sim -radix hexadecimal
wave add -group DEV_TKN hdl_top.dut.o_dev_cons_valid -tag sim -radix hexadecimal -subitemconfig { {hdl_top.dut.o_dev_cons_valid[0]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[1]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[2]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[3]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[4]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[5]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[6]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[7]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[8]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[9]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[10]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[11]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[12]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[13]} {-radix hexadecimal} {hdl_top.dut.o_dev_cons_valid[14]} {-radix mnemonic} {hdl_top.dut.o_dev_cons_valid[15]} {-radix mnemonic} {hdl_top.dut.o_dev_cons_valid[16]} {-radix mnemonic} {hdl_top.dut.o_dev_cons_valid[17]} {-radix mnemonic} }
wave add -group DEV_TKN hdl_top.dut.o_dev_prod_ready -tag sim -radix hexadecimal -subitemconfig { {hdl_top.dut.o_dev_prod_ready[0]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[1]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[2]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[3]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[4]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[5]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[6]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[7]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[8]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[9]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[10]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[11]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[12]} {-radix hexadecimal} {hdl_top.dut.o_dev_prod_ready[13]} {-radix mnemonic} {hdl_top.dut.o_dev_prod_ready[14]} {-radix mnemonic} {hdl_top.dut.o_dev_prod_ready[15]} {-radix mnemonic} {hdl_top.dut.o_dev_prod_ready[16]} {-radix mnemonic} {hdl_top.dut.o_dev_prod_ready[17]} {-radix mnemonic} }
wave insertion [expr [wave index insertpoint] + 1]
wave group TOP_TKN -backgroundcolor #226600
wave add -group TOP_TKN hdl_top.dut.i_top_cons_ready -tag sim -radix hexadecimal
wave add -group TOP_TKN hdl_top.dut.i_top_prod_valid -tag sim -radix hexadecimal
wave add -group TOP_TKN hdl_top.dut.o_top_cons_valid -tag sim -radix hexadecimal
wave add -group TOP_TKN hdl_top.dut.o_top_prod_ready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group OCPL -backgroundcolor #666600
wave add -group OCPL hdl_top.dut.i_tok_cons_ocpl_s_maddr -tag sim -radix hexadecimal
wave add -group OCPL hdl_top.dut.i_tok_cons_ocpl_s_mcmd -tag sim -radix hexadecimal
wave add -group OCPL hdl_top.dut.i_tok_cons_ocpl_s_mdata -tag sim -radix hexadecimal
wave add -group OCPL hdl_top.dut.i_tok_prod_ocpl_m_scmdaccept -tag sim -radix hexadecimal
wave add -group OCPL hdl_top.dut.o_tok_cons_ocpl_s_scmdaccept -tag sim -radix hexadecimal
wave add -group OCPL hdl_top.dut.o_tok_prod_ocpl_m_maddr -tag sim -radix hexadecimal
wave add -group OCPL hdl_top.dut.o_tok_prod_ocpl_m_mcmd -tag sim -radix hexadecimal
wave add -group OCPL hdl_top.dut.o_tok_prod_ocpl_m_mdata -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group ACD_TKN -backgroundcolor #664400
wave add -group ACD_TKN hdl_top.dut.i_acd_cons_ready -tag sim -radix hexadecimal
wave add -group ACD_TKN hdl_top.dut.i_acd_prod_valid -tag sim -radix hexadecimal
wave add -group ACD_TKN hdl_top.dut.o_acd_cons_valid -tag sim -radix hexadecimal
wave add -group ACD_TKN hdl_top.dut.o_acd_prod_ready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group ACD_TKN -collapse
wave group OCPL -collapse
wave group TOP_TKN -collapse
wave group DEV_TKN -collapse
wave group AXI -collapse
wave update on
wave top 0
