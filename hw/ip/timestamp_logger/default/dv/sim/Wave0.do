onerror resume
wave tags  sim
wave update off
wave zoom range 0 3635629
wave group PARAMETERS -backgroundcolor #004466
wave add -group PARAMETERS hdl_top.i_dut.NumGroups -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.AxiSIdWidth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.AxiMIdWidth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.AxiAddrWidth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.AxiDataWidth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.GroupDefaultFifoDepth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.GroupMsgWidth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.GroupFifoDepth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.TimestampFifoDepth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.MemDepth -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.UseMacro -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.REGION_ST_ADDR -tag sim -radix hexadecimal
wave add -group PARAMETERS hdl_top.i_dut.REGION_END_ADDR -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave add hdl_top.i_dut.i_clk -tag sim -radix hexadecimal
wave add hdl_top.i_dut.i_rst_n -tag sim -radix hexadecimal
wave add hdl_top.i_dut.i_group_trigger -tag sim -radix hexadecimal -subitemconfig { {hdl_top.i_dut.i_group_trigger[6]} {-radix hexadecimal} {hdl_top.i_dut.i_group_trigger[5]} {-radix hexadecimal} {hdl_top.i_dut.i_group_trigger[4]} {-radix hexadecimal} {hdl_top.i_dut.i_group_trigger[3]} {-radix hexadecimal} {hdl_top.i_dut.i_group_trigger[2]} {-radix hexadecimal} {hdl_top.i_dut.i_group_trigger[1]} {-radix hexadecimal} {hdl_top.i_dut.i_group_trigger[0]} {-radix hexadecimal} }
wave add hdl_top.i_dut.i_group_message -tag sim -radix hexadecimal
wave add hdl_top.i_dut.i_sync_start -tag sim -radix hexadecimal
wave add hdl_top.i_dut.timestamp -tag sim -radix hexadecimal
wave group WRITES -backgroundcolor #004466
wave add -group WRITES hdl_top.i_dut.i_axi_s_aw_valid -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.o_axi_s_aw_ready -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_aw_id -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_aw_addr -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_aw_len -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_aw_burst -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_aw_size -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_w_valid -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.o_axi_s_w_ready -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_w_strb -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_w_data -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_w_last -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.o_axi_s_b_valid -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.i_axi_s_b_ready -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.o_axi_s_b_id -tag sim -radix hexadecimal
wave add -group WRITES hdl_top.i_dut.o_axi_s_b_resp -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group READS -backgroundcolor #006666
wave add -group READS hdl_top.i_dut.i_axi_s_ar_valid -tag sim -radix hexadecimal
wave add -group READS hdl_top.i_dut.o_axi_s_ar_ready -tag sim -radix hexadecimal
wave add -group READS hdl_top.i_dut.i_axi_s_ar_addr -tag sim -radix hexadecimal
wave add -group READS hdl_top.i_dut.o_axi_s_r_valid -tag sim -radix hexadecimal
wave add -group READS hdl_top.i_dut.i_axi_s_r_ready -tag sim -radix hexadecimal
wave add -group READS hdl_top.i_dut.o_axi_s_r_data -tag sim -radix hexadecimal
wave add -group READS hdl_top.i_dut.o_axi_s_r_last -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {SLAVE WRITES} -backgroundcolor #004466 -select
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_aw_valid -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.i_axi_m_aw_ready -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_aw_addr -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_aw_id -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_aw_burst -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_aw_len -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_aw_size -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_w_valid -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.i_axi_m_w_ready -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_w_data -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_w_last -tag sim -radix hexadecimal
wave add -group {SLAVE WRITES} hdl_top.i_dut.o_axi_m_w_strb -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave add {hdl_top.i_dut.u_csr.u_ctrl_capture_enable.q[0]} -tag sim -radix hexadecimal
wave add {hdl_top.i_dut.u_csr.u_ctrl_trace_mode.q[0]} -tag sim -radix hexadecimal
wave add {hdl_top.i_dut.u_csr.u_ctrl_external_mode.q[0]} -tag sim -radix hexadecimal
wave add hdl_top.i_dut.u_csr.u_ctrl_cntr_division.q -tag sim -radix hexadecimal
wave add hdl_top.i_dut.u_csr.u_group_en_0_63.q -tag sim -radix hexadecimal
wave add hdl_top.i_dut.u_csr.u_entry_count.q -tag sim -radix hexadecimal
wave group {SLAVE WRITES} -collapse
wave group READS -collapse
wave group WRITES -collapse
wave group PARAMETERS -collapse
wave update on
wave top 0
