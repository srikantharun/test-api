onerror resume
wave tags  F0
wave update off
wave zoom range 39985109518 40001140482
wave group Reset -backgroundcolor #004466
wave add -group Reset hdl_top.LPDDR_P_SUBSYSTEM.lpddr_rsts_n -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group pctl_apb -backgroundcolor #006666
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_paddr -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_pwdata -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_pwrite -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_psel -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_penable -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_pstrb -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_pprot -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_syscfg_apb4_s_pready -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_syscfg_apb4_s_prdata -tag F0 -radix hexadecimal
wave add -group pctl_apb hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_syscfg_apb4_s_pslverr -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group config_apb -backgroundcolor #226600
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr -tag F0 -radix hexadecimal -representation twoscomplement -subitemconfig { {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[31]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[30]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[29]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[28]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[27]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[26]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[25]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[24]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[23]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[22]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[21]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[20]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[19]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[18]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[17]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[16]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[15]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[14]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[13]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[12]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[11]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[10]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[9]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[8]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[7]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[6]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[5]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[4]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[3]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[2]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[1]} {-radix mnemonic} {hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[0]} {-radix mnemonic} }
wave expr -group config_apb  -alias rightshift -radix hexadecimal {(hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[31:0] >> 2)} -select
wave expr -group config_apb  -alias leftshift -radix hexadecimal {(hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr[31:0] << 2)}
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_penable -tag F0 -radix hexadecimal
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_pprot -tag F0 -radix hexadecimal
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_psel -tag F0 -radix hexadecimal
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_pstrb -tag F0 -radix hexadecimal
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_pwdata -tag F0 -radix hexadecimal
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_pwrite -tag F0 -radix hexadecimal
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_cfg_apb4_s_prdata -tag F0 -radix hexadecimal
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_cfg_apb4_s_pready -tag F0 -radix hexadecimal
wave add -group config_apb hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_cfg_apb4_s_pslverr -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group pctl_apb -collapse
wave update on
wave top 0
wave bio set 53c19 Blue
wave bio set 1408bc Blue
