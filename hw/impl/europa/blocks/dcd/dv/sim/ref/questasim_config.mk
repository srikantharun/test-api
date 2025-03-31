#############################################
# Add VSIM Run and Elab options for cva6v
#############################################

# Use actual clock frequencies
# APB freq = 600MHz
# AXI freq = 600MHz
#  IP freq = 600MHz
# MCU freq = 1200MHz
VSIM_VOPT_OPTS_EXT  += -gAPB_HALF_PERIOD=833
VSIM_VOPT_OPTS_EXT  += -gAXI_HALF_PERIOD=833
VSIM_VOPT_OPTS_EXT  += -gIP_HALF_PERIOD=833
VSIM_VOPT_OPTS_EXT  += -gMCU_HALF_PERIOD=416

VSIM_VOPT_OPTS_EXT += -access=rw+/. # Short term - avoids internal segfault with vsim
#Suppressible compile errors:
#vlog-2986: The hierarchical reference 'module.something' is not legal in a constant expression context.
#vlog-2125: Associative array string index must be a string variable or literal.
#vlog-13262: A virtual interface element is not allowed in a sensitivity list.
VSIM_VLOG_OPTS_EXT += -suppress 2986,2125,13262
VSIM_RUN_OPTS_EXT  += -suppress 3829 #** Warning: (vsim-3829) Non-existent associative array entry. Returning default value

# AXI VIP configuration defines
VSIM_VLOG_OPTS += +define+AXI_VIP
VSIM_VLOG_OPTS += +define+SYNOPSYS_SV

#** Error (suppressible): ** while parsing file included at /home/projects_2/workspace/sgros/clone02/hw/dv/svt_amba_vip/svt_amba.uvm.pkg.sv(44)
#** at /opt/synopsys/dware/eu001-1.0/vip/svt/common/T-2022.03/sverilog/src/mti/svt_err_check_stats_cov.svp(286): (vlog-2147) Expressions in 'bins' size, value or transition specification must
#be constant or covergroup constructor argument.
# and many others similar (svt_amba_vip)
VSIM_VLOG_OPTS_EXT += -suppress 2147

#** Error (suppressible): /opt/synopsys/dware/eu001-1.0/vip/svt/amba_svt/S-2021.12/sverilog/src/mti/svt_axi_transaction.svp(17305): (vlog-2577) Enum type mismatch between operands of '>' expression.
# and many others similar (svt_amba_vip)
VSIM_VLOG_OPTS_EXT += -suppress 2577

#** Error (suppressible): /home/projects_2/workspace/sgros/clone02/hw/vendor/allegro/codec/default/dv/sim/ref/../../allegro_tb/tbench/alg_ip_top_tb.sv(269): (vopt-3838) Variable 'awvalid' written by continuous and procedural assignments.
#One of the assignments is implicit. See //home/projects/europa_vip/amba_system_env_svt/include/sverilog/svt_axi_master_if.svi(104).
# and many others similar (svt_amba_vip)
VSIM_VOPT_OPTS_EXT += -suppress 3838
VSIM_ELAB_OPTS_EXT += -suppress 3838

# ** Error (suppressible): (vsim-8451) /opt/synopsys/dware/eu001-1.0/vip/svt/common/T-2022.03/sverilog/src/mti/svt_gpio_driver_common.svp(113): Virtual interface resolution cannot find a matching instance for 'virtual svt_gpio_if'.
#    Time: 0 ps  Iteration: 0  Instance: /alg_ip_top_tb File: /opt/synopsys/dware/eu001-1.0/vip/svt/common/T-2022.03/sverilog/src/mti/svt_gpio_driver_common.svp Line: 113
# and many others similar (svt_amba_vip)
VSIM_ELAB_OPTS_EXT += -suppress 8451

# Error when trying to connect inout port of the axi VIP interface to "logic" ports
# (vopt-8885) Illegal inout port connection for 'awaddr' (1st connection) to reg type.
VSIM_VOPT_OPTS_EXT += -suppress 8885
VSIM_ELAB_OPTS_EXT += -suppress 8885

# inout assigned to 'h0 cause this error
# Error (suppressible): (vsim-3053) Illegal output or inout port connection for port 'awakeup'
VSIM_ELAB_OPTS_EXT += -suppress 3053

ifeq ("$(USE_SF5A_MODELS)", "1")
VSIM_ELAB_OPTS_EXT+= +nospecify
endif
 
VHDL_STD_NOWARNINGS = 1
