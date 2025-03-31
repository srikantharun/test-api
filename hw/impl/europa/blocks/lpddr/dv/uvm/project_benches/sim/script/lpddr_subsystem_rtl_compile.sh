#!/usr/bin/bash
# This script was generated automatically by bender.



# Abort early on errors of the sub-commands!
set -e

SIM_DIR=`pwd`
RTL_DIR="$SIM_DIR/../rtl"
BENDER_SCRIPT_ROOT="$RTL_DIR/impl/europa/blocks/lpddr/rtl"


vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/pkg/axe_tcl_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/simulation/axe_tcl_seq_metastability_model.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.10/FE-Common/MODEL/ln05lpe_sc_s6t_flk_lvt_c54l08/ln05lpe_sc_s6t_flk_lvt_c54l08.v" \
  "$RTL_DIR/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10/FE-Common/MODEL/ln05lpe_sc_s6t_flk_rvt_c54l08/ln05lpe_sc_s6t_flk_rvt_c54l08.v" \
  "$RTL_DIR/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_cdk_lvt_c54_a00_V1.30/FE-Common/MODEL/ln05lpe_sc_s6t_cdk_lvt_c54l08/ln05lpe_sc_s6t_cdk_lvt_c54l08.v" \
  "$RTL_DIR/samsung/sf5a/ip/samsung/ln05lpe_gpio_lib_1p8v_auto_V2.16/FE-Common/MODEL/ln05lpe_gpio_lib_t18.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_sram_pkg.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_pad_pkg.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/functional/axe_tcl_sram_cfg.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/functional/axe_tcl_sram_arb_cfg.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_clk.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_pad.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_seq.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_ram_1rp_1wp.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_ram_1rwp.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_rom_1p.sv" \
  "$RTL_DIR/ip/tech_cell_library/default/rtl/sf5a/axe_tcl_std.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/common_cell_library/default/rtl/pkg/cc_cnt_lfsr_pkg.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/pkg/cc_lib_pkg.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/pkg/cc_math_pkg.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/pkg/cc_utils_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/axi/default/rtl/pkg/axi_pkg.sv" \
  "$RTL_DIR/ip/axi/default/rtl/pkg/axi_xbar_pkg.sv" \
  "$RTL_DIR/ip/axi/default/rtl/pkg/axe_axi_default_types_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/axi/default/rtl/pkg/axi_sim_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_cnt_delta.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_cdc_pulse.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_cdc_sync_array.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_clk_div_by_2.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_clk_or_tree.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_cnt_delta.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_cnt_phase_acc.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_mux_onehot.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_cnt_shift_reg.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_cnt_lfsr.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_decode_addr.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_decode_population.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_dft_block_wrapper.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_dft_pad_mux_core.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_dft_pad_mux_inout.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_dft_pad_mux_input.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_dft_pad_mux_output.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_mon_hysteresis_comparator.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_mon_minimum_maximum.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_rst_n_sync.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_round_robin_arbiter.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_buffer.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_demux.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_filter.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_fork.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_join.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_mux.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_pipe_load.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_reg_el.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_reg_ft.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_reg.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/sync_fifo.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/fifo_v3.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/lzc.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_cdc_bus.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_clk_div_by_pt.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_clk_mux.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_cnt_to_threshold.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_decode_onehot.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_disconnect.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_fifo.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_spill_reg.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/rr_arb_tree.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/cc_stream_xbar.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_stream_fifo_mem.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/axe_ccl_stream_to_mem.sv" \
  "$RTL_DIR/ip/common_cell_library/default/rtl/id_queue.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/pkg/prim_subreg_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/apb/default/rtl/pkg/axe_apb_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/apb/default/rtl/pkg/axe_apb_properties_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_atop_filter.sv" \
  "$RTL_DIR/ip/axi/default/rtl/address_translation_unit/axe_axi_atu_l1_channel.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_cut.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_id_prepend.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_id_remap.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_modify_address.sv" \
  "$RTL_DIR/ip/axi/default/rtl/atomics/axe_axi_riscv_amos_alu.sv" \
  "$RTL_DIR/ip/axi/default/rtl/atomics/axe_axi_riscv_lrsc_res_tbl.sv" \
  "$RTL_DIR/ip/axi/default/rtl/address_translation_unit/axe_axi_atu_l1.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_demux.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_err_sub.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_multicut.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_mux.sv" \
  "$RTL_DIR/ip/axi/default/rtl/atomics/axe_axi_riscv_amos.sv" \
  "$RTL_DIR/ip/axi/default/rtl/atomics/axe_axi_riscv_lrsc.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_atu.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_dw_downsizer.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_dw_upsizer.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_isolate.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_riscv_atomics.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_xbar.sv" \
  "$RTL_DIR/ip/axi/default/rtl/axe_axi_dw_converter.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw01/src_ver" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw04/src_ver/DW_tap.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw04/src_ver/DW_bc_1.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw01/src_ver/DW_minmax.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw01/src_ver/DW01_prienc.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw01/src_ver/DW01_add.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw01/src_ver/DW01_sub.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw02/src_ver/DW_fp_i2flt.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw02/src_ver/DW_fp_flt2i.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw02/src_ver/DW_fp_addsub.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw02/src_ver/DW_fp_add.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw02/src_ver/DW_fp_mult.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw05/src_ver/DW_arb_sp.v" \
  "$RTL_DIR/opt/synopsys/syn/U-2022.12-SP7-1/dw/dw02/src_ver/DW02_mult_2_stage.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/vendor/synopsys/designware/default/rtl/DW_lp_fp_multifunc_intf_only.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/dv/common/properties" \
  "$RTL_DIR/dv/common/properties/axe_properties_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/impl/europa/asic/rtl/pkg/chip_pkg.sv" \
  "$RTL_DIR/impl/europa/asic/rtl/pkg/aipu_addr_map_pkg.sv" \
  "$RTL_DIR/impl/europa/asic/rtl/pkg/aic_addr_map_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/include" \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/prim_subreg_cdc.sv" \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/prim_subreg_ext.sv" \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/prim_max_tree.sv" \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/prim_subreg_arb.sv" \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/prim_subreg_ext_async.sv" \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/prim_subreg.sv" \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/prim_subreg_async.sv" \
  "$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/prim_subreg_shadow.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/pctl/default/rtl/build_reg/pctl_ao_csr_reg_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/vendor/synopsys/lpddr_subsys/default/rtl/pkg/lpddr_subsys_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/DWC_ddrctl.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_mux.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/be/bypass.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dr/derate.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd_wrapper.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd_secded_lane.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd_linkecc_secded.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd_linkecc_decoder.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd_ie_rdata_ctl.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd_ie_rdata_merge.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd_ie_rdata_unmerge.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rd/rd_ie_log_reg.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/dwc_ddrctl_ih_bankhash.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_core_in_if.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_core_out_if.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_address_map.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_address_map_wrapper.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_address_map_pkt.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_be_if.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_te_if.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_fifo_if.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_pw.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_te_pipeline.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_token_fifo.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_ie_cmd_ctl.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_ie_token_fifo.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_ie_blk_chn_item.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_ie_blk_chn_table.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_ie_bt_item.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_ie_bt_table.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_retry_mux.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ie/ie_ecc_ram.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ie/ie_err_ram.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ie/ie_brt_mngr.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ie/ie_bwt_mngr.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_data_steering.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_ram_rd_pipeline.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_secded_lane.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_linkecc_secded.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_linkecc_encoder.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_ie_wdata_ctl.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_ie_wdata_merge.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_wrapper.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_latency_calc.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/mr/mr_data_phase_ctrl.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pi/pi.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/rt/rt.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_nxt_vp_update.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_filter_vp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_filter.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_filter_vp_2lv.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_entry_crit.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_rd_nxt.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_wr_nxt.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_rd_replace.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_wr_replace.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_rd_cam.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_rd_entry.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_rd_mux.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/teengine.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_wr_cam.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_wr_entry.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_wr_mux.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_misc.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_hmatrix.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_oldest_tracker.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/bsm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/bsm_pre_act.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_dqsosc.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_phyupd.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_phymstr.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_ctrlupd.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_zq_calib.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_global_constraints.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_global_fsm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_global_fsm_sr_hw_lp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_dfilp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_q_fsm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_glue.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_init_ddr_fsm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_next_xact.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_rank_constraints.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_rfm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_raa_cnt.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_odt.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_load_mr.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_load_mr_hwffc_seq.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_ref_rdwr_switch.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_wck.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/os_glue.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/ts.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/wu/memc_wu.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/wu/memc_wu_wdata_if.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/fifo/ingot_sync_fifo_flopout_rst.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/fifo/ingot_sync_fifo_flopout_rst_rep.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dfi/wrdata_no_toggle.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dfi/dfi_ctrl.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dfi/dfi_data.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dfi/dfi_ic.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dfi/dfi_ic_cp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dfi/dfi_ic_dp_lpddr.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dfi/dfi_ic_cp_ff.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/dfi/dfi_ic_dp_lpddr_ff.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_reg_div.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_reg_ff.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_regmux_div.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_cpfcpeic.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_cpedfiic.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_cperegic.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_cpperfic.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_cpf.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_cpe.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_dp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/ddrc_assertions.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_tb_hif_mux.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ih/ih_assertions.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pi/pi_assertions.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/te/te_assertions.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/gs_assertions.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ts/ts_assertions.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddrctl_bcm36_nhs.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddr_umctl2_bcmwrp36_nhs_inject_x.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddr_umctl2_wr_en_sync.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddr_umctl2_reg_en.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddrctl_apb_coreif.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddrctl_apb_adrdec.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddrctl_apb_slvif.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddrctl_apb_slvfsm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddrctl_apb_slvtop.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/ocpar/DWC_ddrctl_antivalent_reg.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/reg_mux/dwc_ddrctl_reg_mux.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/select_nets/select_net_hmatrix.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/select_nets/select_net_oh.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/common/DWC_ddrctl_bcm57.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/sbr/DWC_ddr_umctl2_sbr.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_pm_mask.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/arb_top/DWC_ddr_arb_top.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/field_packer10.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/field_packer13.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/field_packer15.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_amem_data_match.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_amem_array.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_smem_array.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_gfifo.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/async_fifo_checker.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/sync_fifo_checker.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_gfifo_split.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_rmw.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_iecc_info.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_dcm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_tm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_rrb.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/common/DWC_ddrctl_vqueue.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_lpfsm.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_ws.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_ws_wrapper.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_rp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_rp_wrapper.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_wp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_wp_wrapper.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_dg.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_disp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_cnvg.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_df.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_ad.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_wdd.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_rdu.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_rd_q.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_qos.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_vpt.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_write.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi_read.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_xpi.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddr_umctl2_retime.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddrctl_bcm21.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddrctl_bcm02.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddrctl_bcm06.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddrctl_bcm50.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddrctl_bcm56.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddrctl_bcm_wrap_mem_array.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddrctl_bcm65.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/xpi/DWC_ddrctl_bcm95_i.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/occap/DWC_ddr_umctl2_par_reg.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/apb/DWC_ddr_umctl2_bitsync.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/select_nets/select_node_lite.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/select_nets/select_net_lite.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_pa.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_pa_arb.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_pa_dual.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_pa_port.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_pa_preproc.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_pa_priocomp.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_pa_roundrobincore.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_hif_cmd.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/pa/DWC_ddr_umctl2_hif_data.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/common/DWC_ddrctl_bcm00_mx.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_cp.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src/top/dwc_ddrctl_ddrc_cp_top.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+DWC_LPDDR5XPHY_PG_PINS \
  +define+DWC_LPDDR5XPHY_TOP_PG_PINS \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/dwc_lpddr5xphy_VDEFINES.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/dwc_lpddr5xphy_ac_wrapperX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/dwc_lpddr5xphy_dbyte_wrapperX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/dwc_lpddr5xphy_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_2cyc_checker.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_adder.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_agu_bank_sel.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_agu.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_alu_ca.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_alu.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_aux_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_aux_regs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bc_regs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bitscan_16b.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bitscan_4b.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bitscan_8b.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bitscan.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bpu_aux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bpu_stack.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bpu.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_bpu_write_queue4.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_byte_unit.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_clock_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_core.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_cpu_glue.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dccm_if.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_debug.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_decode.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_div_pipe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_aux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_bank_match.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_bank_sel.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_clock_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_dccm_aux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_dccm.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_ecc_combined_a.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_ecc_combined_b.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_ecc_store_aligner.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_excpn.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_grad_store_aligner.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_grad.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_ibp_buf.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_idle_mgr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_load_aligner.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_lq_cmd_track.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_lq_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_lq_port.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_lq_rrobin.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_lq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_lqwq_if.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_mask_aligner.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_ppb.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_pre_size_aligner.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_pre_store_aligner.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_result_bus.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_simple_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_skid_buffer.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_staging.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_stall_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_store_aligner.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_wq_conflict.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_wq_err.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_wq_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_wq_port.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_dmp_wq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ecc_cac32_c.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ecc_cac32.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ecc_combined.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ecc_gen_32.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ecc_gen32.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_exec_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_exu.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_fetch_buf_br_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_fetch_buf_data_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_fetch_buf.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_halt_mgr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ibp_ppb.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_iccm_arb.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_iccm_aux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_iccm_queue.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_iccm_rdmodwr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_iccm.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_addr_dec_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_addr_dec.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_brinfo_buf.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_clk_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_data_mux_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_data_mux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_fetch_if_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_fetch_if.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_fetch_if_wp_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_ifq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_iprot.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu_tos_queue.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_ifu.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_logic_unit.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_maskgen.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_mpy_pipe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_predecode.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_reset_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_resync_in.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_rtc.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_shifter.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_status32.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_uop_seq_al.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_uop_seq_da.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ahbl2ibp.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ahbl_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ahbl_ibp2single.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ahbl_ibp_compr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_busb_clk_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_busb_ibp_idle.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_bus_bridge.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_bypbuf.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_cbu_mst.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ccmb_ibp_idle.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ccm_bridge.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_clk_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_dccm_dmiibp_slv.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_dccm_dmi_slv.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_dccm_mst.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_dccm_slv.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibp2ahbl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibp2pack.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibp_compr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibp_cwbind.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibpn2ibpw.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibp_preprc.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibp_split.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibpw2ibpn.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_ibpx2ibpy.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_iccm_dmiibp_slv.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_iccm_dmi_slv.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_iccm_mst.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_iccm_slv.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_l2ifu_mst.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_mst_ahbl_ibp_buffer.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_pack2ibp.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_preprc_ibp2pack.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_preprc_ibp_chnl_idle.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_preprc_pack2ibp.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_reset_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_rrobin.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_single2ahbl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_single2sparse.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_slv_ahbl_idle.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_slv_ibp_buffer.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_biu_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cc_aon_wrap.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cc_aux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cc_clock_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cc_gaux_buffer.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cc_pd1_domain.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cc_reset_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cc_top_aon_regs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cc_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_cdc_sync.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_csa_3_2_64.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_csa_4_2_64.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_fd_ffs_33.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_fd_radix4_counter.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_fd_shift_34.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_alu_ca_1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_aon.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_commit_0.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_commit_1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_cpu.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_dec_regs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_dep_pipe2.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_dispatch_pipe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_dispatch_rules.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_dsync_dmb.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_excpn_pipe_0.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_excpn_pipe_1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_excpn_pipe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_exec1_0.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_exec1_1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_exec2_0.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_exec2_1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_exec3_0.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_exec3_1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_exec_pipe2.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_flag_pipe2.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_ifu_align.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_opd_sel.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_pd1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_pred_pipe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_regfile_4r3w.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_sc_pipe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_stall_ctrl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_writeback.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mrl_zol_pipe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_mult16x16_cs35.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_alb_cpu_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pmu_hs_cluster_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ahb2cfg.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_apb2cfg.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_apbfifo_cell.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_apbfifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_cfg2ahb.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_cfg2tdrmux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_jump_search.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_zcal_calval.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_zcalcont.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_zcaldig.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_zcal.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_csrC_TRR_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_csr_TRR_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_csrRW_RW_TRR_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_csrC_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_csr_decode_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_csrRW_RW_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_csr_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_dx_ttcf_mux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_divide_gen.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_rxclktrack.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_rctmath.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ac_dig.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_prbs_checker.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_hwt_complex.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_jtag_dfttdrs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_lcdlcalseq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_cmdmux6.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_micro.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_mtestmux_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_phymasint.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ppgc_gen.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ppgc_chk.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ppgc.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ppgc_txdata_manipulation.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ppgc_rxdata_manipulation.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ppgc_dbi_calc.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_ppgc_patt_gen.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pgdly.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pie.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_ac.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_sideband.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_caxbar.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_rxcoarsedlyX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_rxcoarsedly4X.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_rxcoarseUIdly.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_rxckdly.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_rpneX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_dx_wrapper.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_rxtg_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_master.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_zcal.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pipe_mod.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pipe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphytub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_staging.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_hwt_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_dfi_debug.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_antivalent.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_piping.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_piping_one2n_onechan.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_piping_one2n_alldb.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_rxreplicactl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_tip.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphypub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_sb_gater.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_regs_APBONLY.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_regs_MASTER.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_regs_DBYTE.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_regs_AC.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_regs_DRTUB.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_regs_INITENG.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_regs_PPGC.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_regs_ZCAL.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_asyncmsflop_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_perfctr_pub.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_roller_4b.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_roller_table.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_dxX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_mrr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_fifo_fifoptrX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_xbar_ln2dq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_dbyte_digX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_dbyte_hwt_iso.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_dtsm.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_datatrain.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_trainingcntr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pptrxclk.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_rxtrack.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_txppt.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_cntinv.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_rxppt.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_xbar_dq2ln.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_dfi2dbtxX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_dfi2dbwckX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_txcoarsedlyX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_txdqcoarsedlyX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_coarsedlyX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_dbrxtgX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_dbrxX.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_roller_1b.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_pub_lp54acsm.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_lp54acsm_pulsex.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/src/pub/dwc_lpddr5xphy_premap_do_not_synthesize.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+DWC_LPDDR5XPHY_PG_PINS \
  +define+DWC_LPDDR5XPHY_TOP_PG_PINS \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/rtl/dwc_lpddr5xphy_cdc_syn_stdlib.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/rtl/dwc_lpddr5xphy_rtl_syn_stdlib.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/rtl/dwc_lpddr5xphy_mtestmux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_regs_HMAC.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_wrdatafifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_cmdfifo7.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_lcdl_dlyselencode.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_pclkdca_calseq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_pclkdca_calval.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_pclkdca_lcdlcalseq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_dlycalval.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_lcdl_wrapper.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_data_fifo_nv_X.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_occ_cntrl.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_dlytest.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_occ_clk_multiplexer.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_occ_ctrl.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_occ_counter.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_dlyscale.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_occ_gf.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_occ_clk_ctrl_chain.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_csr_decode.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_occ_decoder.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_clkor2.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_clkand2.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_csrC.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_csrRW_RW.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_occ_orTree.sv" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_csr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphy_dftclkmux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/acx2_ew/Latest/rtl/dwc_lpddr5xphy_acx1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_regs_HMDBYTE4.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_dqsx1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_dqx1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_rxdatfifo_X.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_cmdfifo6.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_dx_ttcf_demux_dq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_dx_ttcf_demux_dqs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_rsm_fifo_v2.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_dqssamp_fifo.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphy_data_fifo_rx_X.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/rtl/dwc_lpddr5xphy_regs_HMZCAL.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/rtl/dwc_lpddr5xphy_regs_HMMAS.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/rtl/dwc_lpddr5xphy_cmdfifo4X.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/rtl/dwc_lpddr5xphy_ptrinit_scm.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/rtl/dwc_lpddr5xphy_master_pclk_mux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/csx2_ew/Latest/rtl/dwc_lpddr5xphy_csx1.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx5_ew/Latest/rtl/dwc_lpddr5xphy_regs_HMDBYTE.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+DWC_LPDDR5XPHY_PG_PINS \
  +define+DWC_LPDDR5XPHY_TOP_PG_PINS \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/rtl/dwc_lpddr5xphycmosx2_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/rtl/dwc_lpddr5xphyckx2_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/acx2_ew/Latest/rtl/dwc_lpddr5xphyacx2_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/rtl/dwc_lpddr5xphydx4_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/csx2_ew/Latest/rtl/dwc_lpddr5xphycsx2_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx5_ew/Latest/rtl/dwc_lpddr5xphydx5_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/rtl/dwc_lpddr5xphyzcal_top.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/rtl/dwc_lpddr5xphymaster_top.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+DWC_LPDDR5XPHY_PG_PINS \
  +define+DWC_LPDDR5XPHY_TOP_PG_PINS \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_rxacvref_vref_rdac.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_stdcells_HM_models.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_por.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_rxacvref_vref_dec_analog.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_rxacvref.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_txrxcmos.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_mux8.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_mux64.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_decoder3to8.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/cmosx2_ew/Latest/behavior/dwc_lpddr5xphy_vregvsh_vref_mux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_pclk_rxdca.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_lcdl_dlyseldecode_stdprod.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_dcd.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_txfe_dca.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_lcdl_atpg.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_lstx_acx2.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_txrxac.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_rxac.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_lcdl.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_txfe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_lcdl_core.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_txbe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_lcdl_cal_SR.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_rxac_afe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/ckx2_ew/Latest/behavior/dwc_lpddr5xphy_stdlib_comparator.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxreplica_gated_se2diff.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_txrxdqs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_txrxdq.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdqs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_lstx_dx4.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxreplica.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdqs_afe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_dfeout.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_txfedqs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxreplica_phase_detector.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdqs_replica_core.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdqs_core.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdqs_rdgate.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_phase_detect.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_afe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_pclk_rptx2.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_sa_dfe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_gm_bias_lp5.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_dfe_summer.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_offgen.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdqs_cml2cmos.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_vreftop.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_dfebias.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx4_ew/Latest/behavior/dwc_lpddr5xphy_rxdqs_replica_att.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalio.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_lstx_zcal.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_ato.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_cmpr_pasa.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_cmpr.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_cmpr_ibias.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_foldedcascode.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_sampler.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_input_divider.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_dac.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_calmux.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_rxdq_vrefdac.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/zcal_ew/Latest/behavior/dwc_lpddr5xphy_zcalana_rcfilt.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/behavior/dwc_phy_pll_ns.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/behavior/dwc_lpddr5xphy_pclk_master.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/behavior/dwc_lpddr5xphy_techrevision.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/master_ew/Latest/behavior/dwc_lpddr5xphy_ato_pll.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/csx2_ew/Latest/behavior/dwc_lpddr5xphy_txrxcs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/csx2_ew/Latest/behavior/dwc_lpddr5xphy_rxcs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/csx2_ew/Latest/behavior/dwc_lpddr5xphy_txfecs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/csx2_ew/Latest/behavior/dwc_lpddr5xphy_txbecs.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/csx2_ew/Latest/behavior/dwc_lpddr5xphy_rxcs_afe.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/csx2_ew/Latest/behavior/dwc_lpddr5xphy_lstx_csx2.v" \
  "$RTL_DIR/lpddr5x/v_roel/ss3/phy/dx5_ew/Latest/behavior/dwc_lpddr5xphy_lstx_dx5.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/src/snps_ddr_subsystem.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddrphy_mem_wrap/src/DWC_ddrphy_mem_wrap.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddrphy_mem_wrap/src/ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2_wrapper.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddrphy_mem_wrap/src/ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddrphy_mem_wrap/src/ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x8m4b2c1r2_wrapper.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddrphy_mem_wrap/src/ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddrphy_mem_wrap/src/ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x64m2b1c1r2_wrapper.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddrphy_mem_wrap/src/ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2_wrapper.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_uddrctl_mem_wrap/src/DWC_uddrctl_mem_wrap_cc_constants.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_uddrctl_mem_wrap/src/DWC_uddrctl_mem_wrap.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_uddrctl_mem_wrap/src/ln05lpe_a00_mc_rf2rwp_hsr_rvt_128x128m1b4c1r2_wrapper.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddr_ss_clk_blk/src/DWC_ddr_ss_clk_gate.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddr_ss_clk_blk/src/DWC_ddr_ss_clk_mux.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_ddr_ss_clk_blk/src/DWC_ddr_ss_clk_blk.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_apb_decoder/src/DWC_apb_constants.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/i_DWC_apb_decoder/src/DWC_apb_decoder.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/mem/ln05lpe_a00_mc_rf2rwp_hsr_rvt_128x128m1b4c1r2.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/mem/ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/mem/ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/mem/ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x8m4b2c1r2.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/mem/ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/mem/ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x64m2b1c1r2.v" \
  "$RTL_DIR/lpddr5x/ss3/ws_snps_ddr_subsystem/components/mem/ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/ip/apb/default/rtl/axe_apb_cut.sv" \
  "$RTL_DIR/ip/apb/default/rtl/axe_apb_demux.sv" \
  "$RTL_DIR/ip/apb/default/rtl/axe_apb_mux.sv" \
  "$RTL_DIR/ip/apb/default/rtl/axe_apb_manager.sv" \
  "$RTL_DIR/ip/apb/default/rtl/axe_apb_8to32.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/impl/europa/rtl/axe_axi_multicut_flat.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "$RTL_DIR/impl/europa/blocks/lpddr/rtl/pkg/lpddr_pkg.sv" \
  "$RTL_DIR/impl/europa/blocks/lpddr/rtl/pkg/../build_reg/lpddr_csr_reg_pkg.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/include" \
  "$RTL_DIR/ip/pctl/default/rtl/build_reg/pctl_ao_csr_reg_top.sv" \
  "$RTL_DIR/ip/pctl/default/rtl/pctl_ppmu.sv" \
  "$RTL_DIR/ip/pctl/default/rtl/pctl.sv"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+GLOBAL_MIN_HOLD_NS=0 \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/lpddr5x/v_roel/ss3/ctrl/src" \
  "+incdir+$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/include" \
  "+incdir+$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/include" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_lpddr_subsys_wrapper.sv" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c12_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_DWC_uddrctl_mem_wrap.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c12_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c11_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_tdr_sri_ctrl.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_tdr_rx_pad_en.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c2_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c4_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c2_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c12_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_tap_main.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_ssn_scan_host_sh.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c9_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c1_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_bscan_logical_group_DEF.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_edt_cx.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_tdr_rx_data_rcv.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p.sv" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c11_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_edt_cx_tdr.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c13_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_posedge_clock_dff_reset.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c1_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c7_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c6_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_tdr_scan_mode.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_sib_3.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbisr_register_ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x64m2b1c1r2_wrapper.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_occ.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_bap.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_edt_c1_int_tdr.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c7_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c9_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c8_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_scanmux_1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_tdr_phy.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c8_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c7_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbisr_register_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2_wrapper.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c13_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_edt_c1_int.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c4_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c5_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbisr_register_ln05lpe_a00_mc_rf2rwp_hsr_rvt_128x128m1b4c1r2_wrapper.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c9_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c8_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c13_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbisr_register_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2_wrapper.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c10_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c6_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c6_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_tdr_tx_mode.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbisr_register_ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2_wrapper.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_sib_4.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_bscan_cells.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c13_interface_m2.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c10_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_ssn_receiver_1x_pipe_w24_1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_sib_1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c5_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c11_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_bscan_interface.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_sib_1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_DWC_ddrphy_mem_wrap.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbisr_register_ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2_wrapper.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c4_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c3_controller.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_tdr_rx_rcv_en.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_sib_2.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c10_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c3_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbisr_register_ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x8m4b2c1r2_wrapper.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c3_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_sib_2.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c2_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c5_interface_m1.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/snps_ddr_subsystem_rtl1_tessent_mbist_c1_controller_assembly.v" \
  "$RTL_DIR/dft/bronze/lpddr/202411302041/rtl/lpddr_p_rtl2_tessent_tdr_sri_ctrl.v"

vlog -incr -sv \
  -nologo -64 -pedanticerrors -timescale=1ns/1ps -sv12compat -svinputport=compat -mfcu=macro -macro=compat -suppress 2972 +define+SVT_VENDOR_LC=mti   \
  +define+TARGET_ASIC \
  +define+TARGET_DFT \
  +define+TARGET_RTL \
  +define+TARGET_SF5A \
  +define+TARGET_SIMULATION \
  +define+TARGET_VSIM \
  "+incdir+$RTL_DIR/vendor/lowrisc/prim_subreg/default/rtl/include" \
  "$RTL_DIR/impl/europa/blocks/lpddr/rtl/europa_lpddr_async_perf_counter.sv" \
  "$RTL_DIR/impl/europa/blocks/lpddr/rtl/generated/lpddr_subsys_wrapper.sv" \
  "$RTL_DIR/impl/europa/blocks/lpddr/rtl/build_reg/lpddr_csr_reg_top.sv" \
  "$RTL_DIR/impl/europa/blocks/lpddr/rtl/jtag_snps_tdr.v"

