#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# Clearing environment variables
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
echo
echo " --- Removing previously defined Environment variables --- "
echo
unset PCIE_WORKSPACE
unset PCIE_PHY_PATH
unset PCIE_CTRL_X4_PATH

unset SS_DIR
echo " --- Environment Clean-Up Done --- "

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# Environment for PCIe Subsystem
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
echo
echo "---------------------------------------------------------------"
echo " --- Welcome to the Axelera PCIe subsystem workspace --- "
echo "---------------------------------------------------------------"
echo
export VRO_CACHE_DIR=`pwd`
echo " Workspace (PCIE_WORKSPACE) :"
echo "   ${PCIE_WORKSPACE} "

# For release
export PCIE_WORKSPACE=`pwd`/subsystem
export SS_DIR=`pwd`/subsystem
echo " Subsystem path (PCIE_WORKSPACE) :"
echo "   ${PCIE_WORKSPACE} "

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# IP Path Settings
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
export PCIE_PHY_PATH=/data/foundry/LIB/synopsys/pcie4/ip/phy
export PCIE_CTRL_X4_PATH=`pwd`/Axelera_Europa_pcie_gen4_ctrl_6.20a_SS2

echo
echo "PCIE_PHY_PATH : ${PCIE_PHY_PATH}"
echo
echo "PCIE_CTRL_X4_PATH : ${PCIE_CTRL_X4_PATH}"
echo
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# To be updated
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
export PHY_METALSTACK=13M_4Mx_7Dx_2Iz_LB
export PHY_NAME=dwc_c20pcie4_pma_x4_ns_sspg0p675v125c_SigRCmaxDP_ErPlus_GlobalRvia_MOL_nominal_detailed_pg

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# Synthesis & Spyglass
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
export LIB_NAME=ln05lpe_sc_s6t_flk_rvt_c54l08_sspg_nominal_max_0p6750v_125c


export MEM_PATH=/data/foundry/samsung/sf5a/memory/samsung/generated/for_synopsys/20240913_PCIE
export MEMDB1=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_260x128m1b8c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_260x128m1b8c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db 
export MEMDB2=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x104m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x104m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB3=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x144m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x144m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB4=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_356x140m1b8c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_356x140m1b8c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB5=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x88m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x88m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB6=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_264x12m1b8c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_264x12m1b8c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB7=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x116m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x116m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB8=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x160m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x160m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB9=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_512x12m1b8c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_512x12m1b8c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db  
export MEMDB10=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_272x136m1b8c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_272x136m1b8c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB11=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x120m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x120m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB12=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x64m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x64m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB13=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x124m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x124m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db  
export MEMDB14=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_284x132m1b8c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_284x132m1b8c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB15=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x136m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x136m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB16=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x84m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x84m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB17=$MEM_PATH/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x148m1b2c1r2/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x148m1b2c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db 
export MEMDB18=$MEM_PATH/ln05lpe_a00_memory_compiler_ra1_hs_rvt_V2.03/ln05lpe_a00_mc_ra1rp_hsr_rvt_2560x16m4b4c1r2/ln05lpe_a00_mc_ra1rp_hsr_rvt_2560x16m4b4c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB19=$MEM_PATH/ln05lpe_a00_memory_compiler_rf1_hs_rvt_V2.03/ln05lpe_a00_mc_rf1rp_hsr_rvt_264x136m2b1c1r2/ln05lpe_a00_mc_rf1rp_hsr_rvt_264x136m2b1c1r2_sspg_sigcmax_0p6750v_0p6750v_125c_lvf_dth.db
export MEMDB20=$MEM_PATH/ln05lpe_a00_memory_compiler_vrom_hd_lvt_V2.02/ln05lpe_a00_mc_vromp_hd_lvt_20480x16m32b8c1/ln05lpe_a00_mc_vromp_hd_lvt_20480x16m32b8c1_sspg_sigrcmax_0p6750v_125c_lvf_dth.db
export memdb="$MEMDB1,$MEMDB2,$MEMDB3,$MEMDB4,$MEMDB5,$MEMDB6,$MEMDB7,$MEMDB8,$MEMDB9,$MEMDB10,$MEMDB11,$MEMDB12,$MEMDB13,$MEMDB14,$MEMDB15,$MEMDB16,$MEMDB17,$MEMDB18,$MEMDB19,$MEMDB20"

export MEM_RTL_PATH=/data/releases/europa/pcie/202410251446

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# License setting
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
echo
echo "Setting up tools"
export LM_LICENSE_FILE="27030@license-1:27020@htz1-license04:27030@htz1-license3:27020@license-0"
export SNPSLMD_LICENSE_FILE="27030@license-1:27020@htz1-license04:27030@htz1-license3:27020@license-0"

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# DesignWare Home
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
echo
echo "DesignWare Home is set to : ${DESIGNWARE_HOME}"
echo

#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
# Tools
#---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
export vCT=V-2024.03
export vSYN=U-2022.12-SP7-1 #2022.12-SP2 
export vFM=U-2022.12-SP1 #2022.12-SP2
export vVCS=U-2023.03-SP2-1 #2023.03-SP2
export vSPYGLASS=S-2021.09-SP2 #2021.09-SP1
export VIP_VERSION=V-2024.03
echo " VIP VERSION : " ${VIP_VERSION}
export CT_HOME=/opt/synopsys/coretools/V-2024.03
echo " CT_HOME : " ${CT_HOME}
module load lic/synopsys
echo " SYNOPSYS : " ${SYNOPSYS}
export FM_HOME=/opt/synopsys/fm/U-2022.12-SP1
echo " FM_HOME : " ${FM_HOME}
echo " PT_HOME : " ${PT_HOME}
export SPYGLASS_HOME=/opt/synopsys/spyglass/S-2021.09-SP2/SPYGLASS_HOME
echo " Spyglass Home : " ${SPYGLASS_HOME}
echo " Vera Home : " ${VERA_HOME}
echo " VCS Home : " ${VCS_HOME}
echo " VC Static Home : " ${VC_STATIC_HOME}
echo " Verdi Home : " ${VERDI_HOME}
export FC_HOME=/opt/synopsys/syn/U-2022.12-SP7-1
echo " FC Home : " ${FC_HOME}
echo
