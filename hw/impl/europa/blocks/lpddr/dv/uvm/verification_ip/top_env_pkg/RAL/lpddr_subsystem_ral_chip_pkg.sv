`ifndef RAL_DDR_CHIP_PKG
`define RAL_DDR_CHIP_PKG

`include "uvm_macros.svh"
`include "ral_DWC_ddrctl_axi_0_AXI_Port0_block_pkg.sv"
`include "ral_DWC_DDRPHYA_AC0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_AC0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_AC0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_AC0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_AC1_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_AC1_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_AC1_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_AC1_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_APBONLY0_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE1_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE1_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE1_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE1_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE2_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE2_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE2_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE2_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE3_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE3_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE3_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_DBYTE3_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_DRTUB0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC1_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC1_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC1_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC1_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC2_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC2_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC2_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC2_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC3_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC3_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC3_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC3_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC4_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC4_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC4_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC4_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC5_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC5_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC5_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC5_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC7_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC7_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC7_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC7_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC8_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC8_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC8_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC8_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC9_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC9_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC9_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC9_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC10_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC10_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC10_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC10_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC11_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC11_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC11_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC11_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC12_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC12_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC12_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMAC12_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_1_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_1_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_1_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_1_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_3_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_3_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_3_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_3_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_5_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_5_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_5_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_5_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_7_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_7_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_7_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE_7_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_2_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_2_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_2_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_2_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_4_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_4_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_4_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_4_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_6_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_6_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_6_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMDBYTE4_6_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMMAS0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMMAS0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMMAS0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMMAS0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_HMZCAL0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_HMZCAL0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_HMZCAL0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_HMZCAL0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_INITENG0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_INITENG0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_INITENG0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_INITENG0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_MASTER0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_MASTER0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_MASTER0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_MASTER0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_PPGC0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_PPGC0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_PPGC0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_PPGC0_p3_pkg.sv"
`include "ral_DWC_DDRPHYA_ZCAL0_p0_pkg.sv"
`include "ral_DWC_DDRPHYA_ZCAL0_p1_pkg.sv"
`include "ral_DWC_DDRPHYA_ZCAL0_p2_pkg.sv"
`include "ral_DWC_DDRPHYA_ZCAL0_p3_pkg.sv"
`include "ral_ICCM_pkg.sv"
`include "ral_DCCM_pkg.sv"
`include "ral_PIE_pkg.sv"
`include "ral_ACSM_pkg.sv"
`include "ral_DWC_ddrctl_map_REGB_DDRC_CH0_pkg.sv"
`include "ral_DWC_ddrctl_map_REGB_ADDR_MAP0_pkg.sv"
`include "ral_DWC_ddrctl_map_REGB_ARB_PORT0_pkg.sv"
`include "ral_DWC_ddrctl_map_REGB_FREQ0_CH0_pkg.sv"
`include "ral_DWC_ddrctl_map_REGB_FREQ1_CH0_pkg.sv"
`include "ral_DWC_ddrctl_map_REGB_FREQ2_CH0_pkg.sv"
`include "ral_DWC_ddrctl_map_REGB_FREQ3_CH0_pkg.sv"
package lpddr_subsystem_ral_chip_pkg;
import uvm_pkg::*;

import ral_DWC_ddrctl_axi_0_AXI_Port0_block_pkg::*;
import ral_DWC_DDRPHYA_AC0_p0_pkg::*;
import ral_DWC_DDRPHYA_AC0_p1_pkg::*;
import ral_DWC_DDRPHYA_AC0_p2_pkg::*;
import ral_DWC_DDRPHYA_AC0_p3_pkg::*;
import ral_DWC_DDRPHYA_AC1_p0_pkg::*;
import ral_DWC_DDRPHYA_AC1_p1_pkg::*;
import ral_DWC_DDRPHYA_AC1_p2_pkg::*;
import ral_DWC_DDRPHYA_AC1_p3_pkg::*;
import ral_DWC_DDRPHYA_APBONLY0_pkg::*;
import ral_DWC_DDRPHYA_DBYTE0_p0_pkg::*;
import ral_DWC_DDRPHYA_DBYTE0_p1_pkg::*;
import ral_DWC_DDRPHYA_DBYTE0_p2_pkg::*;
import ral_DWC_DDRPHYA_DBYTE0_p3_pkg::*;
import ral_DWC_DDRPHYA_DBYTE1_p0_pkg::*;
import ral_DWC_DDRPHYA_DBYTE1_p1_pkg::*;
import ral_DWC_DDRPHYA_DBYTE1_p2_pkg::*;
import ral_DWC_DDRPHYA_DBYTE1_p3_pkg::*;
import ral_DWC_DDRPHYA_DBYTE2_p0_pkg::*;
import ral_DWC_DDRPHYA_DBYTE2_p1_pkg::*;
import ral_DWC_DDRPHYA_DBYTE2_p2_pkg::*;
import ral_DWC_DDRPHYA_DBYTE2_p3_pkg::*;
import ral_DWC_DDRPHYA_DBYTE3_p0_pkg::*;
import ral_DWC_DDRPHYA_DBYTE3_p1_pkg::*;
import ral_DWC_DDRPHYA_DBYTE3_p2_pkg::*;
import ral_DWC_DDRPHYA_DBYTE3_p3_pkg::*;
import ral_DWC_DDRPHYA_DRTUB0_pkg::*;
import ral_DWC_DDRPHYA_HMAC0_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC0_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC0_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC0_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC1_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC1_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC1_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC1_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC2_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC2_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC2_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC2_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC3_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC3_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC3_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC3_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC4_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC4_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC4_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC4_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC5_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC5_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC5_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC5_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC7_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC7_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC7_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC7_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC8_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC8_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC8_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC8_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC9_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC9_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC9_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC9_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC10_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC10_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC10_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC10_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC11_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC11_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC11_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC11_p3_pkg::*;
import ral_DWC_DDRPHYA_HMAC12_p0_pkg::*;
import ral_DWC_DDRPHYA_HMAC12_p1_pkg::*;
import ral_DWC_DDRPHYA_HMAC12_p2_pkg::*;
import ral_DWC_DDRPHYA_HMAC12_p3_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_1_p0_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_1_p1_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_1_p2_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_1_p3_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_3_p0_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_3_p1_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_3_p2_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_3_p3_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_5_p0_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_5_p1_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_5_p2_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_5_p3_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_7_p0_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_7_p1_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_7_p2_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE_7_p3_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_0_p0_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_0_p1_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_0_p2_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_0_p3_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_2_p0_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_2_p1_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_2_p2_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_2_p3_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_4_p0_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_4_p1_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_4_p2_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_4_p3_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_6_p0_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_6_p1_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_6_p2_pkg::*;
import ral_DWC_DDRPHYA_HMDBYTE4_6_p3_pkg::*;
import ral_DWC_DDRPHYA_HMMAS0_p0_pkg::*;
import ral_DWC_DDRPHYA_HMMAS0_p1_pkg::*;
import ral_DWC_DDRPHYA_HMMAS0_p2_pkg::*;
import ral_DWC_DDRPHYA_HMMAS0_p3_pkg::*;
import ral_DWC_DDRPHYA_HMZCAL0_p0_pkg::*;
import ral_DWC_DDRPHYA_HMZCAL0_p1_pkg::*;
import ral_DWC_DDRPHYA_HMZCAL0_p2_pkg::*;
import ral_DWC_DDRPHYA_HMZCAL0_p3_pkg::*;
import ral_DWC_DDRPHYA_INITENG0_p0_pkg::*;
import ral_DWC_DDRPHYA_INITENG0_p1_pkg::*;
import ral_DWC_DDRPHYA_INITENG0_p2_pkg::*;
import ral_DWC_DDRPHYA_INITENG0_p3_pkg::*;
import ral_DWC_DDRPHYA_MASTER0_p0_pkg::*;
import ral_DWC_DDRPHYA_MASTER0_p1_pkg::*;
import ral_DWC_DDRPHYA_MASTER0_p2_pkg::*;
import ral_DWC_DDRPHYA_MASTER0_p3_pkg::*;
import ral_DWC_DDRPHYA_PPGC0_p0_pkg::*;
import ral_DWC_DDRPHYA_PPGC0_p1_pkg::*;
import ral_DWC_DDRPHYA_PPGC0_p2_pkg::*;
import ral_DWC_DDRPHYA_PPGC0_p3_pkg::*;
import ral_DWC_DDRPHYA_ZCAL0_p0_pkg::*;
import ral_DWC_DDRPHYA_ZCAL0_p1_pkg::*;
import ral_DWC_DDRPHYA_ZCAL0_p2_pkg::*;
import ral_DWC_DDRPHYA_ZCAL0_p3_pkg::*;
import ral_ICCM_pkg::*;
import ral_DCCM_pkg::*;
import ral_PIE_pkg::*;
import ral_ACSM_pkg::*;
import ral_DWC_ddrctl_map_REGB_DDRC_CH0_pkg::*;
import ral_DWC_ddrctl_map_REGB_ADDR_MAP0_pkg::*;
import ral_DWC_ddrctl_map_REGB_ARB_PORT0_pkg::*;
import ral_DWC_ddrctl_map_REGB_FREQ0_CH0_pkg::*;
import ral_DWC_ddrctl_map_REGB_FREQ1_CH0_pkg::*;
import ral_DWC_ddrctl_map_REGB_FREQ2_CH0_pkg::*;
import ral_DWC_ddrctl_map_REGB_FREQ3_CH0_pkg::*;
class lpddr_subsystem_apb_reg_block extends uvm_reg_block;

   rand ral_block_DWC_ddrctl_axi_0_AXI_Port0_block DWC_ddrctl_axi_0_AXI_Port0_block;
   rand ral_block_DWC_DDRPHYA_AC0_p0 DWC_DDRPHYA_AC0_p0;
   rand ral_block_DWC_DDRPHYA_AC0_p1 DWC_DDRPHYA_AC0_p1;
   rand ral_block_DWC_DDRPHYA_AC0_p2 DWC_DDRPHYA_AC0_p2;
   rand ral_block_DWC_DDRPHYA_AC0_p3 DWC_DDRPHYA_AC0_p3;
   rand ral_block_DWC_DDRPHYA_AC1_p0 DWC_DDRPHYA_AC1_p0;
   rand ral_block_DWC_DDRPHYA_AC1_p1 DWC_DDRPHYA_AC1_p1;
   rand ral_block_DWC_DDRPHYA_AC1_p2 DWC_DDRPHYA_AC1_p2;
   rand ral_block_DWC_DDRPHYA_AC1_p3 DWC_DDRPHYA_AC1_p3;
   rand ral_block_DWC_DDRPHYA_APBONLY0 DWC_DDRPHYA_APBONLY0;
   rand ral_block_DWC_DDRPHYA_DBYTE0_p0 DWC_DDRPHYA_DBYTE0_p0;
   rand ral_block_DWC_DDRPHYA_DBYTE0_p1 DWC_DDRPHYA_DBYTE0_p1;
   rand ral_block_DWC_DDRPHYA_DBYTE0_p2 DWC_DDRPHYA_DBYTE0_p2;
   rand ral_block_DWC_DDRPHYA_DBYTE0_p3 DWC_DDRPHYA_DBYTE0_p3;
   rand ral_block_DWC_DDRPHYA_DBYTE1_p0 DWC_DDRPHYA_DBYTE1_p0;
   rand ral_block_DWC_DDRPHYA_DBYTE1_p1 DWC_DDRPHYA_DBYTE1_p1;
   rand ral_block_DWC_DDRPHYA_DBYTE1_p2 DWC_DDRPHYA_DBYTE1_p2;
   rand ral_block_DWC_DDRPHYA_DBYTE1_p3 DWC_DDRPHYA_DBYTE1_p3;
   rand ral_block_DWC_DDRPHYA_DBYTE2_p0 DWC_DDRPHYA_DBYTE2_p0;
   rand ral_block_DWC_DDRPHYA_DBYTE2_p1 DWC_DDRPHYA_DBYTE2_p1;
   rand ral_block_DWC_DDRPHYA_DBYTE2_p2 DWC_DDRPHYA_DBYTE2_p2;
   rand ral_block_DWC_DDRPHYA_DBYTE2_p3 DWC_DDRPHYA_DBYTE2_p3;
   rand ral_block_DWC_DDRPHYA_DBYTE3_p0 DWC_DDRPHYA_DBYTE3_p0;
   rand ral_block_DWC_DDRPHYA_DBYTE3_p1 DWC_DDRPHYA_DBYTE3_p1;
   rand ral_block_DWC_DDRPHYA_DBYTE3_p2 DWC_DDRPHYA_DBYTE3_p2;
   rand ral_block_DWC_DDRPHYA_DBYTE3_p3 DWC_DDRPHYA_DBYTE3_p3;
   rand ral_block_DWC_DDRPHYA_DRTUB0 DWC_DDRPHYA_DRTUB0;
   rand ral_block_DWC_DDRPHYA_HMAC0_p0 DWC_DDRPHYA_HMAC0_p0;
   rand ral_block_DWC_DDRPHYA_HMAC0_p1 DWC_DDRPHYA_HMAC0_p1;
   rand ral_block_DWC_DDRPHYA_HMAC0_p2 DWC_DDRPHYA_HMAC0_p2;
   rand ral_block_DWC_DDRPHYA_HMAC0_p3 DWC_DDRPHYA_HMAC0_p3;
   rand ral_block_DWC_DDRPHYA_HMAC1_p0 DWC_DDRPHYA_HMAC1_p0;
   rand ral_block_DWC_DDRPHYA_HMAC1_p1 DWC_DDRPHYA_HMAC1_p1;
   rand ral_block_DWC_DDRPHYA_HMAC1_p2 DWC_DDRPHYA_HMAC1_p2;
   rand ral_block_DWC_DDRPHYA_HMAC1_p3 DWC_DDRPHYA_HMAC1_p3;
   rand ral_block_DWC_DDRPHYA_HMAC2_p0 DWC_DDRPHYA_HMAC2_p0;
   rand ral_block_DWC_DDRPHYA_HMAC2_p1 DWC_DDRPHYA_HMAC2_p1;
   rand ral_block_DWC_DDRPHYA_HMAC2_p2 DWC_DDRPHYA_HMAC2_p2;
   rand ral_block_DWC_DDRPHYA_HMAC2_p3 DWC_DDRPHYA_HMAC2_p3;
   rand ral_block_DWC_DDRPHYA_HMAC3_p0 DWC_DDRPHYA_HMAC3_p0;
   rand ral_block_DWC_DDRPHYA_HMAC3_p1 DWC_DDRPHYA_HMAC3_p1;
   rand ral_block_DWC_DDRPHYA_HMAC3_p2 DWC_DDRPHYA_HMAC3_p2;
   rand ral_block_DWC_DDRPHYA_HMAC3_p3 DWC_DDRPHYA_HMAC3_p3;
   rand ral_block_DWC_DDRPHYA_HMAC4_p0 DWC_DDRPHYA_HMAC4_p0;
   rand ral_block_DWC_DDRPHYA_HMAC4_p1 DWC_DDRPHYA_HMAC4_p1;
   rand ral_block_DWC_DDRPHYA_HMAC4_p2 DWC_DDRPHYA_HMAC4_p2;
   rand ral_block_DWC_DDRPHYA_HMAC4_p3 DWC_DDRPHYA_HMAC4_p3;
   rand ral_block_DWC_DDRPHYA_HMAC5_p0 DWC_DDRPHYA_HMAC5_p0;
   rand ral_block_DWC_DDRPHYA_HMAC5_p1 DWC_DDRPHYA_HMAC5_p1;
   rand ral_block_DWC_DDRPHYA_HMAC5_p2 DWC_DDRPHYA_HMAC5_p2;
   rand ral_block_DWC_DDRPHYA_HMAC5_p3 DWC_DDRPHYA_HMAC5_p3;
   rand ral_block_DWC_DDRPHYA_HMAC7_p0 DWC_DDRPHYA_HMAC7_p0;
   rand ral_block_DWC_DDRPHYA_HMAC7_p1 DWC_DDRPHYA_HMAC7_p1;
   rand ral_block_DWC_DDRPHYA_HMAC7_p2 DWC_DDRPHYA_HMAC7_p2;
   rand ral_block_DWC_DDRPHYA_HMAC7_p3 DWC_DDRPHYA_HMAC7_p3;
   rand ral_block_DWC_DDRPHYA_HMAC8_p0 DWC_DDRPHYA_HMAC8_p0;
   rand ral_block_DWC_DDRPHYA_HMAC8_p1 DWC_DDRPHYA_HMAC8_p1;
   rand ral_block_DWC_DDRPHYA_HMAC8_p2 DWC_DDRPHYA_HMAC8_p2;
   rand ral_block_DWC_DDRPHYA_HMAC8_p3 DWC_DDRPHYA_HMAC8_p3;
   rand ral_block_DWC_DDRPHYA_HMAC9_p0 DWC_DDRPHYA_HMAC9_p0;
   rand ral_block_DWC_DDRPHYA_HMAC9_p1 DWC_DDRPHYA_HMAC9_p1;
   rand ral_block_DWC_DDRPHYA_HMAC9_p2 DWC_DDRPHYA_HMAC9_p2;
   rand ral_block_DWC_DDRPHYA_HMAC9_p3 DWC_DDRPHYA_HMAC9_p3;
   rand ral_block_DWC_DDRPHYA_HMAC10_p0 DWC_DDRPHYA_HMAC10_p0;
   rand ral_block_DWC_DDRPHYA_HMAC10_p1 DWC_DDRPHYA_HMAC10_p1;
   rand ral_block_DWC_DDRPHYA_HMAC10_p2 DWC_DDRPHYA_HMAC10_p2;
   rand ral_block_DWC_DDRPHYA_HMAC10_p3 DWC_DDRPHYA_HMAC10_p3;
   rand ral_block_DWC_DDRPHYA_HMAC11_p0 DWC_DDRPHYA_HMAC11_p0;
   rand ral_block_DWC_DDRPHYA_HMAC11_p1 DWC_DDRPHYA_HMAC11_p1;
   rand ral_block_DWC_DDRPHYA_HMAC11_p2 DWC_DDRPHYA_HMAC11_p2;
   rand ral_block_DWC_DDRPHYA_HMAC11_p3 DWC_DDRPHYA_HMAC11_p3;
   rand ral_block_DWC_DDRPHYA_HMAC12_p0 DWC_DDRPHYA_HMAC12_p0;
   rand ral_block_DWC_DDRPHYA_HMAC12_p1 DWC_DDRPHYA_HMAC12_p1;
   rand ral_block_DWC_DDRPHYA_HMAC12_p2 DWC_DDRPHYA_HMAC12_p2;
   rand ral_block_DWC_DDRPHYA_HMAC12_p3 DWC_DDRPHYA_HMAC12_p3;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_1_p0 DWC_DDRPHYA_HMDBYTE_1_p0;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_1_p1 DWC_DDRPHYA_HMDBYTE_1_p1;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_1_p2 DWC_DDRPHYA_HMDBYTE_1_p2;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_1_p3 DWC_DDRPHYA_HMDBYTE_1_p3;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_3_p0 DWC_DDRPHYA_HMDBYTE_3_p0;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_3_p1 DWC_DDRPHYA_HMDBYTE_3_p1;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_3_p2 DWC_DDRPHYA_HMDBYTE_3_p2;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_3_p3 DWC_DDRPHYA_HMDBYTE_3_p3;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_5_p0 DWC_DDRPHYA_HMDBYTE_5_p0;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_5_p1 DWC_DDRPHYA_HMDBYTE_5_p1;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_5_p2 DWC_DDRPHYA_HMDBYTE_5_p2;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_5_p3 DWC_DDRPHYA_HMDBYTE_5_p3;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_7_p0 DWC_DDRPHYA_HMDBYTE_7_p0;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_7_p1 DWC_DDRPHYA_HMDBYTE_7_p1;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_7_p2 DWC_DDRPHYA_HMDBYTE_7_p2;
   rand ral_block_DWC_DDRPHYA_HMDBYTE_7_p3 DWC_DDRPHYA_HMDBYTE_7_p3;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_0_p0 DWC_DDRPHYA_HMDBYTE4_0_p0;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_0_p1 DWC_DDRPHYA_HMDBYTE4_0_p1;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_0_p2 DWC_DDRPHYA_HMDBYTE4_0_p2;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_0_p3 DWC_DDRPHYA_HMDBYTE4_0_p3;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_2_p0 DWC_DDRPHYA_HMDBYTE4_2_p0;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_2_p1 DWC_DDRPHYA_HMDBYTE4_2_p1;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_2_p2 DWC_DDRPHYA_HMDBYTE4_2_p2;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_2_p3 DWC_DDRPHYA_HMDBYTE4_2_p3;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_4_p0 DWC_DDRPHYA_HMDBYTE4_4_p0;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_4_p1 DWC_DDRPHYA_HMDBYTE4_4_p1;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_4_p2 DWC_DDRPHYA_HMDBYTE4_4_p2;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_4_p3 DWC_DDRPHYA_HMDBYTE4_4_p3;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_6_p0 DWC_DDRPHYA_HMDBYTE4_6_p0;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_6_p1 DWC_DDRPHYA_HMDBYTE4_6_p1;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_6_p2 DWC_DDRPHYA_HMDBYTE4_6_p2;
   rand ral_block_DWC_DDRPHYA_HMDBYTE4_6_p3 DWC_DDRPHYA_HMDBYTE4_6_p3;
   rand ral_block_DWC_DDRPHYA_HMMAS0_p0 DWC_DDRPHYA_HMMAS0_p0;
   rand ral_block_DWC_DDRPHYA_HMMAS0_p1 DWC_DDRPHYA_HMMAS0_p1;
   rand ral_block_DWC_DDRPHYA_HMMAS0_p2 DWC_DDRPHYA_HMMAS0_p2;
   rand ral_block_DWC_DDRPHYA_HMMAS0_p3 DWC_DDRPHYA_HMMAS0_p3;
   rand ral_block_DWC_DDRPHYA_HMZCAL0_p0 DWC_DDRPHYA_HMZCAL0_p0;
   rand ral_block_DWC_DDRPHYA_HMZCAL0_p1 DWC_DDRPHYA_HMZCAL0_p1;
   rand ral_block_DWC_DDRPHYA_HMZCAL0_p2 DWC_DDRPHYA_HMZCAL0_p2;
   rand ral_block_DWC_DDRPHYA_HMZCAL0_p3 DWC_DDRPHYA_HMZCAL0_p3;
   rand ral_block_DWC_DDRPHYA_INITENG0_p0 DWC_DDRPHYA_INITENG0_p0;
   rand ral_block_DWC_DDRPHYA_INITENG0_p1 DWC_DDRPHYA_INITENG0_p1;
   rand ral_block_DWC_DDRPHYA_INITENG0_p2 DWC_DDRPHYA_INITENG0_p2;
   rand ral_block_DWC_DDRPHYA_INITENG0_p3 DWC_DDRPHYA_INITENG0_p3;
   rand ral_block_DWC_DDRPHYA_MASTER0_p0 DWC_DDRPHYA_MASTER0_p0;
   rand ral_block_DWC_DDRPHYA_MASTER0_p1 DWC_DDRPHYA_MASTER0_p1;
   rand ral_block_DWC_DDRPHYA_MASTER0_p2 DWC_DDRPHYA_MASTER0_p2;
   rand ral_block_DWC_DDRPHYA_MASTER0_p3 DWC_DDRPHYA_MASTER0_p3;
   rand ral_block_DWC_DDRPHYA_PPGC0_p0 DWC_DDRPHYA_PPGC0_p0;
   rand ral_block_DWC_DDRPHYA_PPGC0_p1 DWC_DDRPHYA_PPGC0_p1;
   rand ral_block_DWC_DDRPHYA_PPGC0_p2 DWC_DDRPHYA_PPGC0_p2;
   rand ral_block_DWC_DDRPHYA_PPGC0_p3 DWC_DDRPHYA_PPGC0_p3;
   rand ral_block_DWC_DDRPHYA_ZCAL0_p0 DWC_DDRPHYA_ZCAL0_p0;
   rand ral_block_DWC_DDRPHYA_ZCAL0_p1 DWC_DDRPHYA_ZCAL0_p1;
   rand ral_block_DWC_DDRPHYA_ZCAL0_p2 DWC_DDRPHYA_ZCAL0_p2;
   rand ral_block_DWC_DDRPHYA_ZCAL0_p3 DWC_DDRPHYA_ZCAL0_p3;
   rand ral_block_ICCM ICCM;
   rand ral_block_DCCM DCCM;
   rand ral_block_PIE PIE;
   rand ral_block_ACSM ACSM;
   rand ral_block_DWC_ddrctl_map_REGB_DDRC_CH0 DWC_ddrctl_map_REGB_DDRC_CH0;
   rand ral_block_DWC_ddrctl_map_REGB_ADDR_MAP0 DWC_ddrctl_map_REGB_ADDR_MAP0;
   rand ral_block_DWC_ddrctl_map_REGB_ARB_PORT0 DWC_ddrctl_map_REGB_ARB_PORT0;
   rand ral_block_DWC_ddrctl_map_REGB_FREQ0_CH0 DWC_ddrctl_map_REGB_FREQ0_CH0;
   rand ral_block_DWC_ddrctl_map_REGB_FREQ1_CH0 DWC_ddrctl_map_REGB_FREQ1_CH0;
   rand ral_block_DWC_ddrctl_map_REGB_FREQ2_CH0 DWC_ddrctl_map_REGB_FREQ2_CH0;
   rand ral_block_DWC_ddrctl_map_REGB_FREQ3_CH0 DWC_ddrctl_map_REGB_FREQ3_CH0;

	function new(string name = "ddr_chip");
		super.new(name);
	endfunction: new

	function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.DWC_ddrctl_axi_0_AXI_Port0_block = ral_block_DWC_ddrctl_axi_0_AXI_Port0_block::type_id::create("DWC_ddrctl_axi_0_AXI_Port0_block",,get_full_name());
      this.DWC_ddrctl_axi_0_AXI_Port0_block.configure(this, "i_uddrctl");
      this.DWC_ddrctl_axi_0_AXI_Port0_block.build();
      this.default_map.add_submap(this.DWC_ddrctl_axi_0_AXI_Port0_block.default_map, `UVM_REG_ADDR_WIDTH'h1000000);
      this.DWC_DDRPHYA_AC0_p0 = ral_block_DWC_DDRPHYA_AC0_p0::type_id::create("DWC_DDRPHYA_AC0_p0",,get_full_name());
      this.DWC_DDRPHYA_AC0_p0.configure(this, "");
      this.DWC_DDRPHYA_AC0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_AC0_p0.default_map, `UVM_REG_ADDR_WIDTH'h0030000);
      this.DWC_DDRPHYA_AC0_p1 = ral_block_DWC_DDRPHYA_AC0_p1::type_id::create("DWC_DDRPHYA_AC0_p1",,get_full_name());
      this.DWC_DDRPHYA_AC0_p1.configure(this, "");
      this.DWC_DDRPHYA_AC0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_AC0_p1.default_map, `UVM_REG_ADDR_WIDTH'h0130000);
      this.DWC_DDRPHYA_AC0_p2 = ral_block_DWC_DDRPHYA_AC0_p2::type_id::create("DWC_DDRPHYA_AC0_p2",,get_full_name());
      this.DWC_DDRPHYA_AC0_p2.configure(this, "");
      this.DWC_DDRPHYA_AC0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_AC0_p2.default_map, `UVM_REG_ADDR_WIDTH'h0230000);
      this.DWC_DDRPHYA_AC0_p3 = ral_block_DWC_DDRPHYA_AC0_p3::type_id::create("DWC_DDRPHYA_AC0_p3",,get_full_name());
      this.DWC_DDRPHYA_AC0_p3.configure(this, "");
      this.DWC_DDRPHYA_AC0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_AC0_p3.default_map, `UVM_REG_ADDR_WIDTH'h0330000);
      this.DWC_DDRPHYA_AC1_p0 = ral_block_DWC_DDRPHYA_AC1_p0::type_id::create("DWC_DDRPHYA_AC1_p0",,get_full_name());
      this.DWC_DDRPHYA_AC1_p0.configure(this, "");
      this.DWC_DDRPHYA_AC1_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_AC1_p0.default_map, `UVM_REG_ADDR_WIDTH'h0031000);
      this.DWC_DDRPHYA_AC1_p1 = ral_block_DWC_DDRPHYA_AC1_p1::type_id::create("DWC_DDRPHYA_AC1_p1",,get_full_name());
      this.DWC_DDRPHYA_AC1_p1.configure(this, "");
      this.DWC_DDRPHYA_AC1_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_AC1_p1.default_map, `UVM_REG_ADDR_WIDTH'h0131000);
      this.DWC_DDRPHYA_AC1_p2 = ral_block_DWC_DDRPHYA_AC1_p2::type_id::create("DWC_DDRPHYA_AC1_p2",,get_full_name());
      this.DWC_DDRPHYA_AC1_p2.configure(this, "");
      this.DWC_DDRPHYA_AC1_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_AC1_p2.default_map, `UVM_REG_ADDR_WIDTH'h0231000);
      this.DWC_DDRPHYA_AC1_p3 = ral_block_DWC_DDRPHYA_AC1_p3::type_id::create("DWC_DDRPHYA_AC1_p3",,get_full_name());
      this.DWC_DDRPHYA_AC1_p3.configure(this, "");
      this.DWC_DDRPHYA_AC1_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_AC1_p3.default_map, `UVM_REG_ADDR_WIDTH'h0331000);
      this.DWC_DDRPHYA_APBONLY0 = ral_block_DWC_DDRPHYA_APBONLY0::type_id::create("DWC_DDRPHYA_APBONLY0",,get_full_name());
      this.DWC_DDRPHYA_APBONLY0.configure(this, "");
      this.DWC_DDRPHYA_APBONLY0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_APBONLY0.default_map, `UVM_REG_ADDR_WIDTH'hD0000);//10e-1 = D TODO Query-LS#3
      this.DWC_DDRPHYA_DBYTE0_p0 = ral_block_DWC_DDRPHYA_DBYTE0_p0::type_id::create("DWC_DDRPHYA_DBYTE0_p0",,get_full_name());
      this.DWC_DDRPHYA_DBYTE0_p0.configure(this, "");
      this.DWC_DDRPHYA_DBYTE0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE0_p0.default_map, `UVM_REG_ADDR_WIDTH'h0010000);
      this.DWC_DDRPHYA_DBYTE0_p1 = ral_block_DWC_DDRPHYA_DBYTE0_p1::type_id::create("DWC_DDRPHYA_DBYTE0_p1",,get_full_name());
      this.DWC_DDRPHYA_DBYTE0_p1.configure(this, "");
      this.DWC_DDRPHYA_DBYTE0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE0_p1.default_map, `UVM_REG_ADDR_WIDTH'h0110000);
      this.DWC_DDRPHYA_DBYTE0_p2 = ral_block_DWC_DDRPHYA_DBYTE0_p2::type_id::create("DWC_DDRPHYA_DBYTE0_p2",,get_full_name());
      this.DWC_DDRPHYA_DBYTE0_p2.configure(this, "");
      this.DWC_DDRPHYA_DBYTE0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE0_p2.default_map, `UVM_REG_ADDR_WIDTH'h0210000);
      this.DWC_DDRPHYA_DBYTE0_p3 = ral_block_DWC_DDRPHYA_DBYTE0_p3::type_id::create("DWC_DDRPHYA_DBYTE0_p3",,get_full_name());
      this.DWC_DDRPHYA_DBYTE0_p3.configure(this, "");
      this.DWC_DDRPHYA_DBYTE0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE0_p3.default_map, `UVM_REG_ADDR_WIDTH'h0310000);
      this.DWC_DDRPHYA_DBYTE1_p0 = ral_block_DWC_DDRPHYA_DBYTE1_p0::type_id::create("DWC_DDRPHYA_DBYTE1_p0",,get_full_name());
      this.DWC_DDRPHYA_DBYTE1_p0.configure(this, "");
      this.DWC_DDRPHYA_DBYTE1_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE1_p0.default_map, `UVM_REG_ADDR_WIDTH'h0011000);
      this.DWC_DDRPHYA_DBYTE1_p1 = ral_block_DWC_DDRPHYA_DBYTE1_p1::type_id::create("DWC_DDRPHYA_DBYTE1_p1",,get_full_name());
      this.DWC_DDRPHYA_DBYTE1_p1.configure(this, "");
      this.DWC_DDRPHYA_DBYTE1_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE1_p1.default_map, `UVM_REG_ADDR_WIDTH'h0111000);
      this.DWC_DDRPHYA_DBYTE1_p2 = ral_block_DWC_DDRPHYA_DBYTE1_p2::type_id::create("DWC_DDRPHYA_DBYTE1_p2",,get_full_name());
      this.DWC_DDRPHYA_DBYTE1_p2.configure(this, "");
      this.DWC_DDRPHYA_DBYTE1_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE1_p2.default_map, `UVM_REG_ADDR_WIDTH'h0211000);
      this.DWC_DDRPHYA_DBYTE1_p3 = ral_block_DWC_DDRPHYA_DBYTE1_p3::type_id::create("DWC_DDRPHYA_DBYTE1_p3",,get_full_name());
      this.DWC_DDRPHYA_DBYTE1_p3.configure(this, "");
      this.DWC_DDRPHYA_DBYTE1_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE1_p3.default_map, `UVM_REG_ADDR_WIDTH'h0311000);
      this.DWC_DDRPHYA_DBYTE2_p0 = ral_block_DWC_DDRPHYA_DBYTE2_p0::type_id::create("DWC_DDRPHYA_DBYTE2_p0",,get_full_name());
      this.DWC_DDRPHYA_DBYTE2_p0.configure(this, "");
      this.DWC_DDRPHYA_DBYTE2_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE2_p0.default_map, `UVM_REG_ADDR_WIDTH'h0012000);
      this.DWC_DDRPHYA_DBYTE2_p1 = ral_block_DWC_DDRPHYA_DBYTE2_p1::type_id::create("DWC_DDRPHYA_DBYTE2_p1",,get_full_name());
      this.DWC_DDRPHYA_DBYTE2_p1.configure(this, "");
      this.DWC_DDRPHYA_DBYTE2_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE2_p1.default_map, `UVM_REG_ADDR_WIDTH'h0112000);
      this.DWC_DDRPHYA_DBYTE2_p2 = ral_block_DWC_DDRPHYA_DBYTE2_p2::type_id::create("DWC_DDRPHYA_DBYTE2_p2",,get_full_name());
      this.DWC_DDRPHYA_DBYTE2_p2.configure(this, "");
      this.DWC_DDRPHYA_DBYTE2_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE2_p2.default_map, `UVM_REG_ADDR_WIDTH'h0212000);
      this.DWC_DDRPHYA_DBYTE2_p3 = ral_block_DWC_DDRPHYA_DBYTE2_p3::type_id::create("DWC_DDRPHYA_DBYTE2_p3",,get_full_name());
      this.DWC_DDRPHYA_DBYTE2_p3.configure(this, "");
      this.DWC_DDRPHYA_DBYTE2_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE2_p3.default_map, `UVM_REG_ADDR_WIDTH'h0312000);
      this.DWC_DDRPHYA_DBYTE3_p0 = ral_block_DWC_DDRPHYA_DBYTE3_p0::type_id::create("DWC_DDRPHYA_DBYTE3_p0",,get_full_name());
      this.DWC_DDRPHYA_DBYTE3_p0.configure(this, "");
      this.DWC_DDRPHYA_DBYTE3_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE3_p0.default_map, `UVM_REG_ADDR_WIDTH'h0013000);
      this.DWC_DDRPHYA_DBYTE3_p1 = ral_block_DWC_DDRPHYA_DBYTE3_p1::type_id::create("DWC_DDRPHYA_DBYTE3_p1",,get_full_name());
      this.DWC_DDRPHYA_DBYTE3_p1.configure(this, "");
      this.DWC_DDRPHYA_DBYTE3_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE3_p1.default_map, `UVM_REG_ADDR_WIDTH'h0113000);
      this.DWC_DDRPHYA_DBYTE3_p2 = ral_block_DWC_DDRPHYA_DBYTE3_p2::type_id::create("DWC_DDRPHYA_DBYTE3_p2",,get_full_name());
      this.DWC_DDRPHYA_DBYTE3_p2.configure(this, "");
      this.DWC_DDRPHYA_DBYTE3_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE3_p2.default_map, `UVM_REG_ADDR_WIDTH'h0213000);
      this.DWC_DDRPHYA_DBYTE3_p3 = ral_block_DWC_DDRPHYA_DBYTE3_p3::type_id::create("DWC_DDRPHYA_DBYTE3_p3",,get_full_name());
      this.DWC_DDRPHYA_DBYTE3_p3.configure(this, "");
      this.DWC_DDRPHYA_DBYTE3_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DBYTE3_p3.default_map, `UVM_REG_ADDR_WIDTH'h0313000);
      this.DWC_DDRPHYA_DRTUB0 = ral_block_DWC_DDRPHYA_DRTUB0::type_id::create("DWC_DDRPHYA_DRTUB0",,get_full_name());
      this.DWC_DDRPHYA_DRTUB0.configure(this, "");
      this.DWC_DDRPHYA_DRTUB0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_DRTUB0.default_map, `UVM_REG_ADDR_WIDTH'h00C0000);
      this.DWC_DDRPHYA_HMAC0_p0 = ral_block_DWC_DDRPHYA_HMAC0_p0::type_id::create("DWC_DDRPHYA_HMAC0_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC0_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC0_p0.default_map, `UVM_REG_ADDR_WIDTH'h0000000);
      this.DWC_DDRPHYA_HMAC0_p1 = ral_block_DWC_DDRPHYA_HMAC0_p1::type_id::create("DWC_DDRPHYA_HMAC0_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC0_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC0_p1.default_map, `UVM_REG_ADDR_WIDTH'h0100000);
      this.DWC_DDRPHYA_HMAC0_p2 = ral_block_DWC_DDRPHYA_HMAC0_p2::type_id::create("DWC_DDRPHYA_HMAC0_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC0_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC0_p2.default_map, `UVM_REG_ADDR_WIDTH'h0200000);
      this.DWC_DDRPHYA_HMAC0_p3 = ral_block_DWC_DDRPHYA_HMAC0_p3::type_id::create("DWC_DDRPHYA_HMAC0_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC0_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC0_p3.default_map, `UVM_REG_ADDR_WIDTH'h0300000);
      this.DWC_DDRPHYA_HMAC1_p0 = ral_block_DWC_DDRPHYA_HMAC1_p0::type_id::create("DWC_DDRPHYA_HMAC1_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC1_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC1_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC1_p0.default_map, `UVM_REG_ADDR_WIDTH'h0001000);
      this.DWC_DDRPHYA_HMAC1_p1 = ral_block_DWC_DDRPHYA_HMAC1_p1::type_id::create("DWC_DDRPHYA_HMAC1_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC1_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC1_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC1_p1.default_map, `UVM_REG_ADDR_WIDTH'h0101000);
      this.DWC_DDRPHYA_HMAC1_p2 = ral_block_DWC_DDRPHYA_HMAC1_p2::type_id::create("DWC_DDRPHYA_HMAC1_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC1_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC1_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC1_p2.default_map, `UVM_REG_ADDR_WIDTH'h0201000);
      this.DWC_DDRPHYA_HMAC1_p3 = ral_block_DWC_DDRPHYA_HMAC1_p3::type_id::create("DWC_DDRPHYA_HMAC1_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC1_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC1_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC1_p3.default_map, `UVM_REG_ADDR_WIDTH'h0301000);
      this.DWC_DDRPHYA_HMAC2_p0 = ral_block_DWC_DDRPHYA_HMAC2_p0::type_id::create("DWC_DDRPHYA_HMAC2_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC2_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC2_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC2_p0.default_map, `UVM_REG_ADDR_WIDTH'h0002000);
      this.DWC_DDRPHYA_HMAC2_p1 = ral_block_DWC_DDRPHYA_HMAC2_p1::type_id::create("DWC_DDRPHYA_HMAC2_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC2_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC2_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC2_p1.default_map, `UVM_REG_ADDR_WIDTH'h0102000);
      this.DWC_DDRPHYA_HMAC2_p2 = ral_block_DWC_DDRPHYA_HMAC2_p2::type_id::create("DWC_DDRPHYA_HMAC2_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC2_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC2_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC2_p2.default_map, `UVM_REG_ADDR_WIDTH'h0202000);
      this.DWC_DDRPHYA_HMAC2_p3 = ral_block_DWC_DDRPHYA_HMAC2_p3::type_id::create("DWC_DDRPHYA_HMAC2_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC2_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC2_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC2_p3.default_map, `UVM_REG_ADDR_WIDTH'h0302000);
      this.DWC_DDRPHYA_HMAC3_p0 = ral_block_DWC_DDRPHYA_HMAC3_p0::type_id::create("DWC_DDRPHYA_HMAC3_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC3_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC3_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC3_p0.default_map, `UVM_REG_ADDR_WIDTH'h0003000);
      this.DWC_DDRPHYA_HMAC3_p1 = ral_block_DWC_DDRPHYA_HMAC3_p1::type_id::create("DWC_DDRPHYA_HMAC3_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC3_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC3_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC3_p1.default_map, `UVM_REG_ADDR_WIDTH'h0103000);
      this.DWC_DDRPHYA_HMAC3_p2 = ral_block_DWC_DDRPHYA_HMAC3_p2::type_id::create("DWC_DDRPHYA_HMAC3_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC3_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC3_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC3_p2.default_map, `UVM_REG_ADDR_WIDTH'h0203000);
      this.DWC_DDRPHYA_HMAC3_p3 = ral_block_DWC_DDRPHYA_HMAC3_p3::type_id::create("DWC_DDRPHYA_HMAC3_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC3_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC3_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC3_p3.default_map, `UVM_REG_ADDR_WIDTH'h0303000);
      this.DWC_DDRPHYA_HMAC4_p0 = ral_block_DWC_DDRPHYA_HMAC4_p0::type_id::create("DWC_DDRPHYA_HMAC4_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC4_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC4_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC4_p0.default_map, `UVM_REG_ADDR_WIDTH'h0004000);
      this.DWC_DDRPHYA_HMAC4_p1 = ral_block_DWC_DDRPHYA_HMAC4_p1::type_id::create("DWC_DDRPHYA_HMAC4_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC4_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC4_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC4_p1.default_map, `UVM_REG_ADDR_WIDTH'h0104000);
      this.DWC_DDRPHYA_HMAC4_p2 = ral_block_DWC_DDRPHYA_HMAC4_p2::type_id::create("DWC_DDRPHYA_HMAC4_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC4_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC4_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC4_p2.default_map, `UVM_REG_ADDR_WIDTH'h0204000);
      this.DWC_DDRPHYA_HMAC4_p3 = ral_block_DWC_DDRPHYA_HMAC4_p3::type_id::create("DWC_DDRPHYA_HMAC4_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC4_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC4_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC4_p3.default_map, `UVM_REG_ADDR_WIDTH'h0304000);
      this.DWC_DDRPHYA_HMAC5_p0 = ral_block_DWC_DDRPHYA_HMAC5_p0::type_id::create("DWC_DDRPHYA_HMAC5_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC5_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC5_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC5_p0.default_map, `UVM_REG_ADDR_WIDTH'h0005000);
      this.DWC_DDRPHYA_HMAC5_p1 = ral_block_DWC_DDRPHYA_HMAC5_p1::type_id::create("DWC_DDRPHYA_HMAC5_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC5_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC5_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC5_p1.default_map, `UVM_REG_ADDR_WIDTH'h0105000);
      this.DWC_DDRPHYA_HMAC5_p2 = ral_block_DWC_DDRPHYA_HMAC5_p2::type_id::create("DWC_DDRPHYA_HMAC5_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC5_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC5_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC5_p2.default_map, `UVM_REG_ADDR_WIDTH'h0205000);
      this.DWC_DDRPHYA_HMAC5_p3 = ral_block_DWC_DDRPHYA_HMAC5_p3::type_id::create("DWC_DDRPHYA_HMAC5_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC5_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC5_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC5_p3.default_map, `UVM_REG_ADDR_WIDTH'h0305000);
      this.DWC_DDRPHYA_HMAC7_p0 = ral_block_DWC_DDRPHYA_HMAC7_p0::type_id::create("DWC_DDRPHYA_HMAC7_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC7_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC7_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC7_p0.default_map, `UVM_REG_ADDR_WIDTH'h0007000);
      this.DWC_DDRPHYA_HMAC7_p1 = ral_block_DWC_DDRPHYA_HMAC7_p1::type_id::create("DWC_DDRPHYA_HMAC7_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC7_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC7_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC7_p1.default_map, `UVM_REG_ADDR_WIDTH'h0107000);
      this.DWC_DDRPHYA_HMAC7_p2 = ral_block_DWC_DDRPHYA_HMAC7_p2::type_id::create("DWC_DDRPHYA_HMAC7_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC7_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC7_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC7_p2.default_map, `UVM_REG_ADDR_WIDTH'h0207000);
      this.DWC_DDRPHYA_HMAC7_p3 = ral_block_DWC_DDRPHYA_HMAC7_p3::type_id::create("DWC_DDRPHYA_HMAC7_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC7_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC7_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC7_p3.default_map, `UVM_REG_ADDR_WIDTH'h0307000);
      this.DWC_DDRPHYA_HMAC8_p0 = ral_block_DWC_DDRPHYA_HMAC8_p0::type_id::create("DWC_DDRPHYA_HMAC8_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC8_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC8_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC8_p0.default_map, `UVM_REG_ADDR_WIDTH'h0008000);
      this.DWC_DDRPHYA_HMAC8_p1 = ral_block_DWC_DDRPHYA_HMAC8_p1::type_id::create("DWC_DDRPHYA_HMAC8_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC8_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC8_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC8_p1.default_map, `UVM_REG_ADDR_WIDTH'h0108000);
      this.DWC_DDRPHYA_HMAC8_p2 = ral_block_DWC_DDRPHYA_HMAC8_p2::type_id::create("DWC_DDRPHYA_HMAC8_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC8_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC8_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC8_p2.default_map, `UVM_REG_ADDR_WIDTH'h0208000);
      this.DWC_DDRPHYA_HMAC8_p3 = ral_block_DWC_DDRPHYA_HMAC8_p3::type_id::create("DWC_DDRPHYA_HMAC8_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC8_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC8_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC8_p3.default_map, `UVM_REG_ADDR_WIDTH'h0308000);
      this.DWC_DDRPHYA_HMAC9_p0 = ral_block_DWC_DDRPHYA_HMAC9_p0::type_id::create("DWC_DDRPHYA_HMAC9_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC9_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC9_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC9_p0.default_map, `UVM_REG_ADDR_WIDTH'h0009000);
      this.DWC_DDRPHYA_HMAC9_p1 = ral_block_DWC_DDRPHYA_HMAC9_p1::type_id::create("DWC_DDRPHYA_HMAC9_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC9_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC9_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC9_p1.default_map, `UVM_REG_ADDR_WIDTH'h0109000);
      this.DWC_DDRPHYA_HMAC9_p2 = ral_block_DWC_DDRPHYA_HMAC9_p2::type_id::create("DWC_DDRPHYA_HMAC9_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC9_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC9_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC9_p2.default_map, `UVM_REG_ADDR_WIDTH'h0209000);
      this.DWC_DDRPHYA_HMAC9_p3 = ral_block_DWC_DDRPHYA_HMAC9_p3::type_id::create("DWC_DDRPHYA_HMAC9_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC9_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC9_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC9_p3.default_map, `UVM_REG_ADDR_WIDTH'h0309000);
      this.DWC_DDRPHYA_HMAC10_p0 = ral_block_DWC_DDRPHYA_HMAC10_p0::type_id::create("DWC_DDRPHYA_HMAC10_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC10_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC10_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC10_p0.default_map, `UVM_REG_ADDR_WIDTH'h000A000);
      this.DWC_DDRPHYA_HMAC10_p1 = ral_block_DWC_DDRPHYA_HMAC10_p1::type_id::create("DWC_DDRPHYA_HMAC10_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC10_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC10_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC10_p1.default_map, `UVM_REG_ADDR_WIDTH'h010A000);
      this.DWC_DDRPHYA_HMAC10_p2 = ral_block_DWC_DDRPHYA_HMAC10_p2::type_id::create("DWC_DDRPHYA_HMAC10_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC10_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC10_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC10_p2.default_map, `UVM_REG_ADDR_WIDTH'h020A000);
      this.DWC_DDRPHYA_HMAC10_p3 = ral_block_DWC_DDRPHYA_HMAC10_p3::type_id::create("DWC_DDRPHYA_HMAC10_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC10_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC10_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC10_p3.default_map, `UVM_REG_ADDR_WIDTH'h030A000);
      this.DWC_DDRPHYA_HMAC11_p0 = ral_block_DWC_DDRPHYA_HMAC11_p0::type_id::create("DWC_DDRPHYA_HMAC11_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC11_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC11_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC11_p0.default_map, `UVM_REG_ADDR_WIDTH'h000B000);
      this.DWC_DDRPHYA_HMAC11_p1 = ral_block_DWC_DDRPHYA_HMAC11_p1::type_id::create("DWC_DDRPHYA_HMAC11_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC11_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC11_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC11_p1.default_map, `UVM_REG_ADDR_WIDTH'h010B000);
      this.DWC_DDRPHYA_HMAC11_p2 = ral_block_DWC_DDRPHYA_HMAC11_p2::type_id::create("DWC_DDRPHYA_HMAC11_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC11_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC11_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC11_p2.default_map, `UVM_REG_ADDR_WIDTH'h020B000);
      this.DWC_DDRPHYA_HMAC11_p3 = ral_block_DWC_DDRPHYA_HMAC11_p3::type_id::create("DWC_DDRPHYA_HMAC11_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC11_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC11_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC11_p3.default_map, `UVM_REG_ADDR_WIDTH'h030B000);
      this.DWC_DDRPHYA_HMAC12_p0 = ral_block_DWC_DDRPHYA_HMAC12_p0::type_id::create("DWC_DDRPHYA_HMAC12_p0",,get_full_name());
      this.DWC_DDRPHYA_HMAC12_p0.configure(this, "");
      this.DWC_DDRPHYA_HMAC12_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC12_p0.default_map, `UVM_REG_ADDR_WIDTH'h000C000);
      this.DWC_DDRPHYA_HMAC12_p1 = ral_block_DWC_DDRPHYA_HMAC12_p1::type_id::create("DWC_DDRPHYA_HMAC12_p1",,get_full_name());
      this.DWC_DDRPHYA_HMAC12_p1.configure(this, "");
      this.DWC_DDRPHYA_HMAC12_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC12_p1.default_map, `UVM_REG_ADDR_WIDTH'h010C000);
      this.DWC_DDRPHYA_HMAC12_p2 = ral_block_DWC_DDRPHYA_HMAC12_p2::type_id::create("DWC_DDRPHYA_HMAC12_p2",,get_full_name());
      this.DWC_DDRPHYA_HMAC12_p2.configure(this, "");
      this.DWC_DDRPHYA_HMAC12_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC12_p2.default_map, `UVM_REG_ADDR_WIDTH'h020C000);
      this.DWC_DDRPHYA_HMAC12_p3 = ral_block_DWC_DDRPHYA_HMAC12_p3::type_id::create("DWC_DDRPHYA_HMAC12_p3",,get_full_name());
      this.DWC_DDRPHYA_HMAC12_p3.configure(this, "");
      this.DWC_DDRPHYA_HMAC12_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMAC12_p3.default_map, `UVM_REG_ADDR_WIDTH'h030C000);
      this.DWC_DDRPHYA_HMDBYTE_1_p0 = ral_block_DWC_DDRPHYA_HMDBYTE_1_p0::type_id::create("DWC_DDRPHYA_HMDBYTE_1_p0",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_1_p0.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_1_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_1_p0.default_map, `UVM_REG_ADDR_WIDTH'h00E1000);
      this.DWC_DDRPHYA_HMDBYTE_1_p1 = ral_block_DWC_DDRPHYA_HMDBYTE_1_p1::type_id::create("DWC_DDRPHYA_HMDBYTE_1_p1",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_1_p1.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_1_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_1_p1.default_map, `UVM_REG_ADDR_WIDTH'h01E1000);
      this.DWC_DDRPHYA_HMDBYTE_1_p2 = ral_block_DWC_DDRPHYA_HMDBYTE_1_p2::type_id::create("DWC_DDRPHYA_HMDBYTE_1_p2",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_1_p2.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_1_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_1_p2.default_map, `UVM_REG_ADDR_WIDTH'h02E1000);
      this.DWC_DDRPHYA_HMDBYTE_1_p3 = ral_block_DWC_DDRPHYA_HMDBYTE_1_p3::type_id::create("DWC_DDRPHYA_HMDBYTE_1_p3",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_1_p3.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_1_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_1_p3.default_map, `UVM_REG_ADDR_WIDTH'h03E1000);
      this.DWC_DDRPHYA_HMDBYTE_3_p0 = ral_block_DWC_DDRPHYA_HMDBYTE_3_p0::type_id::create("DWC_DDRPHYA_HMDBYTE_3_p0",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_3_p0.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_3_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_3_p0.default_map, `UVM_REG_ADDR_WIDTH'h00E3000);
      this.DWC_DDRPHYA_HMDBYTE_3_p1 = ral_block_DWC_DDRPHYA_HMDBYTE_3_p1::type_id::create("DWC_DDRPHYA_HMDBYTE_3_p1",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_3_p1.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_3_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_3_p1.default_map, `UVM_REG_ADDR_WIDTH'h01E3000);
      this.DWC_DDRPHYA_HMDBYTE_3_p2 = ral_block_DWC_DDRPHYA_HMDBYTE_3_p2::type_id::create("DWC_DDRPHYA_HMDBYTE_3_p2",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_3_p2.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_3_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_3_p2.default_map, `UVM_REG_ADDR_WIDTH'h02E3000);
      this.DWC_DDRPHYA_HMDBYTE_3_p3 = ral_block_DWC_DDRPHYA_HMDBYTE_3_p3::type_id::create("DWC_DDRPHYA_HMDBYTE_3_p3",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_3_p3.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_3_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_3_p3.default_map, `UVM_REG_ADDR_WIDTH'h03E3000);
      this.DWC_DDRPHYA_HMDBYTE_5_p0 = ral_block_DWC_DDRPHYA_HMDBYTE_5_p0::type_id::create("DWC_DDRPHYA_HMDBYTE_5_p0",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_5_p0.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_5_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_5_p0.default_map, `UVM_REG_ADDR_WIDTH'h00E5000);
      this.DWC_DDRPHYA_HMDBYTE_5_p1 = ral_block_DWC_DDRPHYA_HMDBYTE_5_p1::type_id::create("DWC_DDRPHYA_HMDBYTE_5_p1",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_5_p1.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_5_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_5_p1.default_map, `UVM_REG_ADDR_WIDTH'h01E5000);
      this.DWC_DDRPHYA_HMDBYTE_5_p2 = ral_block_DWC_DDRPHYA_HMDBYTE_5_p2::type_id::create("DWC_DDRPHYA_HMDBYTE_5_p2",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_5_p2.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_5_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_5_p2.default_map, `UVM_REG_ADDR_WIDTH'h02E5000);
      this.DWC_DDRPHYA_HMDBYTE_5_p3 = ral_block_DWC_DDRPHYA_HMDBYTE_5_p3::type_id::create("DWC_DDRPHYA_HMDBYTE_5_p3",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_5_p3.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_5_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_5_p3.default_map, `UVM_REG_ADDR_WIDTH'h03E5000);
      this.DWC_DDRPHYA_HMDBYTE_7_p0 = ral_block_DWC_DDRPHYA_HMDBYTE_7_p0::type_id::create("DWC_DDRPHYA_HMDBYTE_7_p0",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_7_p0.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_7_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_7_p0.default_map, `UVM_REG_ADDR_WIDTH'h00E7000);
      this.DWC_DDRPHYA_HMDBYTE_7_p1 = ral_block_DWC_DDRPHYA_HMDBYTE_7_p1::type_id::create("DWC_DDRPHYA_HMDBYTE_7_p1",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_7_p1.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_7_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_7_p1.default_map, `UVM_REG_ADDR_WIDTH'h01E7000);
      this.DWC_DDRPHYA_HMDBYTE_7_p2 = ral_block_DWC_DDRPHYA_HMDBYTE_7_p2::type_id::create("DWC_DDRPHYA_HMDBYTE_7_p2",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_7_p2.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_7_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_7_p2.default_map, `UVM_REG_ADDR_WIDTH'h02E7000);
      this.DWC_DDRPHYA_HMDBYTE_7_p3 = ral_block_DWC_DDRPHYA_HMDBYTE_7_p3::type_id::create("DWC_DDRPHYA_HMDBYTE_7_p3",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE_7_p3.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE_7_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE_7_p3.default_map, `UVM_REG_ADDR_WIDTH'h03E7000);
      this.DWC_DDRPHYA_HMDBYTE4_0_p0 = ral_block_DWC_DDRPHYA_HMDBYTE4_0_p0::type_id::create("DWC_DDRPHYA_HMDBYTE4_0_p0",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_0_p0.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_0_p0.default_map, `UVM_REG_ADDR_WIDTH'h00E0000);
      this.DWC_DDRPHYA_HMDBYTE4_0_p1 = ral_block_DWC_DDRPHYA_HMDBYTE4_0_p1::type_id::create("DWC_DDRPHYA_HMDBYTE4_0_p1",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_0_p1.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_0_p1.default_map, `UVM_REG_ADDR_WIDTH'h01E0000);
      this.DWC_DDRPHYA_HMDBYTE4_0_p2 = ral_block_DWC_DDRPHYA_HMDBYTE4_0_p2::type_id::create("DWC_DDRPHYA_HMDBYTE4_0_p2",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_0_p2.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_0_p2.default_map, `UVM_REG_ADDR_WIDTH'h02E0000);
      this.DWC_DDRPHYA_HMDBYTE4_0_p3 = ral_block_DWC_DDRPHYA_HMDBYTE4_0_p3::type_id::create("DWC_DDRPHYA_HMDBYTE4_0_p3",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_0_p3.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_0_p3.default_map, `UVM_REG_ADDR_WIDTH'h03E0000);
      this.DWC_DDRPHYA_HMDBYTE4_2_p0 = ral_block_DWC_DDRPHYA_HMDBYTE4_2_p0::type_id::create("DWC_DDRPHYA_HMDBYTE4_2_p0",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_2_p0.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_2_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_2_p0.default_map, `UVM_REG_ADDR_WIDTH'h00E2000);
      this.DWC_DDRPHYA_HMDBYTE4_2_p1 = ral_block_DWC_DDRPHYA_HMDBYTE4_2_p1::type_id::create("DWC_DDRPHYA_HMDBYTE4_2_p1",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_2_p1.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_2_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_2_p1.default_map, `UVM_REG_ADDR_WIDTH'h01E2000);
      this.DWC_DDRPHYA_HMDBYTE4_2_p2 = ral_block_DWC_DDRPHYA_HMDBYTE4_2_p2::type_id::create("DWC_DDRPHYA_HMDBYTE4_2_p2",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_2_p2.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_2_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_2_p2.default_map, `UVM_REG_ADDR_WIDTH'h02E2000);
      this.DWC_DDRPHYA_HMDBYTE4_2_p3 = ral_block_DWC_DDRPHYA_HMDBYTE4_2_p3::type_id::create("DWC_DDRPHYA_HMDBYTE4_2_p3",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_2_p3.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_2_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_2_p3.default_map, `UVM_REG_ADDR_WIDTH'h03E2000);
      this.DWC_DDRPHYA_HMDBYTE4_4_p0 = ral_block_DWC_DDRPHYA_HMDBYTE4_4_p0::type_id::create("DWC_DDRPHYA_HMDBYTE4_4_p0",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_4_p0.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_4_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_4_p0.default_map, `UVM_REG_ADDR_WIDTH'h00E4000);
      this.DWC_DDRPHYA_HMDBYTE4_4_p1 = ral_block_DWC_DDRPHYA_HMDBYTE4_4_p1::type_id::create("DWC_DDRPHYA_HMDBYTE4_4_p1",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_4_p1.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_4_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_4_p1.default_map, `UVM_REG_ADDR_WIDTH'h01E4000);
      this.DWC_DDRPHYA_HMDBYTE4_4_p2 = ral_block_DWC_DDRPHYA_HMDBYTE4_4_p2::type_id::create("DWC_DDRPHYA_HMDBYTE4_4_p2",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_4_p2.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_4_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_4_p2.default_map, `UVM_REG_ADDR_WIDTH'h02E4000);
      this.DWC_DDRPHYA_HMDBYTE4_4_p3 = ral_block_DWC_DDRPHYA_HMDBYTE4_4_p3::type_id::create("DWC_DDRPHYA_HMDBYTE4_4_p3",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_4_p3.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_4_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_4_p3.default_map, `UVM_REG_ADDR_WIDTH'h03E4000);
      this.DWC_DDRPHYA_HMDBYTE4_6_p0 = ral_block_DWC_DDRPHYA_HMDBYTE4_6_p0::type_id::create("DWC_DDRPHYA_HMDBYTE4_6_p0",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_6_p0.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_6_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_6_p0.default_map, `UVM_REG_ADDR_WIDTH'h00E6000);
      this.DWC_DDRPHYA_HMDBYTE4_6_p1 = ral_block_DWC_DDRPHYA_HMDBYTE4_6_p1::type_id::create("DWC_DDRPHYA_HMDBYTE4_6_p1",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_6_p1.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_6_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_6_p1.default_map, `UVM_REG_ADDR_WIDTH'h01E6000);
      this.DWC_DDRPHYA_HMDBYTE4_6_p2 = ral_block_DWC_DDRPHYA_HMDBYTE4_6_p2::type_id::create("DWC_DDRPHYA_HMDBYTE4_6_p2",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_6_p2.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_6_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_6_p2.default_map, `UVM_REG_ADDR_WIDTH'h02E6000);
      this.DWC_DDRPHYA_HMDBYTE4_6_p3 = ral_block_DWC_DDRPHYA_HMDBYTE4_6_p3::type_id::create("DWC_DDRPHYA_HMDBYTE4_6_p3",,get_full_name());
      this.DWC_DDRPHYA_HMDBYTE4_6_p3.configure(this, "");
      this.DWC_DDRPHYA_HMDBYTE4_6_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMDBYTE4_6_p3.default_map, `UVM_REG_ADDR_WIDTH'h03E6000);
      this.DWC_DDRPHYA_HMMAS0_p0 = ral_block_DWC_DDRPHYA_HMMAS0_p0::type_id::create("DWC_DDRPHYA_HMMAS0_p0",,get_full_name());
      this.DWC_DDRPHYA_HMMAS0_p0.configure(this, "");
      this.DWC_DDRPHYA_HMMAS0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMMAS0_p0.default_map, `UVM_REG_ADDR_WIDTH'h0060000);
      this.DWC_DDRPHYA_HMMAS0_p1 = ral_block_DWC_DDRPHYA_HMMAS0_p1::type_id::create("DWC_DDRPHYA_HMMAS0_p1",,get_full_name());
      this.DWC_DDRPHYA_HMMAS0_p1.configure(this, "");
      this.DWC_DDRPHYA_HMMAS0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMMAS0_p1.default_map, `UVM_REG_ADDR_WIDTH'h0160000);
      this.DWC_DDRPHYA_HMMAS0_p2 = ral_block_DWC_DDRPHYA_HMMAS0_p2::type_id::create("DWC_DDRPHYA_HMMAS0_p2",,get_full_name());
      this.DWC_DDRPHYA_HMMAS0_p2.configure(this, "");
      this.DWC_DDRPHYA_HMMAS0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMMAS0_p2.default_map, `UVM_REG_ADDR_WIDTH'h0260000);
      this.DWC_DDRPHYA_HMMAS0_p3 = ral_block_DWC_DDRPHYA_HMMAS0_p3::type_id::create("DWC_DDRPHYA_HMMAS0_p3",,get_full_name());
      this.DWC_DDRPHYA_HMMAS0_p3.configure(this, "");
      this.DWC_DDRPHYA_HMMAS0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMMAS0_p3.default_map, `UVM_REG_ADDR_WIDTH'h0360000);
      this.DWC_DDRPHYA_HMZCAL0_p0 = ral_block_DWC_DDRPHYA_HMZCAL0_p0::type_id::create("DWC_DDRPHYA_HMZCAL0_p0",,get_full_name());
      this.DWC_DDRPHYA_HMZCAL0_p0.configure(this, "");
      this.DWC_DDRPHYA_HMZCAL0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMZCAL0_p0.default_map, `UVM_REG_ADDR_WIDTH'h00A0000);
      this.DWC_DDRPHYA_HMZCAL0_p1 = ral_block_DWC_DDRPHYA_HMZCAL0_p1::type_id::create("DWC_DDRPHYA_HMZCAL0_p1",,get_full_name());
      this.DWC_DDRPHYA_HMZCAL0_p1.configure(this, "");
      this.DWC_DDRPHYA_HMZCAL0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMZCAL0_p1.default_map, `UVM_REG_ADDR_WIDTH'h01A0000);
      this.DWC_DDRPHYA_HMZCAL0_p2 = ral_block_DWC_DDRPHYA_HMZCAL0_p2::type_id::create("DWC_DDRPHYA_HMZCAL0_p2",,get_full_name());
      this.DWC_DDRPHYA_HMZCAL0_p2.configure(this, "");
      this.DWC_DDRPHYA_HMZCAL0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMZCAL0_p2.default_map, `UVM_REG_ADDR_WIDTH'h02A0000);
      this.DWC_DDRPHYA_HMZCAL0_p3 = ral_block_DWC_DDRPHYA_HMZCAL0_p3::type_id::create("DWC_DDRPHYA_HMZCAL0_p3",,get_full_name());
      this.DWC_DDRPHYA_HMZCAL0_p3.configure(this, "");
      this.DWC_DDRPHYA_HMZCAL0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_HMZCAL0_p3.default_map, `UVM_REG_ADDR_WIDTH'h03A0000);
      this.DWC_DDRPHYA_INITENG0_p0 = ral_block_DWC_DDRPHYA_INITENG0_p0::type_id::create("DWC_DDRPHYA_INITENG0_p0",,get_full_name());
      this.DWC_DDRPHYA_INITENG0_p0.configure(this, "");
      this.DWC_DDRPHYA_INITENG0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_INITENG0_p0.default_map, `UVM_REG_ADDR_WIDTH'h0090000);
      this.DWC_DDRPHYA_INITENG0_p1 = ral_block_DWC_DDRPHYA_INITENG0_p1::type_id::create("DWC_DDRPHYA_INITENG0_p1",,get_full_name());
      this.DWC_DDRPHYA_INITENG0_p1.configure(this, "");
      this.DWC_DDRPHYA_INITENG0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_INITENG0_p1.default_map, `UVM_REG_ADDR_WIDTH'h0190000);
      this.DWC_DDRPHYA_INITENG0_p2 = ral_block_DWC_DDRPHYA_INITENG0_p2::type_id::create("DWC_DDRPHYA_INITENG0_p2",,get_full_name());
      this.DWC_DDRPHYA_INITENG0_p2.configure(this, "");
      this.DWC_DDRPHYA_INITENG0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_INITENG0_p2.default_map, `UVM_REG_ADDR_WIDTH'h0290000);
      this.DWC_DDRPHYA_INITENG0_p3 = ral_block_DWC_DDRPHYA_INITENG0_p3::type_id::create("DWC_DDRPHYA_INITENG0_p3",,get_full_name());
      this.DWC_DDRPHYA_INITENG0_p3.configure(this, "");
      this.DWC_DDRPHYA_INITENG0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_INITENG0_p3.default_map, `UVM_REG_ADDR_WIDTH'h0390000);
      this.DWC_DDRPHYA_MASTER0_p0 = ral_block_DWC_DDRPHYA_MASTER0_p0::type_id::create("DWC_DDRPHYA_MASTER0_p0",,get_full_name());
      this.DWC_DDRPHYA_MASTER0_p0.configure(this, "");
      this.DWC_DDRPHYA_MASTER0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_MASTER0_p0.default_map, `UVM_REG_ADDR_WIDTH'h0020000);
      this.DWC_DDRPHYA_MASTER0_p1 = ral_block_DWC_DDRPHYA_MASTER0_p1::type_id::create("DWC_DDRPHYA_MASTER0_p1",,get_full_name());
      this.DWC_DDRPHYA_MASTER0_p1.configure(this, "");
      this.DWC_DDRPHYA_MASTER0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_MASTER0_p1.default_map, `UVM_REG_ADDR_WIDTH'h0120000);
      this.DWC_DDRPHYA_MASTER0_p2 = ral_block_DWC_DDRPHYA_MASTER0_p2::type_id::create("DWC_DDRPHYA_MASTER0_p2",,get_full_name());
      this.DWC_DDRPHYA_MASTER0_p2.configure(this, "");
      this.DWC_DDRPHYA_MASTER0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_MASTER0_p2.default_map, `UVM_REG_ADDR_WIDTH'h0220000);
      this.DWC_DDRPHYA_MASTER0_p3 = ral_block_DWC_DDRPHYA_MASTER0_p3::type_id::create("DWC_DDRPHYA_MASTER0_p3",,get_full_name());
      this.DWC_DDRPHYA_MASTER0_p3.configure(this, "");
      this.DWC_DDRPHYA_MASTER0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_MASTER0_p3.default_map, `UVM_REG_ADDR_WIDTH'h0320000);
      this.DWC_DDRPHYA_PPGC0_p0 = ral_block_DWC_DDRPHYA_PPGC0_p0::type_id::create("DWC_DDRPHYA_PPGC0_p0",,get_full_name());
      this.DWC_DDRPHYA_PPGC0_p0.configure(this, "");
      this.DWC_DDRPHYA_PPGC0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_PPGC0_p0.default_map, `UVM_REG_ADDR_WIDTH'h0070000);
      this.DWC_DDRPHYA_PPGC0_p1 = ral_block_DWC_DDRPHYA_PPGC0_p1::type_id::create("DWC_DDRPHYA_PPGC0_p1",,get_full_name());
      this.DWC_DDRPHYA_PPGC0_p1.configure(this, "");
      this.DWC_DDRPHYA_PPGC0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_PPGC0_p1.default_map, `UVM_REG_ADDR_WIDTH'h0170000);
      this.DWC_DDRPHYA_PPGC0_p2 = ral_block_DWC_DDRPHYA_PPGC0_p2::type_id::create("DWC_DDRPHYA_PPGC0_p2",,get_full_name());
      this.DWC_DDRPHYA_PPGC0_p2.configure(this, "");
      this.DWC_DDRPHYA_PPGC0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_PPGC0_p2.default_map, `UVM_REG_ADDR_WIDTH'h0270000);
      this.DWC_DDRPHYA_PPGC0_p3 = ral_block_DWC_DDRPHYA_PPGC0_p3::type_id::create("DWC_DDRPHYA_PPGC0_p3",,get_full_name());
      this.DWC_DDRPHYA_PPGC0_p3.configure(this, "");
      this.DWC_DDRPHYA_PPGC0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_PPGC0_p3.default_map, `UVM_REG_ADDR_WIDTH'h0370000);
      this.DWC_DDRPHYA_ZCAL0_p0 = ral_block_DWC_DDRPHYA_ZCAL0_p0::type_id::create("DWC_DDRPHYA_ZCAL0_p0",,get_full_name());
      this.DWC_DDRPHYA_ZCAL0_p0.configure(this, "");
      this.DWC_DDRPHYA_ZCAL0_p0.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_ZCAL0_p0.default_map, `UVM_REG_ADDR_WIDTH'h00B0000);
      this.DWC_DDRPHYA_ZCAL0_p1 = ral_block_DWC_DDRPHYA_ZCAL0_p1::type_id::create("DWC_DDRPHYA_ZCAL0_p1",,get_full_name());
      this.DWC_DDRPHYA_ZCAL0_p1.configure(this, "");
      this.DWC_DDRPHYA_ZCAL0_p1.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_ZCAL0_p1.default_map, `UVM_REG_ADDR_WIDTH'h01B0000);
      this.DWC_DDRPHYA_ZCAL0_p2 = ral_block_DWC_DDRPHYA_ZCAL0_p2::type_id::create("DWC_DDRPHYA_ZCAL0_p2",,get_full_name());
      this.DWC_DDRPHYA_ZCAL0_p2.configure(this, "");
      this.DWC_DDRPHYA_ZCAL0_p2.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_ZCAL0_p2.default_map, `UVM_REG_ADDR_WIDTH'h02B0000);
      this.DWC_DDRPHYA_ZCAL0_p3 = ral_block_DWC_DDRPHYA_ZCAL0_p3::type_id::create("DWC_DDRPHYA_ZCAL0_p3",,get_full_name());
      this.DWC_DDRPHYA_ZCAL0_p3.configure(this, "");
      this.DWC_DDRPHYA_ZCAL0_p3.build();
      this.default_map.add_submap(this.DWC_DDRPHYA_ZCAL0_p3.default_map, `UVM_REG_ADDR_WIDTH'h03B0000);
      this.ICCM = ral_block_ICCM::type_id::create("ICCM",,get_full_name());
      this.ICCM.configure(this, "");
      this.ICCM.build();
      this.default_map.add_submap(this.ICCM.default_map, `UVM_REG_ADDR_WIDTH'h0050000);
      this.DCCM = ral_block_DCCM::type_id::create("DCCM",,get_full_name());
      this.DCCM.configure(this, "");
      this.DCCM.build();
      this.default_map.add_submap(this.DCCM.default_map, `UVM_REG_ADDR_WIDTH'h0058000);
      this.PIE = ral_block_PIE::type_id::create("PIE",,get_full_name());
      this.PIE.configure(this, "");
      this.PIE.build();
      this.default_map.add_submap(this.PIE.default_map, `UVM_REG_ADDR_WIDTH'h0044000);
      this.ACSM = ral_block_ACSM::type_id::create("ACSM",,get_full_name());
      this.ACSM.configure(this, "");
      this.ACSM.build();
      this.default_map.add_submap(this.ACSM.default_map, `UVM_REG_ADDR_WIDTH'h0041000);
      this.DWC_ddrctl_map_REGB_DDRC_CH0 = ral_block_DWC_ddrctl_map_REGB_DDRC_CH0::type_id::create("DWC_ddrctl_map_REGB_DDRC_CH0",,get_full_name());
      this.DWC_ddrctl_map_REGB_DDRC_CH0.configure(this, "i_uddrctl");
      this.DWC_ddrctl_map_REGB_DDRC_CH0.build();
      this.default_map.add_submap(this.DWC_ddrctl_map_REGB_DDRC_CH0.default_map, `UVM_REG_ADDR_WIDTH'h2010000);
      this.DWC_ddrctl_map_REGB_ADDR_MAP0 = ral_block_DWC_ddrctl_map_REGB_ADDR_MAP0::type_id::create("DWC_ddrctl_map_REGB_ADDR_MAP0",,get_full_name());
      this.DWC_ddrctl_map_REGB_ADDR_MAP0.configure(this, "i_uddrctl");
      this.DWC_ddrctl_map_REGB_ADDR_MAP0.build();
      this.default_map.add_submap(this.DWC_ddrctl_map_REGB_ADDR_MAP0.default_map, `UVM_REG_ADDR_WIDTH'h2030000);
      this.DWC_ddrctl_map_REGB_ARB_PORT0 = ral_block_DWC_ddrctl_map_REGB_ARB_PORT0::type_id::create("DWC_ddrctl_map_REGB_ARB_PORT0",,get_full_name());
      this.DWC_ddrctl_map_REGB_ARB_PORT0.configure(this, "i_uddrctl");
      this.DWC_ddrctl_map_REGB_ARB_PORT0.build();
      this.default_map.add_submap(this.DWC_ddrctl_map_REGB_ARB_PORT0.default_map, `UVM_REG_ADDR_WIDTH'h2020000);
      this.DWC_ddrctl_map_REGB_FREQ0_CH0 = ral_block_DWC_ddrctl_map_REGB_FREQ0_CH0::type_id::create("DWC_ddrctl_map_REGB_FREQ0_CH0",,get_full_name());
      this.DWC_ddrctl_map_REGB_FREQ0_CH0.configure(this, "i_uddrctl");
      this.DWC_ddrctl_map_REGB_FREQ0_CH0.build();
      this.default_map.add_submap(this.DWC_ddrctl_map_REGB_FREQ0_CH0.default_map, `UVM_REG_ADDR_WIDTH'h2000000);
      this.DWC_ddrctl_map_REGB_FREQ1_CH0 = ral_block_DWC_ddrctl_map_REGB_FREQ1_CH0::type_id::create("DWC_ddrctl_map_REGB_FREQ1_CH0",,get_full_name());
      this.DWC_ddrctl_map_REGB_FREQ1_CH0.configure(this, "i_uddrctl");
      this.DWC_ddrctl_map_REGB_FREQ1_CH0.build();
      this.default_map.add_submap(this.DWC_ddrctl_map_REGB_FREQ1_CH0.default_map, `UVM_REG_ADDR_WIDTH'h2100000);
      this.DWC_ddrctl_map_REGB_FREQ2_CH0 = ral_block_DWC_ddrctl_map_REGB_FREQ2_CH0::type_id::create("DWC_ddrctl_map_REGB_FREQ2_CH0",,get_full_name());
      this.DWC_ddrctl_map_REGB_FREQ2_CH0.configure(this, "i_uddrctl");
      this.DWC_ddrctl_map_REGB_FREQ2_CH0.build();
      this.default_map.add_submap(this.DWC_ddrctl_map_REGB_FREQ2_CH0.default_map, `UVM_REG_ADDR_WIDTH'h2200000);
      this.DWC_ddrctl_map_REGB_FREQ3_CH0 = ral_block_DWC_ddrctl_map_REGB_FREQ3_CH0::type_id::create("DWC_ddrctl_map_REGB_FREQ3_CH0",,get_full_name());
      this.DWC_ddrctl_map_REGB_FREQ3_CH0.configure(this, "i_uddrctl");
      this.DWC_ddrctl_map_REGB_FREQ3_CH0.build();
      this.default_map.add_submap(this.DWC_ddrctl_map_REGB_FREQ3_CH0.default_map, `UVM_REG_ADDR_WIDTH'h2300000);
	  uvm_config_db #(uvm_reg_block)::set(null,"","RegisterModel_Debug",this);
	endfunction : build

	`uvm_object_utils(lpddr_subsystem_apb_reg_block)
endclass : lpddr_subsystem_apb_reg_block


endpackage

`endif
