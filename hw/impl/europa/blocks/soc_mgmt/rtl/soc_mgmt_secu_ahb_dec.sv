// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
// Description: Custom AHB address decoder for JTAG manager's accesses to secure enclave IPs.

module soc_mgmt_secu_ahb_dec
import soc_mgmt_pkg::*;
import rot_pkg::*;
(
  input  soc_mgmt_haddr_t             i_haddr,
  output secu_encl_ahb_demux_idx_t    o_sub_idx
);

// -----------------------------------------------------------------------------
// RTL
// -----------------------------------------------------------------------------

// JTAG addresses to OTP, AON and KSE3 are the same as the APU ones, with unnecessary base address MSbits removed
localparam soc_mgmt_haddr_t KSE_ST_ADDR  = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR   [SOC_MGMT_HAW-1:0];
localparam soc_mgmt_haddr_t KSE_END_ADDR = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_END_ADDR  [SOC_MGMT_HAW-1:0];
localparam soc_mgmt_haddr_t OTP_ST_ADDR  = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR  [SOC_MGMT_HAW-1:0];
localparam soc_mgmt_haddr_t AOR_ST_ADDR  = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_ST_ADDR    [SOC_MGMT_HAW-1:0];

localparam int unsigned OTP_ADDR_SPACE_W = 16;
localparam int unsigned AOR_ADDR_SPACE_W = 16;

logic addr_is_kse;
logic addr_is_ao;
logic addr_is_otp;

always_comb addr_is_kse = (i_haddr >= KSE_ST_ADDR) && (i_haddr <= KSE_END_ADDR);
always_comb addr_is_ao  = i_haddr[SOC_MGMT_HAW-1:AOR_ADDR_SPACE_W] == AOR_ST_ADDR[SOC_MGMT_HAW-1:OTP_ADDR_SPACE_W];
always_comb addr_is_otp = i_haddr[SOC_MGMT_HAW-1:OTP_ADDR_SPACE_W] == OTP_ST_ADDR[SOC_MGMT_HAW-1:OTP_ADDR_SPACE_W];

always_comb begin

  o_sub_idx = SECU_ENCL_AHB_DEMUX_ERR_IDX;

  if (addr_is_kse) begin
    o_sub_idx = SECU_ENCL_AHB_DEMUX_KSE3_IDX;
  end else if (addr_is_ao || addr_is_otp) begin
    o_sub_idx = SECU_ENCL_AHB_DEMUX_OTP_AON_IDX;
  end

end

endmodule
