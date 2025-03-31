// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
/// Description: Custom APB address decoder and access rights check.
/// It enforces the following access rights depending on the manager
/// that performs the access (i_manager_idx).
///
/// * HOST has access to:
///    - OTP public        (RW)
///    - OTP wr protected  (RO)
///    - AOR wr protected  (RO)
///    - AOR public        (RW)
/// * JTAG has access to:
///    - OTP public        (RW)
///    - OTP wr protected  (RW when LCS=chip_wafer_test, RO otherwise)
///    - AOR wr protected  (RO)
///    - AOR public        (RW)
/// * KSE-3 has access to:
///    - OTP secure
///    - AOR secure        (RW)
///    - AOR wr protected  (RW)
///    - AOR public        (RW)
///

module soc_mgmt_secu_apb_dec
  import soc_mgmt_pkg::*;
  import rot_pkg::*;
(
  input  soc_mgmt_secu_encl_paddr_t   i_paddr,
  input  logic                        i_pwrite,
  input  logic                        i_lcs_is_chip_wafer_test,
  input  logic                        i_lcs_valid,
  input  secu_encl_apb_mux_idx_t      i_manager_idx,
  output secu_encl_apb_demux_idx_t    o_sub_idx
);

// -----------------------------------------------------------------------------
// signal declarations
// -----------------------------------------------------------------------------
logic     addr_is_otp;
logic     addr_is_otp_secu;
logic     addr_is_otp_public;
logic     addr_is_otp_wr_prot;
logic     addr_is_aor;
logic     addr_is_aor_wr_prot;
logic     addr_is_aor_secu;
logic     addr_is_aor_public;
logic     chip_wafer_test;

logic     rd_allowed;
logic     wr_allowed;
logic     not_allowed;

// -----------------------------------------------------------------------------
// RTL
// -----------------------------------------------------------------------------

// TODO(kluciani, Once OTP memory map is final, change this to check for base address only.)
always_comb addr_is_otp_secu    = (i_paddr >= OTP_SECU_START_ADDR)     & (i_paddr <= OTP_SECU_END_ADDR);
always_comb addr_is_otp_public  = (i_paddr >= OTP_PUB_START_ADDR)      & (i_paddr <= OTP_PUB_END_ADDR);
always_comb addr_is_otp_wr_prot = (i_paddr >= OTP_WR_PROT_START_ADDR)  & (i_paddr <= OTP_WR_PROT_END_ADDR);
always_comb addr_is_otp         = addr_is_otp_secu | addr_is_otp_public | addr_is_otp_wr_prot;

always_comb addr_is_aor_secu    = (i_paddr >= AOR_SECU_START_ADDR)     & (i_paddr <= AOR_SECU_END_ADDR);
always_comb addr_is_aor_wr_prot = (i_paddr >= AOR_WR_PROT_START_ADDR)  & (i_paddr <= AOR_WR_PROT_END_ADDR);
always_comb addr_is_aor_public  = (i_paddr >= AOR_PUB_START_ADDR)      & (i_paddr <= AOR_PUB_END_ADDR);
always_comb addr_is_aor         = addr_is_aor_wr_prot | addr_is_aor_secu | addr_is_aor_public;

always_comb chip_wafer_test     = i_lcs_valid & i_lcs_is_chip_wafer_test;

always_comb begin

  unique case (i_manager_idx)

    SECU_ENCL_APB_MUX_KSE_IDX : begin
      rd_allowed = addr_is_otp_secu | addr_is_aor_secu | addr_is_aor_wr_prot;
      wr_allowed = addr_is_otp_secu | addr_is_aor_secu | addr_is_aor_wr_prot;
    end
    SECU_ENCL_APB_MUX_HOST_IDX: begin
      rd_allowed = addr_is_otp_public | addr_is_otp_wr_prot | addr_is_aor_wr_prot | addr_is_aor_public;
      wr_allowed = addr_is_otp_public | addr_is_aor_public;
    end
    SECU_ENCL_APB_MUX_JTAG_IDX: begin
      rd_allowed = addr_is_otp_public | addr_is_otp_wr_prot | addr_is_aor_wr_prot | addr_is_aor_public;
      wr_allowed = addr_is_otp_public | addr_is_aor_public | (addr_is_otp_wr_prot & chip_wafer_test);
    end
    default: begin
      rd_allowed  = 1'b0;
      wr_allowed  = 1'b0;
    end

  endcase

  not_allowed = (i_pwrite & ~wr_allowed) | (~i_pwrite & ~rd_allowed);

end

always_comb o_sub_idx = not_allowed ? APB_DEMUX_ERR_IDX : // Forbidden access, error response
                        addr_is_otp ? APB_DEMUX_OTP_IDX : // Granted OTP access
                        addr_is_aor ? APB_DEMUX_AOR_IDX : // Granted AOR access
                                      APB_DEMUX_ERR_IDX ; // Out of range access

endmodule
