// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD-ODR Datapath
//   Command Function Coverage
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

//address generator cmd received by dmc devices
covergroup dmc_dpc_cg (string cg_name) with function sample( dmc_addr_gen_seq_item dpc_item);
  option.per_instance = 1'b1;
  option.name = cg_name;

  // DPC address is not covered since it is redundat with AG covergroup
  cp_mask: coverpoint dpc_item.m_dpc_cmd.dpc_msk {
    // 8 bins to cover all mask ranges: 0, '1, and 6 bins of everything in between
    bins ZERO           = {0};
    bins IN_BETWEEN[6]  = {[1:64'hFFFF_FFFF_FFFF_FFFE]};
    bins ALL_ONE        = {64'hFFFF_FFFF_FFFF_FFFF};
  }

  cp_pad: coverpoint dpc_item.m_dpc_cmd.dpc_pad {
    bins NOT_PADDED = {0};
    bins PADDED     = {1};
  }

  cp_pad_val: coverpoint $signed(dpc_item.m_dpc_cmd.dpc_pad_val) iff (dpc_item.m_dpc_cmd.dpc_pad) {
    bins NEGATIVE_16_BIT  = {[-32768:-128]};
    bins NEGATIVE_8_BIT   = {[-127:-1]};
    bins ZERO             = {0};
    bins POSITIVE_8_BIT   = {[1:127]};
    bins POSITIVE_16_BIT  = {[128:32767]};
  }

  cp_intra_pad_val: coverpoint $signed(dpc_item.m_dpc_cmd.dpc_intra_pad_val) iff (dpc_item.m_dpc_cmd.dpc_msk != '1) {  // coverage for intra pad value, in case mask != '1, where mask will be actually applied
    bins NEGATIVE_16_BIT  = {[-32768:-128]};
    bins NEGATIVE_8_BIT   = {[-127:-1]};
    bins ZERO             = {0};
    bins POSITIVE_8_BIT   = {[1:127]};
    bins POSITIVE_16_BIT  = {[128:32767]};
  }

  cp_addr_out_of_range: coverpoint dpc_item.m_dpc_cmd.err_addr_out_of_range {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_error_transition: coverpoint dpc_item.m_dpc_cmd.err_addr_out_of_range {
    bins NO_ERROR_TO_NO_ERROR = (1'b0=> 1'b0);
    bins NO_ERROR_TO_ERROR    = (1'b0=> 1'b1);
    bins ERROR_TO_NO_ERROR    = (1'b1=> 1'b0);
    bins ERROR_TO_ERROR       = (1'b1=> 1'b1);
  }

  cp_pad_transition: coverpoint dpc_item.m_dpc_cmd.dpc_pad {
    bins NO_PAD_TO_NO_PAD = (1'b0=> 1'b0);
    bins NO_PAD_TO_PAD    = (1'b0=> 1'b1);
    bins PAD_TO_NO_PAD    = (1'b1=> 1'b0);
    bins PAD_TO_PAD       = (1'b1=> 1'b1);
  }


endgroup
