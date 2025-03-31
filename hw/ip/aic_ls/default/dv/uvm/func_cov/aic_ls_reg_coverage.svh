// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Register Status/Ctrl
//   Function Coverage
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

covergroup ifd_reg_cg (string cg_name) with function sample(v_object v_obj);
  option.per_instance = 1'b1;
  option.name = cg_name;

  cp_addr_out_of_range_irq: coverpoint (v_obj.m_64bit_data[0]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_mmio_error_irq: coverpoint (v_obj.m_64bit_data[1]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_cmdb_cmd_dropped_irq: coverpoint (v_obj.m_64bit_data[8]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_decomp_access_error_irq: coverpoint (v_obj.m_64bit_data[16]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_decomp_invalid_stream_irq: coverpoint (v_obj.m_64bit_data[17]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_decomp_invalid_scheme_irq: coverpoint (v_obj.m_64bit_data[18]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_decomp_invalid_compressed_size_irq: coverpoint (v_obj.m_64bit_data[19]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_decomp_invalid_uncompressed_size_irq: coverpoint (v_obj.m_64bit_data[20]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_cmdb_fifo_count: coverpoint (v_obj.m_64bit_data[23:16]) iff (v_obj.m_string == "cmdblk_status") {
    bins EMPTY        = {0};
    bins ALMOST_EMPTY = {1};
    bins ALMOST_FULL  = {AIC_DMC_COV_CMDB_FIFO_DEPTH-1};
    bins FULL         = {AIC_DMC_COV_CMDB_FIFO_DEPTH};
  }

  cp_cmdb_outstanding_txn: coverpoint (v_obj.m_64bit_data[31:24]) iff (v_obj.m_string == "cmdblk_status") {
    bins ZERO          = {0};
    bins ONE           = {1};
    bins MORE_THAN_ONE = {[2:$]};
  }

endgroup

covergroup odr_reg_cg (string cg_name) with function sample(v_object v_obj);
  option.per_instance = 1'b1;
  option.name = cg_name;

  cp_unexp_tlast_low_irq: coverpoint (v_obj.m_64bit_data[2]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_unexp_tlast_high_irq: coverpoint (v_obj.m_64bit_data[3]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_addr_out_of_range_irq: coverpoint (v_obj.m_64bit_data[4]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_vtrsp_irq: coverpoint (v_obj.m_64bit_data[5]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_mmio_error_irq: coverpoint (v_obj.m_64bit_data[6]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_cmdb_cmd_dropped_irq: coverpoint (v_obj.m_64bit_data[8]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

  cp_vtrsp_access_error_irq: coverpoint (v_obj.m_64bit_data[16]) iff (v_obj.m_string == "irq_status") {
    bins NO_ERROR  = {0};
    bins HAS_ERROR = {1};
  }

   cp_cmdb_fifo_count: coverpoint (v_obj.m_64bit_data[23:16]) iff (v_obj.m_string == "cmdblk_status") {
    bins EMPTY        = {0};
    bins ALMOST_EMPTY = {1};
    bins ALMOST_FULL  = {AIC_DMC_COV_CMDB_FIFO_DEPTH-1};
    bins FULL         = {AIC_DMC_COV_CMDB_FIFO_DEPTH};
  }

  cp_cmdb_outstanding_txn: coverpoint (v_obj.m_64bit_data[31:24]) iff (v_obj.m_string == "cmdblk_status") {
    bins ZERO          = {0};
    bins ONE           = {1};
    bins MORE_THAN_ONE = {[2:$]};
  }

endgroup

