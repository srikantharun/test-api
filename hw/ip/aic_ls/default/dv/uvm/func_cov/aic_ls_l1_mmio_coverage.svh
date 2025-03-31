// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS L1 MMIO Function Coverage
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

/** Covers l1 access through mmio interface */
covergroup l1_dmc_mmio_cg (string cg_name) with function sample(bit[AIC_DMC_COV_MMIO_ADDR_WIDTH-1:0] addr, bit error, int num_concurrent);
  option.per_instance = 1'b1;
  option.name = cg_name;

  cp_l1_bank : coverpoint(addr[9:6]) {  // we're looking at bank value, it's defined by bits 9:6 = 0/64/128/.../960. after that we're done cycling the 16 banks.
    bins L1_BANKS[] = {[0:AIC_DMC_COV_L1_NUM_BANKS-1]};
  }

  cp_error: coverpoint error {
    bins NO_MMIO_ERROR = {0};
    bins WITH_MMIO_ERROR = {1};
  }

  cp_concurrent_txn_num: coverpoint num_concurrent {
    bins TWO_CONCURRENT        = {2};
    bins THREE_CONCURRENT      = {3};
    bins MORE_THAN_THREE       = {[4:$]};
    ignore_bins NO_CONCURRENCY = {[0:1]};
  }

  cp_cross_l1_bank__concurrent_txn_num: cross cp_l1_bank, cp_concurrent_txn_num;
endgroup

covergroup l1_rvv_mmio_cg (string cg_name) with function sample(bit[AIC_DMC_COV_MMIO_ADDR_WIDTH-1:0] addr, bit write_not_read, int num_concurrent);
  option.per_instance = 1'b1;
  option.name = cg_name;

  cp_l1_bank : coverpoint(addr[9:6]) {  // we're looking at bank value, it's defined by bits 9:6 = 0/64/128/.../960. after that we're done cycling the 16 banks.
    bins L1_BANKS[] = {[0:AIC_DMC_COV_L1_NUM_BANKS-1]};
  }

  cp_l1_sub_bank : coverpoint(addr[5:4]) {  // we're looking at sub bank value, it's defined by bits 5:4 = 0/16/32/48. 64 is already defining bank num.
    bins L1_SUB_BANKS[] = {[0:AIC_DMC_COV_L1_NUM_SUB_BANKS-1]};
  }

  cp_read_or_write : coverpoint write_not_read {
    bins READ = {0};
    bins WRITE = {1};
  }

  cp_concurrent_txn_num: coverpoint num_concurrent {
    bins TWO_CONCURRENT        = {2};
    bins THREE_CONCURRENT      = {3};
    bins MORE_THAN_THREE       = {[4:$]};
    ignore_bins NO_CONCURRENCY = {[0:1]};
  }
endgroup


