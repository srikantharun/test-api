// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS L1 Function Coverage
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

/** L1 Memory Access via HP AXI Slave port. Cover built-in AXI parameters from VIP aside form self-coded function coverage. */
covergroup l1_axi_slv_cg with function sample(svt_axi_transaction trans, int num_concurrent);
  option.per_instance = 1'b1;
  option.name         = "l1_axi_slv_cg";

  cp_op : coverpoint (trans.xact_type) {
    bins AXI_WRITE = {svt_axi_transaction::WRITE};
    bins AXI_READ  = {svt_axi_transaction::READ};
  }

  cp_addr : coverpoint(trans.addr[AIC_DMC_COV_MMIO_ADDR_WIDTH-1:0]) {  // cover only the L1 address range
    bins L1_BANKS[AIC_DMC_COV_L1_NUM_BANKS] = {[AIC_DMC_COV_L1_ADDR_START : AIC_DMC_COV_L1_ADDR_END]};
  }

  cp_burst_length : coverpoint (trans.burst_length) {
    bins AXI_BURST_LEN[] = {[1:64]}; // till 64 only on PWORD access
  }

  cp_burst_size : coverpoint (trans.burst_size) {
    bins AXI_BURST_SIZE_64_BYTE = {6};
  }

  cp_burst_type : coverpoint (trans.burst_type);

  cp_concurrent_txn_num: coverpoint (num_concurrent) {
    bins TWO_CONCURRENT        = {2};
    bins THREE_CONCURRENT      = {3};
    bins MORE_THAN_THREE       = {[4:$]};
    ignore_bins NO_CONCURRENCY = {[0:1]};
  }

  cp_cross_op__addr_burst_len     : cross cp_op, cp_addr, cp_burst_length;
  cp_cross_op__addr__burst_size   : cross cp_op, cp_addr, cp_burst_size;
  cp_cross_op__addr__burst_type   : cross cp_op, cp_addr, cp_burst_type;
  cp_cross_op__concurrent_txn_num : cross cp_op, cp_concurrent_txn_num;
endgroup : l1_axi_slv_cg

covergroup l1_mmio_concurrency_cg with function sample(int num_concurrent, int concurrent_devices, int ch_num);
  option.per_instance = 1'b1;
  option.name         = "l1_mmio_concurrency_cg";

  cp_channel_number: coverpoint (ch_num) {
    bins MVM_IFD0   = {0};
    bins MVM_IFD1   = {1};
    bins MVM_IFD2   = {2};
    bins MVM_IFDW   = {3};
    bins MVM_ODR    = {4};
    bins DWPU_IFD0  = {5};
    bins DWPU_IFD1  = {6};
    bins DWPU_ODR   = {7};
    bins AXI_WR     = {8};
    bins AXI_RD     = {9};
    bins RVV        = {10};
  }

  cp_concurrent_txn_num: coverpoint (num_concurrent) {
    bins TWO_CONCURRENT        = {2};
    bins THREE_CONCURRENT      = {3};
    bins MORE_THAN_THREE       = {[4:$]};
    ignore_bins NO_CONCURRENCY = {[0:1]};
  }

  cp_concurrent_txn_sources: coverpoint (concurrent_devices) {
    bins DMC_ONLY                   = {3'b001};
    bins AXI2MMIO_ONLY              = {3'b010};
    bins RVV_ONLY                   = {3'b100};
    bins DMC_AND_AXI2MMIO           = {3'b011};
    bins DMC_AND_RVV                = {3'b101};
    bins AXI2MMIO_AND_RVV           = {3'b110};
    bins DMC_AND_AXI2MMIO_AND_RVV   = {3'b111};
    ignore_bins NO_CONCURRENCY      = {3'b000};
  }

  cp_cross_channel_num__concurrent_txn_num: cross cp_channel_number, cp_concurrent_txn_num;
endgroup
