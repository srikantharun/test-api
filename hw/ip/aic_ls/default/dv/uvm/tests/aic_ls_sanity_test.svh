// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Sanity Test
//      Does HW reset and operates IFD ODR to access L1
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_DMC_SANITY_TEST_SV
`define GUARD_AIC_DMC_SANITY_TEST_SV

class aic_ls_sanity_test extends aic_ls_dmc_cmdb_tc_test;
  `uvm_component_utils (aic_ls_sanity_test);

  function new (string name="aic_ls_sanity_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task test_seq();
    `uvm_info(get_name(), "Start of test", UVM_LOW)

    randomize_sequences();
    fork
      m_ifd_seq[0].start(null); // mvm ifd0
      m_ifd_seq[1].start(null); // mvm ifd1
      m_ifd_seq[2].start(null); // mvm ifd2
      m_ifd_seq[3].start(null); // mvm ifdw
      m_ifd_seq[4].start(null); // dwpu ifd0
      m_ifd_seq[5].start(null); // dwpu ifd1
      m_odr_seq[0].start(null); // mvm odr
      m_odr_seq[1].start(null); // dwpu odr
    join

    #20us;
    `uvm_info(get_name(), "End of test", UVM_LOW)
  endtask

endclass:aic_ls_sanity_test
`endif

