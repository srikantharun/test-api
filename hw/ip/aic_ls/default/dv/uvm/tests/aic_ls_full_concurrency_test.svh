// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AIC full concurrency test
//      This test preloads l1, and then launches a series of IFD sequences, AXI burst reads from L1, and a burst of RVV L1 reads, 
//      timed in a concurrent manner, to make sure that RVV waits for AXI to be done before it actually reads
//      this test only launches read based sequences, for simplicity and to avoid conflicts.
// Owner: Rafael Frangulyan Polyak <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_FULL_CONCURRENCY_TEST_SV
`define GUARD_AIC_LS_FULL_CONCURRENCY_TEST_SV

class aic_ls_full_concurrency_test extends aic_ls_simple_concurrency_test;
  `uvm_component_utils (aic_ls_full_concurrency_test);

  cfg_addr_t accessed_address;
  cfg_addr_t axi_address;
  cfg_addr_t rvv_address;
  int ifd_device_index;

  function new (string name="aic_ls_full_concurrency_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    m_test_iteration = 10;
    phase.drop_objection(this);
  endtask

  virtual function void randomize_sequences();
    int device_index = ifd_device_index;
    m_ifd_seq[device_index] = aic_ls_ifd_seq_t::type_id::create($sformatf("m_ifd_seq_%0d",device_index));
    m_ifd_seq[device_index].m_prev_tlast_count = m_ifd_tlast_count[device_index];
    m_ifd_seq[device_index].m_enable_cmdb = 0;
    if (!(m_ifd_seq[device_index].randomize() with {
      m_device          == AIC_LS_DMC_IFD_DEVICE[device_index];
      m_ag_cmd_format   == CMDFORMAT_LINEAR; // keep it simple
      m_ag_mem_baseaddr == axi_address;
      m_cid == m_env.m_env_cfg.m_cid;
      m_ag_mem_bsize    == 'h400; // don't want it to be too long
    })) begin
      `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
    end
    `uvm_info (get_name(), $sformatf("Created sequence for ifd %0d", device_index), UVM_LOW)
  endfunction

  virtual task test_seq();
    aic_ls_axi_master_fixed_read_sequence axi_read;
    hp_data_t rdata, bkdr_rdata;
    int address_index;

    `uvm_info(get_name(), "Start of test", UVM_LOW)

    init_l1();
    for (int iter=0; iter < m_test_iteration; iter++) begin
      // Randomize addr_a to be within the range 0 to 32'h3F_FFFF
      // accessed_address = $urandom_range(0, 'h3F_FFFF);
      ifd_device_index = $urandom_range(0, AIC_LS_ENV_IFD_NUM_DEVICE-1);
      enable_cmdblk(ifd_device_index);
      
      accessed_address = m_env_cfg.m_l1_full_start_addr + 'h1000*iter;
      axi_address = accessed_address;
      axi_address[5:0] = 0; // make it 64 size compatible

      rvv_address = accessed_address - m_env_cfg.m_l1_full_start_addr;
      rvv_address[3:0] = 0; // make it 16 size compatible

      randomize_sequences();

      address_index = (axi_address - (m_env_cfg.m_l1_full_start_addr))/m_env_cfg.m_pword_size;

      `uvm_info (get_name(), $sformatf("Forcing address 0x%0x on the test! AXI address is 0x%0x and RVV address is 0x%0x. device index is %0d", accessed_address, axi_address, rvv_address, ifd_device_index), UVM_LOW)
      rvv_seq.forced_address = rvv_address;

      // FD RD
      axi_read = aic_ls_axi_master_fixed_read_sequence::type_id::create("axi_read");
      if (!(axi_read.randomize() with {
          mem_addr        == axi_address;
          burst_len == 15;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for axi_read!")
      end
      
      fork
        begin
          axi_read.start(m_env.m_axi_system_env.master[1].sequencer);
        end
        begin
          repeat(4) @(posedge m_env.m_axi_system_env.vif.common_aclk);
          rvv_seq.start(m_env.m_rvv_agent.m_rvv_sequencer);
        end
        begin
          m_ifd_seq[ifd_device_index].start(null);
        end
      join
      //#100ns;
      rdata = axi_read.rsp.data[0];
      // BD READ
      bkdr_rdata = hdl_read(address_index);
      if (bkdr_rdata != rdata) begin
        `uvm_error(get_name(), $sformatf("BD_WR != FD_RD at L1 address: 0x%0x BD_WR: 0x%0x FD_RD: 0x%0x", axi_address, bkdr_rdata, rdata))
      end else begin
        `uvm_info (get_name(), $sformatf("[%0d] BD_WR == FD_RD to L1 address: 0x%0x is 0x%0x", iter, axi_address, rdata), UVM_LOW)
      end

      m_ifd_tlast_count[ifd_device_index] = m_ifd_seq[ifd_device_index].m_tlast_count;

      #10;
    end

    #20us;
    `uvm_info(get_name(), "End of test", UVM_LOW)
  endtask

endclass:aic_ls_full_concurrency_test
`endif

