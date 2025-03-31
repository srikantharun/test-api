// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS L1 MMIO access concurrency
//              test using TC fabric
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_L1_MEM_SIZE_TEST_SV
`define GUARD_AIC_LS_L1_MEM_SIZE_TEST_SV

class aic_ls_l1_mem_size_test extends aic_ls_dmc_cmdb_lightcmd_test;
  `uvm_component_utils (aic_ls_l1_mem_size_test);

  int unsigned m_mem_bank_num = AIC_LS_ENV_L1_NUM_BANKS;
  int unsigned m_dmc_indx;
  int unsigned m_blk_size = 1024;

  function new (string name="aic_ls_l1_mem_size_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void overwrite_sequences(bit ifd_not_odr, int bank, int blk_size, bit use_offset);
    int offset = (bank==0 || use_offset==0)? 0: blk_size/2;
    if (ifd_not_odr==1) begin
      m_dmc_indx = $urandom_range(0, AIC_LS_ENV_IFD_NUM_DEVICE-1);
      m_ifd_seq[m_dmc_indx].m_ag_mem_baseaddr = (bank * AIC_LS_ENV_L1_BANK_SIZE) + (m_env.m_env_cfg.m_l1_full_start_addr) - offset;
      m_ifd_seq[m_dmc_indx].m_enable_cmdb = 0;
      m_ifd_seq[m_dmc_indx].m_ag_length =  blk_size;
    end else begin
      m_dmc_indx = $urandom_range(0, AIC_LS_ENV_ODR_NUM_DEVICE-1);
      m_odr_seq[m_dmc_indx].m_ag_mem_baseaddr = (bank * AIC_LS_ENV_L1_BANK_SIZE) + (m_env.m_env_cfg.m_l1_full_start_addr) - offset;
      m_odr_seq[m_dmc_indx].m_enable_cmdb = 0;
      m_odr_seq[m_dmc_indx].m_ag_length =  blk_size;
    end
  endfunction

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 1;
    enable_cmdblk();
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

  virtual task test_seq();
    `uvm_info (get_name(), "test_seq started", UVM_LOW)
    for (int iter= 0; iter < m_mem_bank_num; iter++) begin
      for (int dmc= 0; dmc < 2; dmc++) begin
        for (int use_offset= 0; use_offset < 2; use_offset++) begin
          `uvm_info (get_name(), $sformatf("Test Iteration %0d DMC %0d OFFSET %0d started.", iter, dmc, use_offset), UVM_LOW)
          randomize_sequences();
          overwrite_sequences(.ifd_not_odr(dmc), .bank(iter), .blk_size(m_blk_size), .use_offset(use_offset));

          if (dmc==1) begin
            m_ifd_seq[m_dmc_indx].start(null);
          end else begin
            m_odr_seq[m_dmc_indx].start(null);
          end
          #1us;
          if (dmc==1) begin
            m_ifd_tlast_count[m_dmc_indx] = m_ifd_seq[m_dmc_indx].m_tlast_count;
          end else begin
            m_odr_tlast_count[m_dmc_indx] = m_odr_seq[m_dmc_indx].m_tlast_count;
          end
          `uvm_info (get_name(), $sformatf("Test Iteration %0d DMC %0d OFFSET %0d done.", iter, dmc, use_offset), UVM_LOW)
          m_env.reset_addr_gen_refmodel();
        end
      end
    end
  endtask
endclass:aic_ls_l1_mem_size_test
`endif

