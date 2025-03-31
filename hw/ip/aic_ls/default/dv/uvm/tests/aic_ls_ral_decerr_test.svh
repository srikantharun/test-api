// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: RAL Write Read test. Access out of bounds address and check for DECERR.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_RAL_DECERR_TEST_SV
`define GUARD_AIC_LS_RAL_DECERR_TEST_SV

/* allowed ranges:
CSRs: 200_0000 - 207_0000
CMDs: 280_0000 - 287_0000
MEMs: 300_0000 - 308_0000
*/

// AI Core LS registers write/read testcase class
class aic_ls_ral_decerr_test extends aic_ls_ral_single_wrrd_test;
  `uvm_component_utils (aic_ls_ral_decerr_test)

  axi_simple_reset_sequence m_axi_reset_seq;
  uvm_reg m_reg_list[$];
  int m_loop_count = 100;

  rand uvm_reg_addr_t   m_invalid_addr_q[$];
  rand int unsigned     m_device_id_q[$];
  rand int unsigned     m_cid_q[$];


  constraint C_DEVICE_ID {
    m_device_id_q.size() == m_loop_count;
    foreach (m_device_id_q[i]) {
      //max 28 bits
      soft m_device_id_q[i] inside { [0:'hFFF] };
      soft !(m_device_id_q[i] inside { ['h200:'h208], ['h280:'h288], ['h300:'h308] });

    }
  }

  constraint C_CORE_ID {
    m_cid_q.size() == m_loop_count;
    foreach (m_cid_q[i]) {
      //max 28 bits
      soft m_cid_q[i] inside { [0:'hF] };

    }
  }

  constraint C_INVALID_ADDR {
    m_invalid_addr_q.size() == m_loop_count;
    foreach (m_invalid_addr_q[i]) {
      soft m_invalid_addr_q[i] >= 0;
      soft m_invalid_addr_q[i] <= 'hFFFF; 
      soft m_invalid_addr_q[i][2:0] == 0; // 64-bit aligned address
    }
  }

  function new (string name="aic_ls_ral_decerr_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  virtual function void build_phase(uvm_phase phase);
    set_type_override_by_type(aic_ls_env_pkg::svt_axi_reg_adapter::get_type(), aic_ls_env_pkg::aic_ls_axi_slverr_adapter::get_type());
    `uvm_info (get_name(), "Entered...",UVM_LOW)
    super.build_phase(phase);
    m_axi_reset_seq = axi_simple_reset_sequence::type_id::create("m_axi_reset_seq");
    `uvm_info (get_name(), "Exiting...",UVM_LOW)
  endfunction

  // Run phase
  virtual task run_phase(uvm_phase phase);
    aic_ls_axi_cfg_if_read_sequence axi_read;
    aic_ls_axi_cfg_if_write_sequence axi_write;
    uvm_reg_addr_t current_addr;
    bit   [63:0] wdata;
    bit   [63:0] rdata;

    phase.raise_objection(this);
    `uvm_info(get_name(), $sformatf("Run phase started, raising objection"), UVM_LOW)
    m_env.m_ls_regmodel.print();
    m_env.m_aic_ls_agt.vif.drv.disable_rdataX_aserrtion <= 1;

    // Start reset sequence on the sequencer
    m_axi_reset_seq.start(m_env.m_axi_virt_sqr);
    // Get register list
    m_env.m_ls_regmodel.get_registers(m_reg_list);
    
    if (!this.randomize()) begin
      `uvm_fatal(get_name(), "Randomziation failed!")
    end else begin
      foreach (m_invalid_addr_q[i]) begin
        current_addr = {m_cid_q[i], m_device_id_q[i], m_invalid_addr_q[i]};
        `uvm_info(get_name(), $sformatf("[%0d] Current addres is 0x%0x, comprised of: CID: 0x%0x DEVICE ID: 0x%0x ADDR: 0x%0x", i, m_cid_q[i], m_device_id_q[i], m_invalid_addr_q[i], current_addr), UVM_LOW)

        axi_write = aic_ls_axi_cfg_if_write_sequence::type_id::create("axi_write");
        wdata = {$urandom, $urandom};
        if (!(axi_write.randomize() with {
            cfg_addr        == current_addr;
            burst_length    == 1;
            sequence_length == 1;
        })) begin
          `uvm_fatal(get_name(), "Randomization failed for axi_write!")
        end
        axi_write.cfg_data_q.push_back(wdata);
        axi_write.start(m_env.m_axi_system_env.master[0].sequencer);
        if(axi_write.write_txn.bresp == svt_axi_transaction::DECERR) begin
          `uvm_info(get_name(), $sformatf("Address= 0x%0x and BRESP = %s", current_addr, axi_write.write_txn.bresp), UVM_LOW)
        end else begin
         `uvm_error(get_name(), $sformatf("Address= 0x%0x and BRESP = %s", current_addr, axi_write.write_txn.bresp))
        end

        axi_read = aic_ls_axi_cfg_if_read_sequence::type_id::create("axi_read");
        if (!(axi_read.randomize() with {
            cfg_addr        == current_addr;
            sequence_length == 1;
        })) begin
          `uvm_fatal(get_name(), "Randomization failed for axi_read!")
        end
        axi_read.start(m_env.m_axi_system_env.master[0].sequencer);
        foreach(axi_read.read_tran.rresp[i]) begin
          if(axi_read.read_tran.rresp[i] == svt_axi_transaction::DECERR) begin
           `uvm_info(get_name(), $sformatf("Address= 0x%0x and RRESP[%0d] = %s", current_addr, i, axi_read.read_tran.rresp[i]), UVM_LOW)
          end else begin
           `uvm_error(get_name(), $sformatf("Address= 0x%0x and RRESP[%0d] = %s", current_addr, i, axi_read.read_tran.rresp[i]))
          end
        end
        #100ns;
      end
    end
    phase.drop_objection(this);
    // recovery transaction
    `uvm_info(get_name(), "Doing recovery transactions...", UVM_LOW)
    m_skip_reset = 1;
    super.run_phase(phase);
    `uvm_info(get_name(), $sformatf("Run phase finished, dropping objection"), UVM_LOW)  
  endtask
endclass
`endif

