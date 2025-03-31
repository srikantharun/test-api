// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS ODR Sequence
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

class aic_ls_odr_seq#(type T = aic_ls_env) extends aic_ls_ifd_seq#(T);
  `uvm_object_param_utils(aic_ls_odr_seq#(T))

  typedef bit[AIC_LS_ENV_AXI_CFG_ADDR_W-1:0] cfg_addr_t;
  typedef bit[AIC_LS_ENV_AXI_CFG_DATA_W-1:0] cfg_data_t;
  typedef bit[AIC_LS_ENV_AXI_STREAM_DATA_W-1:0] stream_data_t;
  `ifdef AI_CORE_TOP_ENV_CHECK
   bit m_start_stream = 0;
  `else
   bit m_start_stream = 1;
  `endif

  rand int unsigned  m_axi_stream_mst_index;
  protected stream_data_t m_stream_data_q[$];
  protected axi_master_stream_base_sequence m_odr_stream_seq_q[$];

  bit m_debug_data_en;
  bit m_use_icdf_post_memory =0;

  constraint C_DEVICE {
    soft m_device inside {MODR, DODR};
  }

  constraint C_DEVICE_INDEX {
    (m_device==MODR) -> soft m_device_index==MVM_ODR;
    (m_device==DODR) -> soft m_device_index==DWPU_ODR;
  }

  constraint C_AXIS_MST_INDEX {
    (m_device==MODR) -> soft m_axi_stream_mst_index==2;
    (m_device==DODR) -> soft m_axi_stream_mst_index==3;
  }

  constraint C_DEVICE_ADDR_ALLOC {
    (m_device==MODR) -> soft m_ag_mem_baseaddr=='h830_0000 + m_cid * (1 << 28);
    (m_device==DODR) -> soft m_ag_mem_baseaddr=='h838_0000 + m_cid * (1 << 28);
  }

  // constraint C_INT_FORMAT_DEFAULT {  // to make adding constraint on int16/8 modes easier
  //   soft m_ag_header_vector_mode inside {0,1};
  //   soft m_ag_header_vector_mode == m_ag_format;
  // }

  constraint C_SOLVER_ODR {
    solve m_device before m_axi_stream_mst_index;
  }


  function new(string name = "aic_ls_odr_seq");
    super.new(name);
  endfunction

  `ifndef AI_CORE_TOP_ENV_CHECK
  virtual task gen_axi_stream();
    axi_master_stream_base_sequence odr_short_stream_seq;
    stream_data_t sdata;
    stream_data_t odr_short_stream_seq_data_cast [$];
    int unsigned txn_len;
    m_stream_data_q.delete();

    
    m_ls_env_h.m_dmc_ref_mdl[m_device_index].wait_address_gen_output(txn_len);
    //if (m_addr_item.header_vector_mode && !m_addr_item.m_format) txn_len = 2*txn_len; // format = 0 , vect_mode (config) = 1 means we have to supply double the data, to compress it from two lines of 32 int16 numbers into one data line of 64 int8 numbers
    m_stream_len = txn_len;
    `uvm_info(get_name(), $sformatf("Got stream length for %s! Length=%0d", m_device.name(), txn_len), UVM_LOW)

    for (int i = 0; i < txn_len; i++) begin
      if (m_debug_data_en==0) begin
        for (int d=0; d < AIC_LS_ENV_AXI_STREAM_DATA_W; d++) begin
          sdata[d] = bit'($urandom_range(0,1));
        end
      end else begin
        sdata = m_ag_mem_baseaddr + ((AIC_LS_ENV_AXI_STREAM_DATA_W/8)*i);
      end
      m_stream_data_q.push_back(sdata); // store all data
      if (i%m_stream_len==0) begin
        odr_short_stream_seq = axi_master_stream_base_sequence::type_id::create("odr_short_stream_seq");
        if (!(odr_short_stream_seq.randomize() with {
            sequence_length == 'd1;
        })) begin
          `uvm_fatal(get_name(), "Randomization failed for odr_short_stream_seq!")
        end
        odr_short_stream_seq.data.delete();
        odr_short_stream_seq.burst_length = m_stream_len;
      end
      odr_short_stream_seq.data.push_back(sdata);
      if (i%m_stream_len==m_stream_len-1) begin
        m_odr_stream_seq_q.push_back(odr_short_stream_seq); // stor for starting later
        if (m_use_icdf_post_memory) begin
          // Iterate over the original queue and cast each element
          foreach (odr_short_stream_seq.data[i]) begin
            odr_short_stream_seq_data_cast.push_back(stream_data_t'(odr_short_stream_seq.data[i]));
          end
          m_ls_env_h.m_dmc_ref_mdl[m_device_index].get_odr_stream(odr_short_stream_seq_data_cast, m_addr_item.header_vector_mode && !m_addr_item.m_format, m_addr_item.m_format);  // also passing in the casting argument
        end
      end
    end
  endtask: gen_axi_stream
  `else
  virtual task gen_axi_stream();
  endtask: gen_axi_stream
  `endif

  virtual task gen_and_send_stream();
    gen_axi_stream();
    fork
      begin
        foreach (m_odr_stream_seq_q[i]) begin
          `uvm_info(get_name(), $sformatf("AXI Stream[%0d of %0d] started for %s from AXI Stream MST%0d", i, m_odr_stream_seq_q.size()-1, m_device.name(), m_axi_stream_mst_index), UVM_LOW)
          m_odr_stream_seq_q[i].start(m_ral_env_h.m_axi_system_env.master[m_axi_stream_mst_index].sequencer);
          `uvm_info(get_name(), $sformatf("AXI Stream[%0d of %0d] Sent for %s from AXI Stream MST%0d", i, m_odr_stream_seq_q.size()-1, m_device.name(), m_axi_stream_mst_index), UVM_LOW)
        end
      end
      begin
        if (m_irq_status_field == "") begin
          #1ms;
          `uvm_fatal(get_name(), $sformatf("ODR stream timeout! for %s", m_device.name()))
        end else begin
          #100us;
          foreach (m_odr_stream_seq_q[i]) begin
            m_odr_stream_seq_q[i].kill();
          end
          `uvm_info(get_name(), $sformatf("Killing axi stream because of error scenario for %s", m_device.name()), UVM_LOW)
        end
      end
    join_any
    disable fork;
  endtask

  virtual task body();
    `uvm_info(get_name(), $sformatf("ODR Sequence start for %s, %s (pre-header)", m_device.name(), convert2string()), UVM_LOW)
    set_header();
    randomize_item();
    enable_cmdblk();
    write_cmdblk_data();
    if (m_start_stream==1) begin
      fork
        gen_and_send_stream();
      join_none
    end
    if (m_wait_for_status == 1) begin
      if (m_irq_status_field=="") begin
        read_register("cmdblk_status", "state", 1, 0, m_backdoor_polling); // poll STATE field to be 0 (IDLE)
      end else begin
        read_register("irq_status", m_irq_status_field, 1, 1, m_backdoor_polling); // poll error field to be 1
      end
    end
    `uvm_info(get_name(), $sformatf("ODR Sequence end for %s", m_device.name()), UVM_LOW)
  endtask : body

endclass : aic_ls_odr_seq

