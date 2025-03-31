`ifndef AXI_ADDRESS_CHUNK_STRESS_SEQ_SV
`define AXI_ADDRESS_CHUNK_STRESS_SEQ_SV

// Chunk: range allocated by a memory allocator
// In the soc_periph's case subrange within a peripheral's address range
class axi_address_chunk_stress_seq extends svt_axi_master_base_sequence;

  axe_uvm_memory_range m_range;
  int m_transaction_count = 1;
  int max_allowed_burst_length = 16;  // AXI3
  `uvm_object_utils_begin(axi_address_chunk_stress_seq)
    `uvm_field_object(m_range, UVM_ALL_ON)
    `uvm_field_int(m_transaction_count, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction

  function set_wstrb(svt_axi_master_transaction tx);
    int burst_size = 2 ** tx.burst_size;
    int total_size = tx.burst_length * burst_size;
    int wrap_boundary = $floor(tx.addr / total_size) * total_size;
    int wrap_address = wrap_boundary + tx.burst_length * burst_size;
    int address = tx.addr;
    for (int i = 0; i < tx.burst_length; i++) begin
      case (tx.burst_size)
        svt_axi_transaction::BURST_SIZE_64BIT: begin
          if (address % 8 == 0) begin
            tx.wstrb[i] = 'hff;
          end else begin
            tx.wstrb[i] = 'hf0;
          end
        end
        svt_axi_transaction::BURST_SIZE_32BIT: begin
          if (address % 8 == 0) begin
            tx.wstrb[i] = 'h0f;
          end else begin
            tx.wstrb[i] = 'hf0;
          end
        end
        default: begin
          `uvm_fatal(get_type_name(), $sformatf("Unknown burst size: %0d", tx.burst_size))
        end
      endcase
      case (tx.burst_type)
        svt_axi_transaction::FIXED: begin
          address = tx.addr;
        end
        svt_axi_transaction::INCR: begin
          address += burst_size;
        end
        svt_axi_transaction::WRAP: begin
          address += burst_size;
          if (address >= wrap_address) begin
            address = wrap_boundary;
          end
        end
        default:; // Should not happen
      endcase
    end
  endfunction

  task body();
    svt_configuration get_cfg;
    super.body();
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal(get_type_name(),
                 "Unable to $cast the configuration to a svt_axi_port_configuration class")
    end
    `uvm_info(get_type_name(), "Sequence started!", UVM_HIGH)
    for (int i = 0; i < m_transaction_count; i++) begin
      svt_axi_master_transaction axi_tran;
      svt_axi_transaction::xact_type_enum xact_type;
      if ($urandom_range(0, 1)) begin
        xact_type = svt_axi_transaction::READ;
      end else begin
        xact_type = svt_axi_transaction::WRITE;
      end
      `uvm_create(axi_tran)
      axi_tran.port_cfg = cfg;
      // TODO: tweak the ready/valid delays
      if (!axi_tran.randomize() with {
            solve burst_type before addr, burst_length;
            xact_type == local:: xact_type;
            addr inside {[m_range.base : m_range.top]};
            atomic_type == svt_axi_transaction::NORMAL;
            addr inside {[m_range.base : m_range.top]};
            if (burst_type == svt_axi_transaction::WRAP) {
              // Make sure wrap address and boundary are within the allowed range
              (addr - (addr % (burst_length * (2**burst_size)))) inside {[m_range.base : m_range.top]};
              (addr - (addr % (burst_length * (2**burst_size))) + (burst_length * (2**burst_size))) inside {[m_range.base : m_range.top]};
            }
            if (burst_type == svt_axi_transaction::INCR) {
              (addr + burst_length * (2 ** burst_size)) inside {[m_range.base : m_range.top]};
            }
            addr % 4 == 0;  // Smallest burst size accepted by the fabric
            burst_size inside {svt_axi_transaction::BURST_SIZE_64BIT, svt_axi_transaction::BURST_SIZE_32BIT};
          }) begin
        `uvm_fatal(get_type_name(), "Failed to randomize transaction!")
      end

      if (xact_type == svt_axi_transaction::WRITE) begin
        set_wstrb(axi_tran);
      end

      /** Send the write transaction */
      `uvm_send(axi_tran)

      /** Wait for the write transaction to complete */
      `uvm_info(get_type_name(), "Waiting for response", UVM_HIGH)
      get_response(rsp, axi_tran.get_transaction_id());
      `uvm_info(get_type_name(), "Got response", UVM_HIGH)
    end
    `uvm_info(get_type_name(), "Sequence finished!", UVM_HIGH)
  endtask
endclass

`endif // AXI_ADDRESS_CHUNK_STRESS_SEQ_SV
