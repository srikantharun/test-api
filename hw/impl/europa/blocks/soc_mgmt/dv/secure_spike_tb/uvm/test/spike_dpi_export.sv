`ifndef SECURE_SPIKE_DPI_EXPORT_SV
`define SECURE_SPIKE_DPI_EXPORT_SV

// Export these tasks so that they can be visible from the C++ code
export "DPI-C" task rot_kse_write;
export "DPI-C" task rot_kse_read;
export "DPI-C" task spm_write;
export "DPI-C" task spm_read;

// Basic AXI read/write tasks called by exported tasks
task automatic axi_write(input bit [31:0] addr, input bit [63:0] data, input int len,
                         input svt_axi_master_agent agent, output byte resp);

  axi_master_single_write_seq write_seq;
  write_seq = axi_master_single_write_seq::type_id::create("write_seq");
  write_seq.addr = addr;
  write_seq.data = data;
  write_seq.len = len;
  write_seq.set_item_context(null, agent.sequencer);
  `uvm_info("axi_write", $sformatf(
            "[%s] addr=%16h, data=%16h, len=%d", agent.get_type_name(), addr, data, len), UVM_HIGH);
  write_seq.start(agent.sequencer);

  if ((write_seq.bresp == 2'b00) || (write_seq.bresp == 2'b01)) begin
    resp = 0;
  end else begin
    resp = 1;
  end
endtask

task automatic axi_read(input bit [31:0] addr, output bit [63:0] data, input int len,
                        input svt_axi_master_agent agent, output byte resp);

  axi_master_single_read_seq read_seq;
  bit [63:0] mask;

  read_seq = axi_master_single_read_seq::type_id::create("read_seq");
  read_seq.addr = addr;
  read_seq.set_item_context(null, agent.sequencer);
  read_seq.start(agent.sequencer);

  // Extract the data read
  mask = 16'h0;
  for (int i = 0; i < len; i++) begin
    mask += (16'hff << 8 * i);
  end
  data = read_seq.data;

  `uvm_info("axi_read", $sformatf(
            "[%s] addr=%16h, data=%16h, len=%d", agent.get_type_name(), addr, data, len), UVM_HIGH);

  if ((read_seq.rresp == 2'b00) || (read_seq.rresp == 2'b01)) begin
    resp = 0;
  end else begin
    resp = 1;
  end
endtask

task automatic rot_kse_write(input bit [31:0] addr, input bit [63:0] data, input int len,
                                output byte resp);
  uvm_component comp;
  svt_axi_system_env system_env;

  // Start a single write sequence on the master AXI VIP
  comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env");
  if (!$cast(system_env, comp))
    `uvm_fatal("rot_kse_write", "Failed to cast uvm_component to svt_axi_system_env!")

  axi_write(addr, data, len, system_env.master[0], resp);
endtask

task automatic rot_kse_read(input bit [31:0] addr, output bit [63:0] data, input int len,
                               output byte resp);
  uvm_component comp;
  svt_axi_system_env system_env;

  comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env");
  if (!$cast(system_env, comp))
    `uvm_fatal("rot_kse_read", "Failed to cast uvm_component to svt_axi_system_env!")

  // Start a single read sequence on the master AXI VIP
  axi_read(addr, data, len, system_env.master[0], resp);
endtask

task automatic spm_write(input bit [31:0] addr, input bit [63:0] data, input int len,
                         output byte resp);
  uvm_component comp;
  svt_axi_system_env system_env;

  // Start a single write sequence on the master AXI VIP
  comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env");
  if (!$cast(system_env, comp))
    `uvm_fatal("spm_write", "Failed to cast uvm_component to svt_axi_system_env!")

  axi_write(addr, data, len, system_env.master[1], resp);
endtask

task automatic spm_read(input bit [31:0] addr, output bit [63:0] data, input int len,
                        output byte resp);
  uvm_component comp;
  svt_axi_system_env system_env;

  comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env");
  if (!$cast(system_env, comp))
    `uvm_fatal("spm_read", "Failed to cast uvm_component to svt_axi_system_env!")

  // Start a single read sequence on the master AXI VIP
  axi_read(addr, data, len, system_env.master[1], resp);
endtask




`endif  // SECURE_SPIKE_DPI_EXPORT_SV
