`ifndef SOC_IO_SPIKE_DPI_EXPORT_SV
`define SOC_IO_SPIKE_DPI_EXPORT_SV

`include "spike_dpi_macros.svh"

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


`SPIKE_DPI_TASK_WRITE(soc_periph);
  uvm_component comp;
  svt_axi_system_env system_env;

  // Start a single write sequence on the master AXI VIP
  comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env");
  if (!$cast(system_env, comp))
    `uvm_fatal("soc_periph_write", "Failed to cast uvm_component to svt_axi_system_env!")

  axi_write(addr, data, len, system_env.master[0], resp);
endtask

`SPIKE_DPI_TASK_READ(soc_periph);
  uvm_component comp;
  svt_axi_system_env system_env;

  comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env");
  if (!$cast(system_env, comp))
    `uvm_fatal("soc_periph_read", "Failed to cast uvm_component to svt_axi_system_env!")

  // Start a single read sequence on the master AXI VIP
  axi_read(addr, data, len, system_env.master[0], resp);
endtask

`SPIKE_DPI_TASK_WRITE(spm);
  uvm_component comp;
  svt_axi_system_env system_env;

  // Start a single write sequence on the master AXI VIP
  comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env");
  if (!$cast(system_env, comp))
    `uvm_fatal("spm_write", "Failed to cast uvm_component to svt_axi_system_env!")

  axi_write(addr, data, len, system_env.master[1], resp);
endtask

`SPIKE_DPI_TASK_READ(spm);
  uvm_component comp;
  svt_axi_system_env system_env;

  comp = uvm_top.find("uvm_test_top.m_env.m_axi_system_env");
  if (!$cast(system_env, comp))
    `uvm_fatal("spm_read", "Failed to cast uvm_component to svt_axi_system_env!")

  // Start a single read sequence on the master AXI VIP
  axi_read(addr, data, len, system_env.master[1], resp);
endtask

`SPIKE_DPI_TASK_WRITE(i2c0_master);
  spike_top_config top_config;

  if (!uvm_config_db#(spike_top_config)::get(null, "uvm_test_top", "config", top_config))
    `uvm_fatal("i2c0_master_write", "Failed to get top config")

  assert (len == 1)
  else `uvm_fatal("i2c0_master_write", $sformatf("write len is greater than 1 byte: %0d", len))
  top_config.i2c0_master_vif.write_reg(addr[2:0], data);
  resp = 'h0;  // We respond ok everytime
endtask

`SPIKE_DPI_TASK_READ(i2c0_master);
  spike_top_config top_config;

  if (!uvm_config_db#(spike_top_config)::get(null, "uvm_test_top", "config", top_config))
    `uvm_fatal("i2c0_master_read", "Failed to get top config")

  assert (len == 1)
  else `uvm_fatal("i2c0_master_read", $sformatf("read len is greater than 1 byte: %0d", len))
  top_config.i2c0_master_vif.read_reg(addr[2:0], data);
  resp = 'h0;  // We respond ok everytime
endtask

`SPIKE_DPI_TASK_WRITE(i2c1_master);
  spike_top_config top_config;

  if (!uvm_config_db#(spike_top_config)::get(null, "uvm_test_top", "config", top_config))
    `uvm_fatal("i2c0_master_write", "Failed to get top config")

  assert (len == 1)
  else `uvm_fatal("i2c0_master_write", $sformatf("write len is greater than 1 byte: %0d", len))
  top_config.i2c1_master_vif.write_reg(addr[2:0], data);
  resp = 'h0;  // We respond ok everytime
endtask

`SPIKE_DPI_TASK_READ(i2c1_master);
  spike_top_config top_config;

  if (!uvm_config_db#(spike_top_config)::get(null, "uvm_test_top", "config", top_config))
    `uvm_fatal("i2c0_master_read", "Failed to get top config")

  assert (len == 1)
  else `uvm_fatal("i2c0_master_read", $sformatf("read len is greater than 1 byte: %0d", len))
  top_config.i2c1_master_vif.read_reg(addr[2:0], data);
  resp = 'h0;  // We respond ok everytime
endtask

`endif  // SOC_IO_SPIKE_DPI_EXPORT_SV
