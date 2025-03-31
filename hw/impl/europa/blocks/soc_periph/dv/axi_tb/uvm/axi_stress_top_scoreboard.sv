`ifndef AXI_STRESS_TOP_SCOREBOARD
`define AXI_STRESS_TOP_SCOREBOARD

`uvm_analysis_imp_decl(_from_axi_master_agent)

class axi_stress_top_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(axi_stress_top_scoreboard)

  uvm_analysis_imp_from_axi_master_agent #(svt_axi_transaction, axi_stress_top_scoreboard) axi_master_agent_export;

  axi_stress_top_config m_config;

  int bus_width_bytes = 8;  // 64 bits

  bit [7:0] m_address_map[bit [64:0]] = '{default: 'h0};

  function new(string name, uvm_component parent);
    super.new(name, parent);
    axi_master_agent_export = new("axi_master_agent_export", this);
  endfunction : new

  virtual function void write_from_axi_master_agent(svt_axi_transaction pkt);
    `uvm_info(get_type_name(), $sformatf(
              "Received tx from axi_master_agent: type: %d address:%h", pkt.xact_type, pkt.addr),
              UVM_HIGH)
    // Check address is at least aligned on 32 bits
    if (pkt.addr % 4 != 0) begin
      `uvm_error(get_type_name(), $sformatf("Address 'h%0h is not aligned on 32bits", pkt.addr))
      return;
    end
    case (pkt.xact_type)
      svt_axi_transaction::WRITE: handle_write_transaction(pkt);
      svt_axi_transaction::READ:  handle_read_transaction(pkt);
      default: begin
        `uvm_error(get_type_name(), $sformatf("Incorrect transaction type: %d", pkt.xact_type))
      end
    endcase
  endfunction : write_from_axi_master_agent

  extern function void handle_write_transaction(svt_axi_transaction pkt);
  extern function void update_address_map_fixed(svt_axi_transaction pkt);
  extern function void update_address_map_incr(svt_axi_transaction pkt);
  extern function void update_address_map_wrap(svt_axi_transaction pkt);
  extern function void handle_read_transaction(svt_axi_transaction pkt);
  extern function bit [7:0] get_data(bit [63:0] address);
  extern function void set_data(bit [63:0] address, bit [7:0] data);
  extern function void check_address_map_fixed(svt_axi_transaction pkt);
  extern function void check_address_map_incr(svt_axi_transaction pkt);
  extern function void check_address_map_wrap(svt_axi_transaction pkt);
  extern function void compare(bit [63:0] addr, bit [7:0] mem_byte, bit [7:0] read_byte);

endclass : axi_stress_top_scoreboard

function void axi_stress_top_scoreboard::handle_write_transaction(svt_axi_transaction pkt);
  // Discard transaction if it was unsuccessful
  `uvm_info(get_type_name(), $sformatf("Got write transaction: \n%s", pkt.sprint()), UVM_HIGH)
  if ((pkt.bresp != svt_axi_transaction::OKAY) && (pkt.bresp != svt_axi_transaction::EXOKAY)) begin
    `uvm_error(get_type_name(), $sformatf("Invalid slave response: %d", pkt.bresp))
    return;
  end

  case (pkt.burst_type)
    svt_axi_transaction::FIXED: update_address_map_fixed(pkt);
    svt_axi_transaction::INCR:  update_address_map_incr(pkt);
    svt_axi_transaction::WRAP:  update_address_map_wrap(pkt);
    default: begin
      `uvm_error(get_type_name(), $sformatf("Incorrect burst type: %d", pkt.burst_type))
    end
  endcase
endfunction

function void axi_stress_top_scoreboard::update_address_map_fixed(svt_axi_transaction pkt);
  int lower_offset = pkt.addr % bus_width_bytes;
  int burst_size = 2 ** pkt.burst_size;
  for (int i = 0; i < pkt.burst_length; i++) begin
    bit [7:0] wstrb = pkt.wstrb[i];
    int upper_bound = bus_width_bytes-lower_offset;
    if ((bus_width_bytes-lower_offset) > burst_size) begin
      upper_bound = burst_size;
    end
    for (int j = 0; j < upper_bound; j++) begin
      if (wstrb[j+lower_offset] == 1) set_data(pkt.addr + j, pkt.data[i][(j+lower_offset)*8+:8]);
    end
  end
endfunction

function void axi_stress_top_scoreboard::update_address_map_incr(svt_axi_transaction pkt);
  bit [63:0] address = pkt.addr;
  int burst_size = 2 ** pkt.burst_size;
  for (int i = 0; i < pkt.burst_length; i++) begin
    int lower_offset = address % bus_width_bytes;
    bit [7:0] wstrb = pkt.wstrb[i];
    int upper_bound = bus_width_bytes-lower_offset;
    if ((bus_width_bytes-lower_offset) > burst_size) begin
      upper_bound = burst_size;
    end
    for (int j = 0; j < upper_bound; j++) begin
      if (wstrb[j+lower_offset] == 1) set_data(address, pkt.data[i][(j+lower_offset)*8+:8]);
      address += 1;
    end
  end
endfunction

function void axi_stress_top_scoreboard::update_address_map_wrap(svt_axi_transaction pkt);
  int burst_size = 2 ** pkt.burst_size;
  int total_size = pkt.burst_length * burst_size;
  bit [63:0] wrap_boundary = $floor(pkt.addr / total_size) * total_size;
  bit [63:0] wrap_address = wrap_boundary + pkt.burst_length * burst_size;
  bit [63:0] address = pkt.addr;
  for (int i = 0; i < pkt.burst_length; i++) begin
    int lower_offset = address % bus_width_bytes;
    int upper_bound = bus_width_bytes-lower_offset;
    bit [7:0] wstrb = pkt.wstrb[i];
    if ((bus_width_bytes-lower_offset) > burst_size) begin
      upper_bound = burst_size;
    end
    if (address >= wrap_address) address = wrap_boundary;
    for (int j = 0; j < upper_bound; j++) begin
      if (wstrb[j+lower_offset] == 1) set_data(address, pkt.data[i][(j+lower_offset)*8+:8]);
      address += 1;
    end
  end
endfunction


function void axi_stress_top_scoreboard::handle_read_transaction(svt_axi_transaction pkt);

  `uvm_info(get_type_name(), $sformatf("Got read transaction: \n%s", pkt.sprint()), UVM_HIGH)
  if (pkt.rresp.size() != pkt.burst_length) begin
    `uvm_error(get_type_name(), $sformatf("Got %d read responses for %d transfers",
                                          pkt.rresp.size(), pkt.burst_length))
    return;
  end

  // Check that all transactions were successful
  for (int i = 0; i < pkt.burst_length; i++) begin
    bit [63:0] data;
    svt_axi_transaction::resp_type_enum rresp;
    rresp = pkt.rresp[i];
    data  = pkt.data[i];
    if ((rresp != svt_axi_transaction::OKAY) && (rresp != svt_axi_transaction::EXOKAY)) begin
      `uvm_error(get_type_name(), $sformatf("Invalid slave response: %d", rresp))
      return;
    end
  end

  case (pkt.burst_type)
    svt_axi_transaction::FIXED: check_address_map_fixed(pkt);
    svt_axi_transaction::INCR:  check_address_map_incr(pkt);
    svt_axi_transaction::WRAP:  check_address_map_wrap(pkt);
    default: begin
      `uvm_error(get_type_name(), $sformatf("Incorrect burst type: %d", pkt.burst_type))
    end
  endcase
endfunction


function bit [7:0] axi_stress_top_scoreboard::get_data(bit [63:0] address);
  bit [7:0] data;
  data = m_address_map[address];
  `uvm_info(get_type_name(), $sformatf("Getting %h which is %h", address, data), UVM_HIGH)
  return data;
endfunction

function void axi_stress_top_scoreboard::set_data(bit [63:0] address, bit [7:0] data);
  `uvm_info(get_type_name(), $sformatf("Setting %h to %h", address, data), UVM_HIGH)
  m_address_map[address] = data;
endfunction

function void axi_stress_top_scoreboard::check_address_map_fixed(svt_axi_transaction pkt);
  int burst_size = 2 ** pkt.burst_size;
  int lower_offset = pkt.addr % bus_width_bytes;

  foreach (pkt.data[i]) begin
    // When the address is not aligned on 64 bits, only the upper 32 bits contain relevant data
    int upper_bound = bus_width_bytes-lower_offset;
    if ((bus_width_bytes-lower_offset) > burst_size) begin
      upper_bound = burst_size;
    end
    for (int j = 0; j < upper_bound; j++) begin
      bit [63:0] address = pkt.addr + j;
      bit [ 7:0] read_byte = pkt.data[i][(j+lower_offset)*8+:8];
      bit [ 7:0] mem_value = get_data(address);
      compare(address, mem_value, read_byte);
    end
  end
endfunction

function void axi_stress_top_scoreboard::check_address_map_incr(svt_axi_transaction pkt);
  bit [63:0] address = pkt.addr;
  int burst_size = 2 ** pkt.burst_size;
  foreach (pkt.data[i]) begin
    int lower_offset = address % bus_width_bytes;
    int upper_bound = bus_width_bytes-lower_offset;
    if ((bus_width_bytes-lower_offset) > burst_size) begin
      upper_bound = burst_size;
    end
    for (int j = 0; j < upper_bound; j++) begin
      bit [7:0] read_byte = pkt.data[i][(lower_offset+j)*8+:8];
      bit [7:0] mem_value = get_data(address);
      compare(address, mem_value, read_byte);
      address += 1;
    end
  end
endfunction

function void axi_stress_top_scoreboard::check_address_map_wrap(svt_axi_transaction pkt);
  int burst_size = 2 ** pkt.burst_size;
  int total_size = pkt.burst_length * burst_size;
  bit [63:0] wrap_boundary = $floor(pkt.addr / total_size) * total_size;
  bit [63:0] wrap_address = wrap_boundary + pkt.burst_length * burst_size;
  bit [63:0] address = pkt.addr;
  for (int i = 0; i < pkt.burst_length; i++) begin
    int lower_offset = address % bus_width_bytes;
    int upper_bound = bus_width_bytes-lower_offset;
    if ((bus_width_bytes-lower_offset) > burst_size) begin
      upper_bound = burst_size;
    end
    if (address >= wrap_address) address = wrap_boundary;
    for (int j = 0; j < upper_bound; j++) begin
      bit [7:0] read_byte = pkt.data[i][(j+lower_offset)*8+:8];
      bit [7:0] mem_value = get_data(address);
      compare(address, mem_value, read_byte);
      address += 1;
    end
  end
endfunction

function void axi_stress_top_scoreboard::compare(bit [63:0] addr, bit [7:0] mem_byte,
                                                 bit [7:0] read_byte);
  `uvm_info(get_type_name(), $sformatf("[%h] Comparing %h with %h", addr, mem_byte, read_byte),
            UVM_HIGH)
  if (mem_byte != read_byte) begin
    `uvm_error(get_type_name(), $sformatf("Read error at address %h! Read value: %h, expected: %h",
                                          addr, read_byte, mem_byte))
  end
endfunction

`endif  //  `ifndef AXI_STRESS_TOP_SCOREBOARD
