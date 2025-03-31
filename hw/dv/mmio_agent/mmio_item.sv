`ifndef MMIO_ITEM_SV
`define MMIO_ITEM_SV

class mmio_item#(int DATA_WIDTH = 512, int ADDR_WIDTH = 22) extends uvm_sequence_item;
  `uvm_object_param_utils(mmio_item#(DATA_WIDTH, ADDR_WIDTH))

  rand bit[ADDR_WIDTH-1:0]  m_addr;
  rand bit[DATA_WIDTH-1:0] m_wdata;
  rand bit        m_we;
  rand bit[DATA_WIDTH-1:0] m_rdata;
  rand bit        m_error;
  rand mmio_txn_t m_type;
  rand int        m_port_num;

  function new (string name = "");
    super.new (name);
  endfunction : new

  virtual function mmio_item#(DATA_WIDTH, ADDR_WIDTH) do_clone();
    mmio_item#(DATA_WIDTH, ADDR_WIDTH) item;
    if(!$cast(item, this.clone())) begin
      `uvm_fatal(get_type_name(), "Clone failed")
    end
    return item;
  endfunction : do_clone

  virtual function void do_copy(uvm_object rhs);
    mmio_item seq_rhs;
    if(rhs == null) begin
      `uvm_fatal(get_type_name(), "do_copy from null ptr");
    end
    if(!$cast(seq_rhs, rhs)) begin
      `uvm_fatal(get_type_name(), "do_copy cast failed");
    end
    super.do_copy(rhs);
    this.m_addr   = seq_rhs.m_addr;
    this.m_wdata  = seq_rhs.m_wdata;
    this.m_rdata  = seq_rhs.m_rdata;
    this.m_error  = seq_rhs.m_error;
    this.m_port_num = seq_rhs.m_port_num;
  endfunction : do_copy

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n---------------------------------------------") };
    s = {s, $sformatf("\n  name  :   %s", get_name())};
    s = {s, $sformatf("\n  addr  :   0x%0x", m_addr)};
    s = {s, $sformatf("\n  we    :   0x%0x", m_we)};
    if (m_we==1) begin
      s = {s, $sformatf("\n  wdata :   0x%0x", m_wdata)};
    end else begin
      s = {s, $sformatf("\n  rdata :   0x%0x", m_rdata)};
    end
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;
  endfunction : convert2string

endclass : mmio_item

`endif // TOKEN_AGENT_SEQ_ITEM_SV

