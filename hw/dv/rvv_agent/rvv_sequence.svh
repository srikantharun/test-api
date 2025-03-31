`ifndef RVV_SEQUENCE_LIBRARY_SV
`define RVV_SEQUENCE_LIBRARY_SV

// Basic RVV sequence. it has the option to preload L1 if requested by test. It gets the L1 specific data from the test.
class rvv_sequence#(int DATA_WIDTH = 128, int ADDR_WIDTH = 22) extends uvm_sequence#(rvv_sequence_item#(DATA_WIDTH, ADDR_WIDTH));
  `uvm_object_param_utils(rvv_sequence#(DATA_WIDTH, ADDR_WIDTH))

  typedef bit[AIC_HT_AXI_ADDR_WIDTH-1:0] hp_addr_t;

  int repeat_cycles=1;
  int unsigned connections_num;
  int unsigned m_pword_size;
  hp_addr_t forced_address;

  function new (string name = "");
    super.new (name);
  endfunction : new

  task body();
    rvv_sequence_item#(DATA_WIDTH, ADDR_WIDTH) rvv_trans;

    `uvm_info(get_name(), $sformatf("rvv_sequence started!"), UVM_MEDIUM)
    for (int i=0; i<repeat_cycles; i++) begin
      `uvm_create(rvv_trans)
      rvv_trans.connections_num = connections_num;
      rvv_trans.address_alignment = m_pword_size/L1_SUB_BANKS_PER_BANK;
      rvv_trans.forced_address = forced_address;
      //randomize transaction
      if(!rvv_trans.randomize()) `uvm_error(get_name, "rvv_trans randomization error!");
      `uvm_info(get_name(), $sformatf("rvv_sequence[%0d] created:%s", i, rvv_trans.convert2string), UVM_MEDIUM)
      /** Send the write transaction and wait for the sequence item to be finished */
      `uvm_send(rvv_trans)
    end
    #10;
    `uvm_info(get_name(), $sformatf("rvv_sequence ended!"), UVM_MEDIUM)
  endtask: body
endclass : rvv_sequence

`endif // RVV_SEQUENCE_LIBRARY_SV

