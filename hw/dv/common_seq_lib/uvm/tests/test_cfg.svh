`ifndef GUARD_TEST_CFG_SV
`define GUARD_TEST_CFG_SV


  `define GRAPH_DDR_BASE_ADDR 'h0000_0000
  `define GRAPH_DDR_END_ADDR  'h3FFF_FFFF
  `define PP_DDR_BASE_ADDR    'h4000_0000
  `define PP_DDR_END_ADDR     'h7FFF_FFFF
  `define L2_BASE_ADDR        'h8000_0000
  `define L2_END_ADDR         'h801F_FFFF

class test_cfg extends uvm_object;

  `uvm_object_utils(test_cfg)

  bit [`AXI_HP_ADDR_WIDTH-1:0] DST_ADDR, SRC_ADDR;
  bw_t BW;
  size_t DATA_BSIZE;
  init_t INITIATOR;

  function new(string name="test_cfg");
    super.new(name);
  endfunction
endclass

`endif  
