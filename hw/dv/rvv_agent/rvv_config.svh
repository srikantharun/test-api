`ifndef RVV_CONFIG_SV
`define RVV_CONFIG_SV

// Config File for RVV Agent
class rvv_config extends uvm_object;
  `uvm_object_utils(rvv_config)

  int   connections_num;
  int   data_width;
  int   addr_width;
  int   wbe_width;
  int          m_has_scoreboard;
  int unsigned banks_num;
  int unsigned sub_banks_num;
  string       m_memory_path;

  function new (string name = "rvv_config");
    super.new (name);
  endfunction

  function void set_defaults();  // Defaults to be used in case no configurations were passed.
    connections_num = 8;
    data_width = 128;
    addr_width = 22;
    wbe_width = (data_width + 7) / 8;
    m_has_scoreboard = 1;
    banks_num = 16;
    sub_banks_num = 4;
    m_memory_path = "hdl_top.dut.u_aic_ls.u_l1.u_l1_mem";
  endfunction

endclass

`endif // RVV_CONFIG_SV


