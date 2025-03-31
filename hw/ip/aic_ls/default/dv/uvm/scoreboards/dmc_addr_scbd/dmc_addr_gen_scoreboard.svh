`ifndef DMC_ADDR_GEN_SCOREBOARD_SV
`define DMC_ADDR_GEN_SCOREBOARD_SV

/*
the scoreboards waits for data from two sources:
- reference model: list of expected addresses, masks, pad values.
- DUT address generation module: same data
the scoreboards then makes sure that they're equal. if they are, it's safe to check the actual data in dmc_Data_scoreboard.
*/
class dmc_addr_gen_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(dmc_addr_gen_scoreboard)

  dmc_addr_gen_seq_item mon_item;
  dmc_addr_gen_seq_item mdl_item;
  event m_rst_evt;
  event m_rst_done_evt;

  uvm_tlm_analysis_fifo#(dmc_addr_gen_seq_item) act_fifo; // the actual output from rtl datapath
  uvm_tlm_analysis_fifo#(dmc_addr_gen_seq_item) exp_fifo; // coming from refmodel/ python script golden model

  int mon_cnt, mdl_cnt;

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon_item = dmc_addr_gen_seq_item::type_id::create("mon_item");
    mdl_item = dmc_addr_gen_seq_item::type_id::create("mdl_item");
    act_fifo = new("act_fifo", this);
    exp_fifo = new("exp_fifo", this);
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    dmc_addr_gen_seq_item itm;
    super.run_phase(phase);
    forever begin
      fork
        forever begin
          act_fifo.get(mon_item);
          `uvm_info(get_name, $sformatf("Got mon_item: #%0d %s", mdl_cnt, mon_item.dpc_cmd_2string()), UVM_MEDIUM)
          exp_fifo.get(mdl_item);
          `uvm_info(get_name, $sformatf("Got mdl_item: #%0d %s", mdl_cnt, mdl_item.dpc_cmd_2string()), UVM_MEDIUM)
          if (mon_item.m_dpc_cmd != mdl_item.m_dpc_cmd) begin
            `uvm_error(get_name, $sformatf("Mismatch #%0d m_dpc_cmd \nmdl: %s\nrtl: %s", mon_cnt, mdl_item.dpc_cmd_2string(), mon_item.dpc_cmd_2string()))
          end else begin
            `uvm_info(get_name, $sformatf("Match #%0d m_dpc_cmd \nmdl: %s\nrtl: %s", mdl_cnt, mdl_item.dpc_cmd_2string(), mon_item.dpc_cmd_2string()), UVM_MEDIUM)
          end
          mon_cnt++;
          mdl_cnt++;
        end
        begin
          @ (m_rst_evt);
          while(act_fifo.try_get(itm));
          while(exp_fifo.try_get(itm));
          mon_cnt = 0;
          mdl_cnt = 0;
          @ (m_rst_done_evt);
          `uvm_info(get_name(), "Reset happened", UVM_NONE)
        end
      join_any
      disable fork;
    end
  endtask : run_phase

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    if (!exp_fifo.is_empty()) begin
      `uvm_error(get_name, $sformatf("exp_fifo is not empty with %0d items", exp_fifo.used()))
    end
    if (!act_fifo.is_empty()) begin
      `uvm_error(get_name, $sformatf("act_fifo is not empty with %0d items", act_fifo.used()))
    end
    if (mon_cnt != mdl_cnt) begin
      `uvm_error(get_name, $sformatf("number of received items RTL vs MDL mismatch, mdl: %0d rtl: %0d",mdl_cnt,mon_cnt))
    end
  endfunction


endclass
`endif
