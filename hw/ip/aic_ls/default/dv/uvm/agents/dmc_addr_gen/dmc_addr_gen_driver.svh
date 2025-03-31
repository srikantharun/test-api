`ifndef DMC_ADDR_GEN_DRIVER_SV
`define DMC_ADDR_GEN_DRIVER_SV

class dmc_addr_gen_driver extends uvm_driver#(dmc_addr_gen_seq_item);
  `uvm_component_utils(dmc_addr_gen_driver)

  localparam AG_RDY_TIMEOUT = 10000; //cycles
  int ag_rdy_timeout_cnt;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual dmc_addr_gen_if vif;

  uvm_analysis_port#(dmc_addr_gen_seq_item) ap;

  dmc_addr_gen_seq_item item_drv;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    item_drv = new();
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    vif.drv.ag_cmd  <= 0;
    vif.drv.ag_vld  <= 0;
    vif.drv.dpc_rdy <= 1;
    fork
      forever begin
        seq_item_port.get_next_item(req);
        @(vif.drv);
        while (vif.drv.ag_rdy !== 1) begin
          @(vif.drv);
          ag_rdy_timeout_cnt++;
          if (ag_rdy_timeout_cnt == AG_RDY_TIMEOUT)
            `uvm_fatal(get_name, $sformatf("ag_rdy timeout! Not asserted in %0d cycles, check if it's a bug or increase the timeout!",AG_RDY_TIMEOUT))
        end
        ag_rdy_timeout_cnt = 0;
        vif.drv.ag_vld <= 1;
        vif.drv.ag_cmd <= req.m_cmd;
        @(vif.drv);
        vif.drv.ag_vld <= 0;
        seq_item_port.item_done();
      end

      //mimics ready signal
      forever begin
        repeat ($urandom_range(0,4)) @(vif.drv);
        vif.drv.dpc_rdy <= 1;
        repeat ($urandom_range(60,100)) @(vif.drv);
        vif.drv.dpc_rdy <= 0;
      end
    join


  endtask
endclass

`endif


