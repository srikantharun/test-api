// AI Core AXI directed test-case class
class ai_core_infra_axi_rnd_test extends ai_core_infra_base_test;

  // Registration with the factory
  `uvm_component_utils(ai_core_infra_axi_rnd_test)

  // Class Constructor
  function new(string name = "ai_core_infra_axi_rnd_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info (get_name, "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    axi_reset_seq.start(env.sequencer);
    axi_write_data = 64'h0000_BEEF_FACE_CAFE;

    foreach(env.axi_system_env.master[k]) begin
      gen_axi_addrs(k);
      foreach(axi_addr_q[i]) begin 
        bit [15:0] rnd_dt = $urandom_range(0,65535);
        axi_wr_seq.randomize() with {
          sequence_length == 'd1;
          cfg_addr        == axi_addr_q[i]; 
          cfg_data[0]     == {rnd_dt, axi_write_data[47:0]};
        };
        `uvm_info(get_name, $sformatf("writing @ %0h, data: %0h", axi_addr_q[i], axi_wr_seq.cfg_data[0]),UVM_HIGH)
        axi_wr_seq.start(env.axi_system_env.master[k].sequencer);

        #50ns
        axi_rd_seq.randomize() with {
          sequence_length == 'd1;
          cfg_addr        == axi_addr_q[i]; 
        };
        axi_rd_seq.start(env.axi_system_env.master[k].sequencer);
      end
      break;
    end

    #100ns;
    phase.drop_objection(this);
    `uvm_info (get_name, "Objection dropped", UVM_HIGH)
  endtask : run_phase

  function void gen_axi_addrs(masters_t mst);
    //bit [3:0] cid = core_id + 1;
    string str_idx;
    axi_addr_q.delete();
    //master can only access internal aicore addrs
    if (mst == noc_lt_s) begin
      foreach (ai_core_in_memory_map[i])  begin
        axi_addr_q.push_back({core_id,ai_core_in_memory_map[i][0][27:0]});
        `uvm_info(get_name, $sformatf("generated addr for %0s master, addr: %s %0h", mst.name, i, axi_addr_q[$]),UVM_HIGH)
       end
    end
    //cva6v interface can access all other aicores too
    else begin
      foreach (ai_core_out_memory_map[i])  begin
        axi_addr_q.push_back(ai_core_out_memory_map[i][0]);
        `uvm_info(get_name, $sformatf("generated addr for %0s master, addr: %s %0h", mst.name, i, axi_addr_q[$]),UVM_HIGH)
      end
      foreach (ai_core_in_memory_map[i]) begin 
        axi_addr_q.push_back({core_id,ai_core_in_memory_map[i][0][27:0]});
        `uvm_info(get_name, $sformatf("generated addr for %0s master, addr: %s %0h", mst.name, i, axi_addr_q[$]),UVM_HIGH)
      end
      //acessing different outer aicore
      foreach (ai_core_in_memory_map[i]) begin
        bit [3:0] out_cid;
        std::randomize(out_cid) with { out_cid inside {[1:8]}; out_cid != core_id;};
        axi_addr_q.push_back({out_cid,ai_core_in_memory_map[i][0][27:0]});
        `uvm_info(get_name, $sformatf("generated addr for %0s master, addr: %s %0h", mst.name, i, axi_addr_q[$]),UVM_HIGH)
      end

    end
  endfunction
  
endclass : ai_core_infra_axi_rnd_test

