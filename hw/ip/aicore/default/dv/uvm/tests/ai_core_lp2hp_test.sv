// This testcase checks the lp2hp resizing when cache[1]=1 (resizing enabled)
//CACHE[1]=0 (resizing disabled)
//TODO : Add checkers 

class ai_core_top_access_test extends ai_core_base_test;

  // Registration with the factory
  `uvm_component_utils(ai_core_top_access_test)
axi_master_write_sequence axi_wr_seq;
axi_master_read_sequence axi_rd_seq;
  bit [31:0]    axi_addr[$];
  int size;
  bit [3:0] cac_type;

  // Class constructor
  function new (string name="ai_core_top_access_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_top_access_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
  endfunction

  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    phase.raise_objection(this);
    

    //--------initial address read and write
    // Address and data
    `uvm_info("AI_CORE_TOP_REG",$sformatf("access starting"), UVM_LOW)
    //access start address
    axi_addr.push_back(`AI_CORE_L1_MEM_START_ADDR    );

    for(int i=0;i<axi_addr.size();i++) begin
      cac_type= $urandom_range(0,15);
      cac_type[1]= 1;
      axi_wr_seq.randomize() with {
        cfg_addr        == axi_addr[i];
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_10;
        cache_type == cac_type;
        cfg_data[0] == axi_write_data;
      };
      // Start the sequence on the respective sequencer
      axi_wr_seq.start(env.m_axi_system_env.master[0].sequencer);
      `uvm_info("AI_CORE_WR_ACCESS", $sformatf(" =================== \n%s",axi_wr_seq.sprint()), UVM_LOW)

      axi_rd_seq.randomize() with {
        cfg_addr        == axi_addr[i];
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_10;
      };
      axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer);
      `uvm_info("AI_CORE_RD_ACCESS", $sformatf(" =================== \n%s",axi_rd_seq.sprint()), UVM_LOW)

      `uvm_info("AI_CORE_ID", $sformatf(" ==========================  %0h",m_env_cfg.ai_core_cid), UVM_LOW)
      `uvm_info("AI_CORE_WR ADDR", $sformatf(" =====================  %0h",axi_wr_seq.rsp.addr), UVM_LOW)
      `uvm_info("AI_CORE_WR BRESP", $sformatf(" ==================== %0s",axi_wr_seq.rsp.bresp), UVM_LOW)
      `uvm_info("AI_CORE_RD ADDR",   $sformatf(" =================== %0h",axi_rd_seq.rsp.addr), UVM_LOW)
      `uvm_info("AI_CORE_RD RSEP",   $sformatf(" =================== %0s",axi_rd_seq.rsp.rresp[0]), UVM_LOW)
    end
    #50ns;

    //--------initial address read and write
    // Address and data
    `uvm_info("AI_CORE_TOP_REG",$sformatf("access starting"), UVM_LOW)
    //access start address

    for(int i=0;i<axi_addr.size();i++) begin
      cac_type= $urandom_range(0,15);
      cac_type[1]= 1;
      axi_wr_seq.randomize() with {
        cfg_addr        == axi_addr[i];
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_9;
        cache_type == cac_type;
        cfg_data[0] == axi_write_data;
      };
      // Start the sequence on the respective sequencer
      axi_wr_seq.start(env.m_axi_system_env.master[0].sequencer);
      `uvm_info("AI_CORE_WR_ACCESS", $sformatf(" =================== \n%s",axi_wr_seq.sprint()), UVM_LOW)

      axi_rd_seq.randomize() with {
        cfg_addr        == axi_addr[i];
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_9;
      };
      axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer);
      `uvm_info("AI_CORE_RD_ACCESS", $sformatf(" =================== \n%s",axi_rd_seq.sprint()), UVM_LOW)
      `uvm_info("AI_CORE_ID", $sformatf(" ==========================  %0h",m_env_cfg.ai_core_cid), UVM_LOW)
      `uvm_info("AI_CORE_WR ADDR", $sformatf(" =====================  %0h",axi_wr_seq.rsp.addr), UVM_LOW)
      `uvm_info("AI_CORE_WR BRESP", $sformatf(" ==================== %0s",axi_wr_seq.rsp.bresp), UVM_LOW)
      `uvm_info("AI_CORE_RD ADDR",   $sformatf(" =================== %0h",axi_rd_seq.rsp.addr), UVM_LOW)
      `uvm_info("AI_CORE_RD RSEP",   $sformatf(" =================== %0s",axi_rd_seq.rsp.rresp[0]), UVM_LOW)
    end
    #50ns;

    `uvm_info("AI_CORE_TOP_REG",$sformatf("access starting"), UVM_LOW)
    //access start address

    for(int i=0;i<axi_addr.size();i++) begin
      cac_type= $urandom_range(0,15);
      cac_type[1]= 0;
      axi_wr_seq.randomize() with {
        cfg_addr        == axi_addr[i];
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_9;
        cache_type == cac_type;
        cfg_data[0] == axi_write_data;
      };
      // Start the sequence on the respective sequencer
      axi_wr_seq.start(env.m_axi_system_env.master[0].sequencer);
      `uvm_info("AI_CORE_WR_ACCESS", $sformatf(" =================== \n%s",axi_wr_seq.sprint()), UVM_LOW)

      axi_rd_seq.randomize() with {
        cfg_addr        == axi_addr[i];
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_9;
      };
      axi_rd_seq.start(env.m_axi_system_env.master[0].sequencer);
      `uvm_info("AI_CORE_RD_ACCESS", $sformatf(" =================== \n%s",axi_rd_seq.sprint()), UVM_LOW)
      `uvm_info("AI_CORE_ID", $sformatf(" ==========================  %0h",m_env_cfg.ai_core_cid), UVM_LOW)
      `uvm_info("AI_CORE_WR ADDR", $sformatf(" =====================  %0h",axi_wr_seq.rsp.addr), UVM_LOW)
      `uvm_info("AI_CORE_WR BRESP", $sformatf(" ==================== %0s",axi_wr_seq.rsp.bresp), UVM_LOW)
      `uvm_info("AI_CORE_RD ADDR",   $sformatf(" =================== %0h",axi_rd_seq.rsp.addr), UVM_LOW)
      `uvm_info("AI_CORE_RD RSEP",   $sformatf(" =================== %0s",axi_rd_seq.rsp.rresp[0]), UVM_LOW)
    end


    phase.drop_objection(this);
  endtask

endclass:ai_core_top_access_test

