//The uvm_analysis_imp_decl allows for a scoreboard (or other analysis component) to
// support input from many places
/** Macro that define two analysis ports with unique suffixes */
`uvm_analysis_imp_decl(_initiated)
`uvm_analysis_imp_decl(_initiated_ctrlr)
`uvm_analysis_imp_decl(_response)

//TS
`uvm_analysis_imp_decl(_actual_response_noc_hp)
`uvm_analysis_imp_decl(_actual_response_mvm)
`uvm_analysis_imp_decl(_actual_response_dwpu)
`uvm_analysis_imp_decl(_actual_response_dpu_0)
`uvm_analysis_imp_decl(_actual_response_dpu_1)
`uvm_analysis_imp_decl(_actual_response_ls_lp)
`uvm_analysis_imp_decl(_actual_response_ls_hp)

class axi_uvm_scoreboard extends uvm_scoreboard;

  /** Analysis port connected to the AXI Master Agent */
  uvm_analysis_imp_initiated#(svt_axi_transaction, axi_uvm_scoreboard) item_observed_initiated_export;

  /** Analysis port connected to the AXI Master Agent */
  uvm_analysis_imp_initiated_ctrlr#(svt_axi_transaction, axi_uvm_scoreboard) item_observed_initiated_export_ctrlr;

  /** Analysis port conneted to the AXI Slave Agent */
  uvm_analysis_imp_response#(svt_axi_transaction, axi_uvm_scoreboard) item_observed_response_export;

  /** Analysis port conneted to the passive MVM AXI Slave Agent */
  uvm_analysis_imp_actual_response_mvm#(svt_axi_transaction, axi_uvm_scoreboard) actual_data_response_export_mvm;

  /** Analysis port conneted to the passive DWPU AXI Slave Agent */
  uvm_analysis_imp_actual_response_dwpu#(svt_axi_transaction, axi_uvm_scoreboard) actual_data_response_export_dwpu;

  /** Analysis port conneted to the passive DPU_0 AXI Slave Agent */
  uvm_analysis_imp_actual_response_dpu_0#(svt_axi_transaction, axi_uvm_scoreboard) actual_data_response_export_dpu_0;

  /** Analysis port conneted to the passive DPU_1 AXI Slave Agent */
  uvm_analysis_imp_actual_response_dpu_1#(svt_axi_transaction, axi_uvm_scoreboard) actual_data_response_export_dpu_1;

  /** Analysis port conneted to the passive LS_LP AXI Slave Agent */
  uvm_analysis_imp_actual_response_ls_lp#(svt_axi_transaction, axi_uvm_scoreboard) actual_data_response_export_ls_lp;

  /** Analysis port conneted to the passive LS_HP AXI Slave Agent */
  uvm_analysis_imp_actual_response_ls_hp#(svt_axi_transaction, axi_uvm_scoreboard) actual_data_response_export_ls_hp;

  /** Analysis port conneted to the NOC_HP AXI Slave Agent */
  uvm_analysis_imp_actual_response_noc_hp#(svt_axi_transaction, axi_uvm_scoreboard) actual_data_response_export_noc_hp;

  virtual ai_core_top_if tb_cfg_if;

  // ai_core environment configuration
  ai_core_top_env_cfg m_env_cfg;

  /** UVM Component Utility macro */
  `uvm_component_utils(axi_uvm_scoreboard)

  int num_of_exp_pkts,num_of_exp_pkts_ctrlr,num_of_act_pkts_mvm,num_of_act_pkts_dwpu,num_of_act_pkts_dpu_0,num_of_act_pkts_dpu_1,num_of_act_pkts_ls_lp, num_of_act_pkts_ls_hp, num_of_act_pkts_noc_hp, num_of_act_pkts_noc_lp;
  svt_axi_master_reg_transaction reg_xact;
  svt_axi_transaction act_xact_mvm[$];
  svt_axi_transaction act_xact_dwpu[$];
  svt_axi_transaction act_xact_dpu_0[$];
  svt_axi_transaction act_xact_dpu_1[$];
  svt_axi_transaction act_xact_ls_lp[$];
  svt_axi_transaction act_xact_ls_hp[$];
  svt_axi_transaction act_xact_noc_hp[$];
  svt_axi_transaction act_xact_noc_lp[$];
  bit vld_addr, vld_addr_decerr, vld_addr_decerr_exp;
  bit [36-1:0] addr_tmp;

  svt_axi_transaction tx,tx_pkt,tx_drv,rx_pkt;
  int k,dt_size,q_size, addr_dec_cid;

  bit [36-1:0] l2_rsrvd_lp_noc_min, l2_rsrvd_lp_noc_max   ;

  int tot_act_pkt, tot_exp_pkt;
  int unsigned write_pkt_success=0,write_pkt_failure=0, read_pkt_success=0,read_pkt_failure=0;

  function new (string name = "axi_uvm_scoreboard", uvm_component parent=null);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build();

    //getting tb configuration interface in environment
    uvm_config_db#(virtual ai_core_top_if)::get(uvm_root::get(), "", "tb_cfg_if", tb_cfg_if);

    if (!uvm_config_db#(ai_core_top_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg)) begin
      `uvm_error(get_type_name(), "Unable to find environment configuration object in the uvm_config_db");
    end

    /** Construct the analysis ports */
    item_observed_initiated_export       = new("item_observed_initiated_export", this);
    item_observed_initiated_export_ctrlr = new("item_observed_initiated_export_ctrlr", this);
    item_observed_response_export        = new("item_observed_response_export", this);
    actual_data_response_export_mvm      = new("actual_data_response_export_mvm", this);
    actual_data_response_export_dwpu     = new("actual_data_response_export_dwpu", this);
    actual_data_response_export_dpu_0    = new("actual_data_response_export_dpu_0", this);
    actual_data_response_export_dpu_1    = new("actual_data_response_export_dpu_1", this);
    actual_data_response_export_ls_lp    = new("actual_data_response_export_ls_lp", this);
    actual_data_response_export_ls_hp    = new("actual_data_response_export_ls_hp", this);
    actual_data_response_export_noc_hp   = new("actual_data_response_export_noc_hp", this);

    l2_rsrvd_lp_noc_min  = 36'ha00_0000         ;
    l2_rsrvd_lp_noc_max  = 36'hfff_ffff         ;

  endfunction

  /** This method is called by item_observed_initiated_export */
  // NOC transactions
  virtual function void write_initiated(input svt_axi_transaction xact);
    svt_axi_transaction init_xact;
    bit cid_1_vld_noc,cid_2_vld_noc,cid_3_vld_noc,cid_4_vld_noc;

    if (!$cast(init_xact, xact.clone())) begin
      `uvm_fatal("Write_initiated", "Unable to $cast the received transaction to svt_axi_transaction");
    end

    if($cast(reg_xact, xact)) begin
      `uvm_info("SB_exp_DATA", $sformatf("incoming packet is reg trabsation and hence discarded...."), UVM_LOW)
    end else begin
      `uvm_info("Write_initiated", $sformatf("xact:\n%s", init_xact.sprint()), UVM_HIGH)
      `uvm_info("Write_initiated", $sformatf("SCB:: Pkt recived from mst-0"), UVM_LOW)
      // init_xact.print();

      decerr_chk(init_xact.addr,vld_addr_decerr);

      if(vld_addr_decerr==1) begin
        if(
          (init_xact.addr >= `L2_BANK0_MEM_START_ADDR     && init_xact.addr <=  `L2_BANK3_MEM_END_ADDR    ) || // 0800_0000 to 09FF_FFFF
          (init_xact.addr >= `AI_CORE_M_IFD0_START_ADDR   && init_xact.addr <=  `AI_CORE_TRACE_END_ADDR   ) || // X001_0000 to X008_FFFF
          (init_xact.addr >= `AI_CORE_M_MVMEXE_START_ADDR && init_xact.addr <=  `AI_CORE_M_MVMPRG_END_ADDR) || // X009_0000 to X00A_FFFF
          (init_xact.addr >= `AI_CORE_M_IAU_START_ADDR    && init_xact.addr <=  `AI_CORE_M_DPU_END_ADDR   ) || // X00B_0000 to X00C_FFFF
          (init_xact.addr >= `AI_CORE_D_DWPU_START_ADDR   && init_xact.addr <=  `AI_CORE_D_DWPU_END_ADDR  ) || // X00D_0000 to X00D_FFFF
          (init_xact.addr >= `AI_CORE_D_IAU_START_ADDR    && init_xact.addr <=  `AI_CORE_D_DPU_END_ADDR   ) || // X00E_0000 to X00F_FFFF
          (init_xact.addr >= `AI_CORE_L1_MEM_START_ADDR   && init_xact.addr <=  `AI_CORE_L1_MEM_END_ADDR  ) || // X800_0000 to X83F_FFFF
          (init_xact.addr >= `DDR_MEM_START_ADDR          && init_xact.addr <=  `DDR_MEM_END_ADDR         ) || // 8000_0000 to FFFF_FFFF
          (init_xact.addr >= `DDR1_MEM_START_ADDR         && init_xact.addr <=  `DDR1_MEM_END_ADDR        )    // 8_8000_0000 to B_FFFF_FFFF
        ) begin
          `uvm_info("SB_exp_DATA", $sformatf("entering into compare function from noc master and addr is %0h",init_xact.addr), UVM_LOW)
          compare(xact);
          num_of_exp_pkts++;
        end else begin
          `uvm_info("SB_exp_DATA", $sformatf("wrong transaction address and addr : %0h",init_xact.addr ), UVM_LOW)
        end
      end else begin
        `uvm_info("SB_exp_DATA", $sformatf("wrong transaction address having reserved space and addr : %0h",init_xact.addr ), UVM_LOW)
      end
    end

  endfunction:write_initiated

  /** This method is called by item_observed_initiated_export_ctrlr */
  // RISC-V transactions
  virtual function void write_initiated_ctrlr(input svt_axi_transaction xact);
    svt_axi_transaction init_xact_ctrlr;
    if (!$cast(init_xact_ctrlr, xact.clone())) begin
      `uvm_fatal("Write_initiated", "Unable to $cast the received transaction to svt_axi_transaction");
    end

    if($cast(reg_xact, xact)) begin
      `uvm_info("SB_exp_DATA", $sformatf("incoming packet is reg trabsation and hence discarded...."), UVM_LOW)
    end else begin
      `uvm_info("Write_initiated", $sformatf("SCB:: Pkt recived from controller"), UVM_LOW)
      // init_xact_ctrlr.print();

      decerr_chk(init_xact_ctrlr.addr,vld_addr_decerr);

      if(vld_addr_decerr==1) begin

        `uvm_info("SB_exp_DATA", $sformatf("entering into compare function from ctrlr master and addr is %0h",init_xact_ctrlr.addr), UVM_LOW)

        addr_chk_exp(init_xact_ctrlr.addr,vld_addr);

        if(vld_addr==1) begin
          `uvm_info("SB_exp_DATA", $sformatf("entering into compare function from ctrlr master and addr is %0h",init_xact_ctrlr.addr), UVM_LOW)
          compare(xact);
          num_of_exp_pkts_ctrlr++;
        end else begin
          `uvm_info("SB_exp_DATA", $sformatf("wrong transaction address and addr : %0h",init_xact_ctrlr.addr ), UVM_LOW)
        end
      end else begin
        `uvm_info("SB_exp_DATA", $sformatf("wrong transaction address having reserved space and addr : %0h",init_xact_ctrlr.addr ), UVM_LOW)
      end

    end

  endfunction:write_initiated_ctrlr

  /** This method is called by item_observed_response_export */
  virtual function void write_response(input svt_axi_transaction xact);

    svt_axi_transaction resp_xact;
    if (!$cast(resp_xact, xact.clone())) begin
      `uvm_fatal("Write_response", "Unable to $cast the received transaction to svt_axi_transaction");
    end
    begin
      `uvm_info("Write_response", $sformatf("xact:\n%s", resp_xact.sprint()), UVM_HIGH)
      `uvm_info("L2SCOREBOARD", $sformatf("AXI_ADDR = %h", resp_xact.addr), UVM_HIGH)
      for (int ii = 0; ii < 15; ii++)
        `uvm_info("L2SCOREBOARD", $sformatf("AXI_DATA[%d] = %h", ii, resp_xact.data[ii]), UVM_HIGH)
    end

    num_of_act_pkts_noc_lp++;
    `uvm_info("SB_act_DATA", $sformatf("noc_lp slave actual packet received from scoreboard and addr is %0h ", xact.addr), UVM_LOW)
    // xact.print();
    act_xact_noc_lp.push_back(xact);
    `uvm_info(get_type_name(), "SCB:: noc_lp actual Pkt printed from mst-1", UVM_LOW);
  endfunction:write_response

  /** This method is called by actual_data_response_export_mvm */
  virtual function void write_actual_response_mvm(input svt_axi_transaction xact);

    int index = num_of_act_pkts_mvm;
    //if((xact.xact_type==svt_axi_transaction::WRITE && xact.bresp==svt_axi_transaction::OKAY ) || (xact.xact_type==svt_axi_transaction::READ && xact.rresp[0]==svt_axi_transaction::OKAY) ) begin
      num_of_act_pkts_mvm++;
      `uvm_info("SB_act_DATA", $sformatf("mvm actual packet received from scoreboard and addr is %0h ", xact.addr), UVM_LOW)
      // xact.print();
      act_xact_mvm.push_back(xact);
    //end
    `uvm_info(get_type_name(), "SCB:: mvm actual Pkt printed from mst-1", UVM_LOW);

  endfunction:write_actual_response_mvm

  /** This method is called by actual_data_response_export_dwpu */
  virtual function void write_actual_response_dwpu(input svt_axi_transaction xact);

    int index = num_of_act_pkts_dwpu;
    //if((xact.xact_type==svt_axi_transaction::WRITE && xact.bresp==svt_axi_transaction::OKAY ) || (xact.xact_type==svt_axi_transaction::READ && xact.rresp[0]==svt_axi_transaction::OKAY) ) begin
      num_of_act_pkts_dwpu++;
      `uvm_info("SB_act_DATA", $sformatf("dwpu actual packet received from scoreboard and addr is %0h ", xact.addr), UVM_LOW)
      // xact.print();
      act_xact_dwpu.push_back(xact);
    //end
    `uvm_info(get_type_name(), "SCB:: dwpu actual Pkt printed from mst-1", UVM_LOW);

  endfunction:write_actual_response_dwpu

  /** This method is called by actual_data_response_export_dpu_0 */
  virtual function void write_actual_response_dpu_0(input svt_axi_transaction xact);

    int index = num_of_act_pkts_dpu_0;
    //if((xact.xact_type==svt_axi_transaction::WRITE && xact.bresp==svt_axi_transaction::OKAY ) || (xact.xact_type==svt_axi_transaction::READ && xact.rresp[0]==svt_axi_transaction::OKAY) ) begin
      num_of_act_pkts_dpu_0++;
      `uvm_info("SB_act_DATA", $sformatf("dpu_0 actual packet received from scoreboard and addr is %0h ", xact.addr), UVM_LOW)
      // xact.print();
      act_xact_dpu_0.push_back(xact);
    //end
    `uvm_info(get_type_name(), "SCB:: dpu_0 actual Pkt printed from mst-1", UVM_LOW);

  endfunction:write_actual_response_dpu_0

  /** This method is called by actual_data_response_export_dpu_1 */
  virtual function void write_actual_response_dpu_1(input svt_axi_transaction xact);

    int index = num_of_act_pkts_dpu_1;
    //if((xact.xact_type==svt_axi_transaction::WRITE && xact.bresp==svt_axi_transaction::OKAY ) || (xact.xact_type==svt_axi_transaction::READ && xact.rresp[0]==svt_axi_transaction::OKAY) ) begin
      num_of_act_pkts_dpu_1++;
      `uvm_info("SB_act_DATA", $sformatf("dpu_1 actual packet received from scoreboard and addr is %0h ", xact.addr), UVM_LOW)
      // xact.print();
      act_xact_dpu_1.push_back(xact);
    //end
    `uvm_info(get_type_name(), "SCB:: dpu_1 actual Pkt printed from mst-1", UVM_LOW);

  endfunction:write_actual_response_dpu_1

  /** This method is called by actual_data_response_export_ls_lp */
  virtual function void write_actual_response_ls_lp(input svt_axi_transaction xact);

    int index = num_of_act_pkts_ls_lp;
    //if((xact.xact_type==svt_axi_transaction::WRITE && xact.bresp==svt_axi_transaction::OKAY ) || (xact.xact_type==svt_axi_transaction::READ && xact.rresp[0]==svt_axi_transaction::OKAY) ) begin
    num_of_act_pkts_ls_lp++;
      `uvm_info("SB_act_DATA", $sformatf("ls_lp actual packet received from scoreboard and addr is %0h ", xact.addr), UVM_LOW)
      // xact.print();
      act_xact_ls_lp.push_back(xact);
    //end
    `uvm_info(get_type_name(), "SCB:: ls_lp actual Pkt printed from mst-1", UVM_LOW);

  endfunction:write_actual_response_ls_lp

  /** This method is called by actual_data_response_export_ls_hp */
  virtual function void write_actual_response_ls_hp(input svt_axi_transaction xact);

    int index = num_of_act_pkts_ls_hp;
    //if((xact.xact_type==svt_axi_transaction::WRITE && xact.bresp==svt_axi_transaction::OKAY ) || (xact.xact_type==svt_axi_transaction::READ && xact.rresp[0]==svt_axi_transaction::OKAY) ) begin
      num_of_act_pkts_ls_hp++;
      `uvm_info("SB_act_DATA", $sformatf("ls_hp actual packet received from scoreboard and addr is %0h ", xact.addr), UVM_LOW)
      // xact.print();
      act_xact_ls_hp.push_back(xact);
    //end
    `uvm_info(get_type_name(), "SCB:: ls_hp actual Pkt printed from mst-1", UVM_LOW);

  endfunction:write_actual_response_ls_hp

  /** This method is called by actual_data_response_export_noc_hp */
  virtual function void write_actual_response_noc_hp(input svt_axi_transaction xact);

    int index = num_of_act_pkts_noc_hp;
    //if((xact.xact_type==svt_axi_transaction::WRITE && xact.bresp==svt_axi_transaction::OKAY ) || (xact.xact_type==svt_axi_transaction::READ && xact.rresp[0]==svt_axi_transaction::OKAY) ) begin
      num_of_act_pkts_noc_hp++;
      `uvm_info("SB_act_DATA", $sformatf("no_hp actual packet received from scoreboard and addr is %0h ", xact.addr), UVM_LOW)
      // xact.print();
      act_xact_noc_hp.push_back(xact);
    //end
    `uvm_info(get_type_name(), "SCB:: noc_hp actual Pkt printed from mst-1", UVM_LOW);

  endfunction:write_actual_response_noc_hp


  task run_phase(uvm_phase phase);
    int l2_mode;
    int iter_cnt;

    //super.run_phase();
    // Get L2 operating parameters
    get_l2_oper_params(l2_mode, iter_cnt);
  endtask:run_phase

  // Get L2 operating Parameters
  function void get_l2_oper_params (output int l2_mode, output int iter_cnt);
    uvm_config_db#(uvm_bitstream_t)::get(null,"*","L2_Mode",l2_mode);
    uvm_config_db#(uvm_bitstream_t)::get(null,"*","ITER_CNT",iter_cnt);
    `uvm_info("Get-Op: L2SCOREBOARD", $sformatf("l2 Mode = %d Iteration Count = %d", l2_mode, iter_cnt), UVM_HIGH)
  endfunction:get_l2_oper_params

  function void compare(input svt_axi_transaction  tx_pkt);
    `uvm_info("SCOREBOARD","Entered into compare logic",UVM_LOW)
    addr_tmp = tx_pkt.addr;
    `uvm_info("SCOREBOARD",$sformatf("addr coming into compare function is %0h", addr_tmp), UVM_LOW)

    addr_decode(addr_tmp);

    `uvm_info("SCOREBOARD",$sformatf("address decoding completed "), UVM_LOW)

    begin
      if(tx_pkt.addr[27:0]==rx_pkt.addr[27:0]) begin // && tx_pkt.data[0]==rx_pkt.data[0] ) begin
        dt_size=tx_pkt.data.size();
        for (int i=0; i<=dt_size; i++) begin

          if( (tx_pkt.addr == (`AI_CORE_M_IFD0_END_ADDR   - 8'h7)) || (tx_pkt.addr == (`AI_CORE_M_IFD0_DESC_MEM_END_ADDR    - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_M_IFD1_END_ADDR   - 8'h7)) || (tx_pkt.addr == (`AI_CORE_M_IFD1_DESC_MEM_END_ADDR    - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_M_IFDW_END_ADDR   - 8'h7)) || (tx_pkt.addr == (`AI_CORE_M_IFDW_DESC_MEM_END_ADDR    - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_M_ODR_END_ADDR    - 8'h7)) || (tx_pkt.addr == (`AI_CORE_M_ODR_DESC_MEM_END_ADDR     - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_D_IFD0_END_ADDR   - 8'h7)) || (tx_pkt.addr == (`AI_CORE_D_IFD0_DESC_MEM_END_ADDR    - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_D_IFD1_END_ADDR   - 8'h7)) || (tx_pkt.addr == (`AI_CORE_D_IFD1_DESC_MEM_END_ADDR    - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_D_ODR_END_ADDR    - 8'h7)) || (tx_pkt.addr == (`AI_CORE_D_ODR_DESC_MEM_END_ADDR     - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_TOKEN_END_ADDR    - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_TRACE_END_ADDR    - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_M_MVMEXE_END_ADDR - 8'h7)) || (tx_pkt.addr == (`AI_CORE_M_MVMEXE_DESC_MEM_END_ADDR  - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_M_MVMPRG_END_ADDR - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_M_IAU_END_ADDR    - 8'h7)) || (tx_pkt.addr == (`AI_CORE_M_IAU_DESC_MEM_END_ADDR     - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_M_DPU_END_ADDR    - 8'h7)) || (tx_pkt.addr == (`AI_CORE_M_DPU_DESC_MEM_END_ADDR     - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_D_DWPU_END_ADDR   - 8'h7)) || (tx_pkt.addr == (`AI_CORE_D_DWPU_DESC_MEM_END_ADDR    - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_D_IAU_END_ADDR    - 8'h7)) || (tx_pkt.addr == (`AI_CORE_D_IAU_DESC_MEM_END_ADDR     - 8'h7)) ||
              (tx_pkt.addr == (`AI_CORE_D_DPU_END_ADDR    - 8'h7)) || (tx_pkt.addr == (`AI_CORE_D_DPU_DESC_MEM_END_ADDR     - 8'h7))
          ) begin
            `uvm_info("SCOREBOARD",$sformatf("entered in if part for failing address" ), UVM_LOW)

            if(tx_pkt.physical_data[i]==rx_pkt.physical_data[i][63:0]) begin
              `uvm_info("SCOREBOARD",$sformatf("data Comparison Successfully of both packet in write part : tx_pkt.physical_data[%0d] is %0h and rx_pkt.physical_data[%0d] is %0h and tx_addr is %0h and rx_addr is %0h", i, tx_pkt.physical_data[i], i, rx_pkt.physical_data[i][63:0], tx_pkt.addr[27:0],rx_pkt.addr[27:0] ), UVM_LOW)
            end else begin
              `uvm_error("SCOREBOARD",$sformatf("data got mismatch & scoreboarding failed: tx_pkt.physical_data[%0d] is %0h and rx_pkt.physical_data[%0d] is %h and tx_addr is %0h and rx_addr is %0h", i, tx_pkt.physical_data[i], i, rx_pkt.physical_data[i][63:0], tx_pkt.addr[27:0],rx_pkt.addr[27:0] ))
            end

          end else begin
            //begin
            //temporary changing the data as slave
            //side unable to observe wstrb and data at
            // slave end but physical data is getting
            // updated
            if(tx_pkt.data[i]==rx_pkt.data[i][63:0]) begin
              `uvm_info("SCOREBOARD",$sformatf("data Comparison Successfully of both packet in write part : tx_pkt.data[%0d] is %0h and rx_pkt.data[%0d] is %0h and tx_addr is %0h and rx_addr is %0h", i, tx_pkt.data[i], i, rx_pkt.data[i][63:0], tx_pkt.addr[27:0],rx_pkt.addr[27:0] ), UVM_LOW)
            end else begin
              `uvm_error("SCOREBOARD",$sformatf("data got mismatch & scoreboarding failed: tx_pkt.data[%0d] is %0h and rx_pkt.data[%0d] is %h and tx_addr is %0h and rx_addr is %0h", i, tx_pkt.data[i], i, rx_pkt.data[i][63:0], tx_pkt.addr[27:0],rx_pkt.addr[27:0] ))
            end
          end
        end

        `uvm_info(get_type_name(), "addr and data got match", UVM_LOW);
        `uvm_info("SCOREBOARD","Comparison Successfully of both packet in write part",UVM_LOW)
        write_pkt_success++;
      end else begin
        `uvm_info(get_type_name(), "addr mismatch and scoreboading failed", UVM_LOW);
        `uvm_error("SCOREBOARD","Comparison failure of packet in write operation")
        write_pkt_failure++;
      end
    end

  endfunction:compare

  function addr_decode (input bit [36-1:0] addr);
    addr_dec_cid=tb_cfg_if.cid;
    `uvm_info("SCOREBOARD",$sformatf("Entered into address decode function and addr coming into address decode function is %0h", addr), UVM_LOW)

    if(addr >= `AI_CORE_M_MVMEXE_START_ADDR && addr <= `AI_CORE_M_MVMPRG_END_ADDR) begin // X009_0000 to X00A_FFFF
      `uvm_info("SB_exp_DATA", $sformatf("size of queue before popping actual transaction lp_1 pkt is %0d and addr is %0h", act_xact_mvm.size(), addr), UVM_LOW)
      if(act_xact_mvm.size()>1) begin
        for(int i=0 ; i<act_xact_mvm.size(); i++) begin
          `uvm_info("SCOREBOARD",$sformatf("lp slave 1 tx_addr[27:0] : %0d and  packet inside for loop act_xact_mvm(%0d) addr is %0h ",addr[27:0], i, act_xact_mvm[i].addr ), UVM_LOW)
          if(addr[27:0]==act_xact_mvm[i].addr[27:0]) begin
            `uvm_info(get_type_name(), "entered into if loop....", UVM_LOW);
            rx_pkt=act_xact_mvm[i];
            act_xact_mvm.delete(i);
          end
        end
      end
      else begin rx_pkt=act_xact_mvm.pop_front(); end

      `uvm_info("SCOREBOARD",$sformatf("mvm slave packet got popped "), UVM_LOW)
    end

    else
    if(addr >= `AI_CORE_D_DWPU_START_ADDR && addr <= `AI_CORE_D_DWPU_END_ADDR) begin // X00D_0000 to X00D_FFFF
      `uvm_info("SB_exp_DATA", $sformatf("size of queue before popping actual transaction lp_2 pkt is %0d and addr is %0h", act_xact_dwpu.size(), addr), UVM_LOW)
      if(act_xact_dwpu.size()>1) begin
        for(int i=0 ; i<act_xact_dwpu.size(); i++) begin
          `uvm_info("SCOREBOARD",$sformatf("lp slave 2 tx_addr[27:0] : %0d and  packet inside for loop act_xact_dwpu(%0d) addr is %0h ",addr[27:0], i, act_xact_dwpu[i].addr ), UVM_LOW)
          if(addr[27:0]==act_xact_dwpu[i].addr[27:0]) begin
            `uvm_info(get_type_name(), "entered into if loop....", UVM_LOW);
            rx_pkt=act_xact_dwpu[i];
            act_xact_dwpu.delete(i);
          end
        end
      end
      else begin rx_pkt=act_xact_dwpu.pop_front(); end

      `uvm_info("SCOREBOARD",$sformatf("dwpu slave packet got popped "), UVM_LOW)
    end

    else
    if(addr >= `AI_CORE_M_IAU_START_ADDR && addr <= `AI_CORE_M_DPU_END_ADDR) begin // X00B_0000 to X00C_FFFF
      `uvm_info("SB_exp_DATA", $sformatf("size of queue before popping actual transaction lp_3 pkt is %0d and addr is %0h", act_xact_dpu_0.size(), addr), UVM_LOW)
      if(act_xact_dpu_0.size()>1) begin
        for(int i=0 ; i<act_xact_dpu_0.size(); i++) begin
          `uvm_info("SCOREBOARD",$sformatf("lp slave 3 tx_addr[27:0] : %0d and  packet inside for loop act_xact_dpu_0(%0d) addr is %0h ",addr[27:0], i, act_xact_dpu_0[i].addr ), UVM_LOW)
          if(addr[27:0]==act_xact_dpu_0[i].addr[27:0]) begin
            `uvm_info(get_type_name(), "entered into if loop....", UVM_LOW);
            rx_pkt=act_xact_dpu_0[i];
            act_xact_dpu_0.delete(i);
          end
        end
      end
      else begin rx_pkt=act_xact_dpu_0.pop_front(); end
      `uvm_info("SCOREBOARD",$sformatf("dpu_0 slave packet got popped "), UVM_LOW)
    end

    else
    if(addr >= `AI_CORE_D_IAU_START_ADDR && addr <= `AI_CORE_D_DPU_END_ADDR) begin // X00E_0000 to X00F_FFFF
      `uvm_info("SB_exp_DATA", $sformatf("size of queue before popping actual transaction lp_4 pkt is %0d and addr is %0h", act_xact_dpu_1.size(), addr), UVM_LOW)
      if(act_xact_dpu_1.size()>1) begin
        for(int i=0 ; i<act_xact_dpu_1.size(); i++) begin
          `uvm_info("SCOREBOARD",$sformatf("lp slave 4 tx_addr[27:0] : %0d and  packet inside for loop act_xact_dpu_1(%0d) addr is %0h ",addr[27:0], i, act_xact_dpu_1[i].addr ), UVM_LOW)
          if(addr[27:0]==act_xact_dpu_1[i].addr[27:0]) begin
            `uvm_info(get_type_name(), "entered into if loop....", UVM_LOW);
            rx_pkt=act_xact_dpu_1[i];
            act_xact_dpu_1.delete(i);
          end
        end
      end
      else begin rx_pkt=act_xact_dpu_1.pop_front(); end

      `uvm_info("SCOREBOARD",$sformatf("dpu_1 slave packet got popped "), UVM_LOW)
    end

    else
    if(addr >= `AI_CORE_M_IFD0_START_ADDR && addr <= `AI_CORE_TRACE_END_ADDR) begin // X001_0000 to X008_FFFF
      `uvm_info("SB_exp_DATA", $sformatf("size of queue before popping actual transaction lp_5 pkt is %0d and addr is %0h ", act_xact_ls_lp.size(), addr), UVM_LOW)
      if(act_xact_ls_lp.size()>1) begin
        for(int i=0 ; i<act_xact_ls_lp.size(); i++) begin
          `uvm_info("SCOREBOARD",$sformatf("lp slave 5 tx_addr[27:0] : %0d and  packet inside for loop act_xact_ls_lp(%0d) addr is %0h ",addr[27:0], i, act_xact_ls_lp[i].addr ), UVM_LOW)
          if(addr[27:0]==act_xact_ls_lp[i].addr[27:0]) begin
            `uvm_info(get_type_name(), "entered into if loop....", UVM_LOW);
            rx_pkt=act_xact_ls_lp[i];
            act_xact_ls_lp.delete(i);
          end
        end
      end
      else begin rx_pkt=act_xact_ls_lp.pop_front(); end
      `uvm_info("SCOREBOARD",$sformatf("ls_lp slave packet got popped and popped pkt addr is %0h ",rx_pkt.addr ), UVM_LOW)
    end

    else
    if( (addr >= `DDR_MEM_START_ADDR      && addr <= `DDR_MEM_END_ADDR      ) ||  // 8000_0000 to FFFF_FFFF
        (addr >= `DDR1_MEM_START_ADDR     && addr <= `DDR1_MEM_END_ADDR     ) ||  // 8_8000_0000 to B_FFFF_FFFF
        (addr >= `L2_BANK0_MEM_START_ADDR && addr <= `L2_BANK3_MEM_END_ADDR )     // 0800_0000 to 09FF_FFFF
    ) begin
      `uvm_info("SB_exp_DATA", $sformatf("size of queue before popping actual transaction hp_0 pkt is %0d and addr is %0h", act_xact_noc_hp.size(), addr), UVM_LOW)
      if(act_xact_noc_hp.size()>1) begin
        for(int i=0 ; i<act_xact_noc_hp.size(); i++) begin
          `uvm_info("SCOREBOARD",$sformatf("noc_hp slave tx_addr[27:0] : %0d and  packet inside for loop act_xact_noc_hp(%0d) addr is %0h ",addr[27:0], i, act_xact_noc_hp[i].addr ), UVM_LOW)
          if(addr[27:0]==act_xact_noc_hp[i].addr[27:0]) begin
            `uvm_info(get_type_name(), "entered into if loop....", UVM_LOW);
            rx_pkt=act_xact_noc_hp[i];
            act_xact_noc_hp.delete(i);
          end
        end
      end
      else begin rx_pkt=act_xact_noc_hp.pop_front(); end
      `uvm_info("SCOREBOARD",$sformatf("noc_hp slave packet got popped "), UVM_LOW)
    end


    else
    if(addr >= `AI_CORE_L1_MEM_START_ADDR && addr <= `AI_CORE_L1_MEM_END_ADDR) begin // X800_0000 to X83F_FFFF
      `uvm_info("SB_exp_DATA", $sformatf("size of queue before popping actual transaction ls_hp pkt is %0d and addr is %0h", act_xact_ls_hp.size(), addr), UVM_LOW)
      if(act_xact_ls_hp.size()>1) begin
        for(int i=0 ; i<act_xact_ls_hp.size(); i++) begin
          `uvm_info("SCOREBOARD",$sformatf("act_xact_ls_hp tx_addr[27:0] : %0d and  packet inside for loop act_xact_ls_hp(%0d) addr is %0h ",addr[27:0], i, act_xact_ls_hp[i].addr ), UVM_LOW)
          if(addr[27:0]==act_xact_ls_hp[i].addr[27:0]) begin
            `uvm_info(get_type_name(), "entered into if loop....", UVM_LOW);
            rx_pkt=act_xact_ls_hp[i];
            act_xact_ls_hp.delete(i);
          end
        end
      end
      else begin rx_pkt=act_xact_ls_hp.pop_front(); end
      `uvm_info("SCOREBOARD",$sformatf("ls_hp slave  packet got popped "), UVM_LOW)
    end

    else if(addr < 'h07ff_ffff ||
    (addr >= 'h5000_0000 && addr < 'h7fff_ffff) ||
    (addr_dec_cid==1 && addr > 'h1fff_ffff) ||
    (addr_dec_cid==2 && (addr > 'h2fff_ffff || addr < 'h2000_0000) ) ||
    (addr_dec_cid==3 && (addr > 'h3fff_ffff || addr < 'h3000_0000)) ||
    (addr_dec_cid==4 && (addr < 'h4000_0000 || addr > 'h7fff_ffff )) ||
    (addr >= l2_rsrvd_lp_noc_min && addr < l2_rsrvd_lp_noc_max) ) begin
      `uvm_info("SB_exp_DATA", $sformatf("size of queue before popping actual transaction act_xact_noc_lp pkt is %0d and addr is %0h", act_xact_noc_lp.size(),addr ), UVM_LOW)
        if(act_xact_noc_lp.size()>1) begin
        for(int i=0 ; i<act_xact_noc_lp.size(); i++) begin
          `uvm_info("SCOREBOARD",$sformatf("act_xact_noc_lp tx_addr[27:0] : %0d and  packet inside for loop act_xact_lp_0(%0d) addr is %0h ",addr[27:0], i, act_xact_noc_lp[i].addr ), UVM_LOW)
          if(addr[27:0]==act_xact_noc_lp[i].addr[27:0]) begin
            `uvm_info(get_type_name(), "entered into if loop....", UVM_LOW);
            rx_pkt=act_xact_noc_lp[i];
            act_xact_noc_lp.delete(i);
          end
        end
      end
      else begin rx_pkt=act_xact_noc_lp.pop_front(); end

    end else begin
      `uvm_info(get_type_name(), $sformatf("No matching adress range...."), UVM_LOW);
    end

  endfunction


  function addr_chk_exp(input bit [36-1] addr, output bit vld_addr);

    //TODO
    // currently discarded 'hA00_0000 address
    //from HP_NOC range as it is giving decerror
    // to be fixed in omega

    if(
      (addr <  `AI_CORE_MAILBOX_START_ADDR                                        ) ||  // less than X000_0000
      (addr >= `AI_CORE_M_IFD0_START_ADDR   && addr <= `AI_CORE_TRACE_END_ADDR    ) ||  // X001_0000 to X008_FFFF
      (addr >= `AI_CORE_M_MVMEXE_START_ADDR && addr <= `AI_CORE_M_MVMPRG_END_ADDR ) ||  // X009_0000 to X00A_FFFF
      (addr >= `AI_CORE_M_IAU_START_ADDR    && addr <= `AI_CORE_M_DPU_END_ADDR    ) ||  // X00B_0000 to X00C_FFFF
      (addr >= `AI_CORE_D_DWPU_START_ADDR   && addr <= `AI_CORE_D_DWPU_END_ADDR   ) ||  // X00D_0000 to X00D_FFFF
      (addr >= `AI_CORE_D_IAU_START_ADDR    && addr <= `AI_CORE_D_DPU_END_ADDR    ) ||  // X00E_0000 to X00F_FFFF
      (addr >= `AI_CORE_L1_MEM_START_ADDR   && addr <= `AI_CORE_L1_MEM_END_ADDR   ) ||  // X800_0000 to X83F_FFFF
      (addr >  `AI_CORE_RESERVED_AI_CORE_MEM_END_ADDR                             )     // more that XFFF_FFFF
    ) begin
      vld_addr = 1;
    end else begin
      vld_addr = 0;
      `uvm_info(get_type_name(), $sformatf("value of vld_addr coming from last else part is %0b",vld_addr) , UVM_LOW);
    end

  endfunction

  //decerr_chk
  function decerr_chk(input bit [37-1:0] addr,  output bit vld_addr_decerr);

    //TODO -> Done
    // currently discarded 'hA00_0000 address
    //from HP_NOC range as it is giving decerror
    //to be fixed in omega
    //Also reserved range needs to be fixed
    //in omega
    // pcie//ddr range is also discarded
    //needs to be fixed in omega

    //issue 822 got solved now and
    // rsrv range also got fixed in omega

    if( (addr >= `AI_CORE_RESERVED1_START_ADDR            && addr <= `AI_CORE_RESERVED1_END_ADDR            ) ||  // X012_0000 to X021_FFFF
        (addr >= `AI_CORE_RESERVED2_START_ADDR            && addr <= `AI_CORE_RESERVED2_END_ADDR            ) ||  // X024_0000 to X03F_FFFF
        (addr >= `AI_CORE_RESERVED_ILM_MEM_START_ADDR     && addr <= `AI_CORE_RESERVED_ILM_MEM_END_ADDR     ) ||  // X080_0000 to X083_FFFF
        (addr >= `AI_CORE_RESERVED_DLM_MEM_START_ADDR     && addr <= `AI_CORE_RESERVED_DLM_MEM_END_ADDR     ) ||  // X086_0000 to X08F_FFFF
        (addr >= `AI_CORE_RESERVED_SPM_MEM_START_ADDR     && addr <= `AI_CORE_RESERVED_SPM_MEM_END_ADDR     ) ||  // X091_0000 to X7FF_FFFF
        (addr >= `AI_CORE_RESERVED_AI_CORE_MEM_START_ADDR && addr <= `AI_CORE_RESERVED_AI_CORE_MEM_END_ADDR )     // X840_0000 to XFFF_FFFF
    ) begin
      vld_addr_decerr = 0;
      `uvm_info(get_type_name(), $sformatf("value of dec_err is %0b",vld_addr_decerr) , UVM_LOW);
    end else begin
      vld_addr_decerr=1;
      `uvm_info(get_type_name(), $sformatf("value of dec_err from last else  loop is %0b",vld_addr_decerr) , UVM_LOW);
    end

  endfunction


  function void check_phase(uvm_phase phase);
    int tot_act_pkt, tot_exp_pkt;
    tot_act_pkt = num_of_act_pkts_noc_lp + num_of_act_pkts_mvm + num_of_act_pkts_dwpu + num_of_act_pkts_dpu_0 + num_of_act_pkts_dpu_1 + num_of_act_pkts_ls_lp + num_of_act_pkts_ls_hp + num_of_act_pkts_noc_hp;
    tot_exp_pkt = num_of_exp_pkts + num_of_exp_pkts_ctrlr ;

    //if(tot_act_pkt != (tot_exp_pkt-10))
    if(tot_act_pkt != (tot_exp_pkt)) begin
      `uvm_error("SB_CHECK", $sformatf("num_of_act_pkts=%0d,num_of_exp_pkts=%0d",tot_act_pkt, tot_exp_pkt))
    end else
      `uvm_info("SB_CHECK", $sformatf("num_of_act_pkts=%0d,num_of_exp_pkts=%0d",tot_act_pkt,tot_exp_pkt), UVM_LOW)


  endfunction

endclass // axi_uvm_scoreboard


