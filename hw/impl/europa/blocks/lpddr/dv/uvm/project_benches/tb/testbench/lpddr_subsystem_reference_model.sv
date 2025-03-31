//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_reference_model.sv
// Unit        : lpddr_subsystem_reference_model
//------------------------------------------------------------------------------
// Description : This is 
//------------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_REFERENCE_MODEL_SV
`define LPDDR_SUBSYSTEM_REFERENCE_MODEL_SV

`uvm_analysis_imp_decl(_from_axi)

//---------------------------------------------------------------------------
// Class          : lpddr_subsystem_reference_model
// Parent         : uvm_subscriber
//---------------------------------------------------------------------------
class lpddr_subsystem_reference_model extends uvm_subscriber#(amem_command_class);

  //typedef for lpddr_subsystem_reference_model
  typedef lpddr_subsystem_reference_model this_type;
  
  //-------------------------------------------------------------
  // Local parameter Declaration
  //-------------------------------------------------------------
  axi_trans_t m_axi_read_blue_q [$];
  axi_trans_t m_axi_read_red_q [$];
  axi_trans_t m_axi_write_q [$];

  int red_queue_timeout, blue_queue_timeout, write_queue_timeout_region_0_1, write_queue_timeout_region_2;

  //Queue in arbiter
  axi_trans_t m_arbiter_read_write_q [$];

  //TODO: replace the transaction type with CAM queue
  axi_trans_t m_exp_q [$];
  bit [1:0] mstr0_data_bus_width;
  bit [4:0] raa_counter[];
  int rfshset1tmg1_t_rfc_min, rfshsrt1tmg0_refresh_to_x1_x32, rfshmod0_auto_refab_en, derateint_mr4_read_interval, dramset1tmg14_t_osco;
  bit derateen_derate_enable, deratectl5_derate_temp_limit_intr_en;
  bit dbictl_dm_en, pwrctl_selfref_en, pwrctl_selfref_sw, dfiphymstr_dfi_phymstr_en, hwlpctl_hw_lp_en;
  bit per_bank_refresh_arr [$];
  bit all_bank_refresh_arr [$];
  int per_bank_refresh = 65;
  int all_bank_refresh = 9;

  bit [4:0] rfmmod0_raaimt;
  bit [7:0] local_pageclose_timer;
  bit [9:0] port_aging_blue_read_counter;
  bit [9:0] port_aging_red_read_counter;
  bit [9:0] port_aging_write_counter;
  bit axi_error_trans;
  bit red_read_pagematch_en, blue_read_pagematch_en, write_pagematch_en;
  bit red_read_port_pagematch_release, blue_read_port_pagematch_release, write_port_pagematch_release;
  int red_read_pop_counter, blue_read_pop_counter, write_pop_counter;

  bit[40:0] hif_cmd_addr;
  
  //TODO: assign below signal through System reset and remove below line
  bit reset_assertion;

  event received_lpddr_trans;
  event received_axi_trans;
  event trans_written_to_queue;
  event trans_written_to_write_queue;

  longint ddr_bytes;

  write_combine_state_e current_write_combine_state;
  write_combine_state_e next_write_combine_state;

  //Transaction Handle Declaration
  axi_trans_t axi_trans;
  apb3_host_apb3_transaction apb_trans;
  amem_command_class lpddr_trans;
  //transaction to be written on port connecting to scoreboard
  amem_command_class lpddr_exp_trans;

  //Virtual Interface
  virtual subsystem_signal_intf top_signals_intf;

  //To send expected transaction to lpddr_subsystem_scoreboard
  uvm_analysis_port #(amem_command_class) exp_lpddr_port;

	// Declar ports to get data from Monitor 
	uvm_analysis_imp_from_axi#(mvc_sequence_item_base, this_type) axi_analysis_port;

  // ------------------------------------------------------------------------
  // Register fault management component with the factory.
  // ------------------------------------------------------------------------
  `uvm_component_param_utils(this_type)

  //-------------------------------------------------------------------------
  // Function       : new
  // Arguments      : string name - Name of the object.
  //                  uvm_component parent
  // Description    : Constructor for fpga base scoreboard class objects.
  //-------------------------------------------------------------------------
  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);

    //Creating all required ports
	  axi_analysis_port = new("axi_analysis_port", this);
    exp_lpddr_port = new("exp_lpddr_port", this);

    //Count banks as per data_bus_width
    if (mstr0_data_bus_width == 2'b00) begin
      raa_counter = new[64];
    end
    else if (mstr0_data_bus_width == 2'b01) begin
      raa_counter = new[32];
    end

    if(!uvm_config_db#(virtual subsystem_signal_intf)::get(null,"UVMF_VIRTUAL_INTERFACES","top_signals_intf",top_signals_intf)) begin
      `uvm_error("Config Error","uvm_config_db #(subsystem_signal_intf)::get cannot find resource 'subsystem_signals'")
  	end
  endfunction : new

  //--------------------------------------------------------------------------
  // Function       : build_phase
  // Arguments      : uvm_phase phase - Handle of uvm_phase.
  // Description    : This phase create all the required objects.
  //--------------------------------------------------------------------------
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    axi_trans  = axi_trans_t::type_id::create("axi_trans");
  endfunction : build_phase

  //--------------------------------------------------------------------------
  // Function       : connect_phase
  // Arguments      : uvm_phase phase - Handle of uvm_phase.
  // Description    : This phase create all the required objects.
  //--------------------------------------------------------------------------
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction : connect_phase

  //-------------------------------------------------------------------------
  // Task           : run_phase
  // Arguments      : uvm_phase phase  - Handle of uvm_phase.
  // Description    : In this phase the TB execution starts
  //-------------------------------------------------------------------------
  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    forever begin
      fork begin
        fork
          default_value_on_reset();
          detect_input_trans_errors();
          get_axi_addr_trans();
          port_arbitration();
          application_to_hif_address_map();
          // hif_to_sdram_address_map();
          bank_hashing();
          // rmw_generation_bypass();
          axi_to_ddr_data_width_conversion();
          page_policy_explicit_autoprecharge_intelligent_precharge();
          address_collision_write_combine();
          direct_software_refresh_or_auto_refresh();
          automatic_temperature_derating();
          zq_calibration();
          mrr_snooping();
          mode_reg_read_write();
          data_bus_inversion();
          precharge_power_down_mode();
          self_refresh_mode();
          deep_sleep_mode();
          dfi_dram_clk_disable();
        join_any
        disable fork;
      end join
    end
  endtask : run_phase
  
  //-----------------------------------------------------------------------------
  // Name        : default_value_on_reset
  // Argument    : None
  // Description : This method resets local signals on reset assertion.
  //-----------------------------------------------------------------------------
  task default_value_on_reset();
    // TODO : need to provide relevant reset signal
    forever @(reset_assertion) begin
      //Add List signals here to reset it's value
      local_pageclose_timer = 0;
      axi_error_trans = 0;
      port_aging_blue_read_counter = 'h1F;
      port_aging_red_read_counter = 'h1F;
      port_aging_write_counter = 'h1F;
      rfshset1tmg1_t_rfc_min = 'h8C;
      rfshsrt1tmg0_refresh_to_x1_x32 = 'h10;
      derateint_mr4_read_interval = 'h800000;
      deratectl5_derate_temp_limit_intr_en = 1;
      rfmmod0_raaimt = 'd1;
      dramset1tmg14_t_osco = 'h8;
    end
  endtask : default_value_on_reset

  //-----------------------------------------------------------------------------
  // Name        : detect_input_trans_errors
  // Argument    : None
  // Description : This method detects error transaction and send response to
  //               AXI Scoreboard.
  //-----------------------------------------------------------------------------
  task detect_input_trans_errors();
    int addrmap12_nonbinary_device_density;
    fork
      forever@(received_axi_trans) begin
        //addrmap12_nonbinary_device_density = reg_read(ADDRMAP12, NONBINARY_DEVICE_DENSITY);
        if (addrmap12_nonbinary_device_density == 3'b000) begin
          axi_error_trans = 0;
        end
        else begin
          if (axi_trans.read_or_write == AXI4_TRANS_WRITE) begin
            axi_trans.resp[0] = AXI4_SLVERR;
          end
          else begin
            for (int i=0; i<axi_trans.burst_length; i++) begin
              axi_trans.resp[i] = AXI4_SLVERR;
            end
          end
          axi_error_trans = 1;
        end
      end
      forever @(axi_trans.addr_user_data[0]) begin
        if (axi_trans.addr_user_data[0] == 1) begin
          if (axi_trans.read_or_write == AXI4_TRANS_WRITE) begin
            axi_trans.resp[0] = AXI4_SLVERR;
          end
          else begin
            for (int i=0; i<axi_trans.burst_length; i++) begin
              axi_trans.resp[i] = AXI4_SLVERR;
            end
          end
          axi_error_trans = 1;
        end
        else begin
          axi_error_trans = 0;
        end
      end
      //TODO: Add link ECC error response here
      //forever begin
      //end
    join
  endtask : detect_input_trans_errors

  //-----------------------------------------------------------------------------
  // Name        : get_axi_read_trans
  // Argument    : None
  // Description : This method stores coming AXI transaction in different
  //               queues according to priority.
  //-----------------------------------------------------------------------------
  task get_axi_addr_trans();
    int pcfgqos0_rqos_map_region2, pcfgwqos0_wqos_map_region2;
    int pcfgqos1_rqos_map_timeoutb, pcfgqos1_rqos_map_timeoutr, pcfgwqos1_wqos_map_timeout1, pcfgwqos1_wqos_map_timeout2;
    fork
      forever@(pcfgqos1_rqos_map_timeoutr) begin
        red_queue_timeout = pcfgqos1_rqos_map_timeoutr;
      end
      forever@(pcfgqos1_rqos_map_timeoutb) begin
        blue_queue_timeout = pcfgqos1_rqos_map_timeoutb;
      end
      forever@(pcfgwqos1_wqos_map_timeout1) begin
        write_queue_timeout_region_0_1 = pcfgwqos1_wqos_map_timeout1;
      end
      forever@(pcfgwqos1_wqos_map_timeout2) begin
        write_queue_timeout_region_2 = pcfgwqos1_wqos_map_timeout2;
      end
      forever@(received_axi_trans) begin
        if (axi_error_trans == 0) begin
          //m_exp_fifo.get(axi_trans);
          if (axi_trans.read_or_write == AXI4_TRANS_READ) begin
            if (axi_trans.qos inside {0,13}) begin
              if (axi_trans.region == 0) begin
                //axi_trans.low_or_high_priority = AXI4_LPR_TRAFFIC;
                m_axi_read_blue_q.push_back(axi_trans);
                ->trans_written_to_queue;
              end
              else if (axi_trans.region == 1) begin
                //axi_trans.low_or_high_priority = AXI4_VPR_TRAFFIC;
                m_axi_read_blue_q.push_back(axi_trans);
                blue_queue_timeout = blue_queue_timeout - 1;
                ->trans_written_to_queue;
              end
            end
            else begin
              if (axi_trans.region == 2) begin
                if (pcfgqos0_rqos_map_region2 == 1) begin
                  //axi_trans.low_or_high_priority = AXI4_VPR_TRAFFIC;
                  m_axi_read_red_q.push_back(axi_trans);
                  red_queue_timeout = red_queue_timeout - 1;
                  ->trans_written_to_queue;
                end
                else if (pcfgqos0_rqos_map_region2 == 2) begin
                  //axi_trans.low_or_high_priority = AXI4_HPR_TRAFFIC;
                  m_axi_read_red_q.push_back(axi_trans);
                  ->trans_written_to_queue;
                end
              end
            end
          end
          else if (axi_trans.read_or_write == AXI4_TRANS_WRITE) begin
            if (axi_trans.qos inside {0,13}) begin
              if (axi_trans.region == 0) begin
                //axi_trans.normal_or_variable_priority = AXI4_NPW_TRAFFIC;
                m_axi_write_q.push_back(axi_trans);
                ->trans_written_to_queue;
              end
              else if (axi_trans.region == 1) begin
                //axi_trans.normal_or_variable_priority = AXI4_VPW_TRAFFIC;
                m_axi_write_q.push_back(axi_trans);
                write_queue_timeout_region_0_1 = write_queue_timeout_region_0_1 - 1;
                ->trans_written_to_queue;
              end
            end
            else begin
              if (axi_trans.region == 2) begin
                if (pcfgwqos0_wqos_map_region2 == 0) begin
                  //axi_trans.normal_or_variable_priority = AXI4_NPW_TRAFFIC;
                  m_axi_write_q.push_back(axi_trans);
                  ->trans_written_to_queue;
                end
                else if (pcfgwqos0_wqos_map_region2 == 1) begin
                  //axi_trans.normal_or_variable_priority = AXI4_VPW_TRAFFIC;
                  m_axi_write_q.push_back(axi_trans);
                  write_queue_timeout_region_2 = write_queue_timeout_region_2 - 1;
                  ->trans_written_to_queue;
                end
              end
            end
          end
        end
      end
    join
  endtask : get_axi_addr_trans

  //-----------------------------------------------------------------------------
  // Name        : port_arbitration
  // Argument    : None
  // Description : This method uses for port arbitration to choose data
  //               between different queues.
  //-----------------------------------------------------------------------------
  task port_arbitration();
    bit red_port_flag, blue_port_flag, write_port_flag;
    bit pcfgr_rd_port_urgent_en, pcfgw_wr_port_urgent_en;
    int pcfgr_rd_port_priority, pcfgw_wr_port_priority;
    bit pcfgr_red_rd_port_pagematch_en, pcfgr_blue_rd_port_pagematch_en, pcfgw_wr_port_pagematch_en, pccfg_pagematch_limit;
    //axi_trans.received_vpr_trans_timeout = 'h1;
    fork
      //forever begin
      //  pcfgr_rd_port_urgent_en = reg_read(PCFGR, RD_PORT_URGENT_EN);
      //  pcfgw_wr_port_urgent_en = reg_read(PCFGW, WR_PORT_URGENT_EN);
      //  pcfgr_rd_port_priority  = reg_read(PCFGR, RD_PORT_PRIORITY);
      //  pcfgw_wr_port_priority  = reg_read(PCFGW, WR_PORT_PRIORITY);
      //end
      forever@(pcfgr_rd_port_priority, pcfgw_wr_port_priority) begin
        port_aging_red_read_counter = pcfgr_rd_port_priority;
        port_aging_blue_read_counter = pcfgr_rd_port_priority;
        port_aging_write_counter = pcfgw_wr_port_priority;
      end
      forever@(trans_written_to_queue) begin
        if ((m_axi_read_red_q.size()>0) && (red_port_flag == 0)) begin
          port_aging_red_read_counter = port_aging_red_read_counter - 1;
        end
        else if ((m_axi_read_blue_q.size()>0) && (blue_port_flag == 0)) begin
          port_aging_blue_read_counter = port_aging_blue_read_counter - 1;
        end
        else if ((m_axi_write_q.size()>0) && (write_port_flag == 0)) begin
          port_aging_write_counter = port_aging_write_counter - 1;
        end
      end
      forever@(pcfgr_red_rd_port_pagematch_en, pcfgr_blue_rd_port_pagematch_en, pcfgw_wr_port_pagematch_en) begin
        if (pcfgr_red_rd_port_pagematch_en==1) begin
          red_read_pagematch_en = 1;
        end
        else if (pcfgr_blue_rd_port_pagematch_en==1) begin
          blue_read_pagematch_en = 1;
        end
        else if (pcfgw_wr_port_pagematch_en==1) begin
          write_pagematch_en = 1;
        end
      end
      forever@(port_aging_red_read_counter, port_aging_blue_read_counter, port_aging_write_counter) begin
        if (port_aging_red_read_counter==0) begin
          red_read_port_pagematch_release = 1;
        end
        else if (port_aging_blue_read_counter==0) begin
          blue_read_port_pagematch_release = 1;
        end
        else if (port_aging_write_counter==0) begin
          write_port_pagematch_release = 1;
        end
        else begin
          if (red_read_pagematch_en == 1) begin
            wait(m_axi_read_red_q.size()==0);
            red_read_port_pagematch_release = 1;
          end
          else if (blue_read_pagematch_en == 1) begin
            wait(m_axi_read_blue_q.size()==0);
            blue_read_port_pagematch_release = 1;
          end
          else if (write_pagematch_en == 1) begin
            wait(m_axi_write_q.size()==0);
            write_port_pagematch_release = 1;
          end
        end
      end
      forever@(red_read_pagematch_en) begin
        if ((m_axi_read_red_q.size()>0) && (red_read_pagematch_en == 1)) begin
          red_read_port_pagematch_release = 0;
          red_read_pop_counter = 0;
          if (pccfg_pagematch_limit == 1) begin
            if (red_read_pop_counter < 4) begin
              m_arbiter_read_write_q.push_back(m_axi_read_red_q.pop_front());
              red_read_pop_counter++;
            end
            else begin
              red_read_port_pagematch_release = 1;
              break;
            end
          end
          else begin
            foreach(m_axi_read_red_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_read_red_q.pop_front());
            end
          end
        end
      end
      forever@(blue_read_pagematch_en) begin
        if ((m_axi_read_blue_q.size()>0) && (blue_read_pagematch_en == 1)) begin
          blue_read_port_pagematch_release = 0;
          blue_read_pop_counter = 0;
          if (pccfg_pagematch_limit == 1) begin
            if (blue_read_pop_counter < 4) begin
              m_arbiter_read_write_q.push_back(m_axi_read_blue_q.pop_front());
              blue_read_pop_counter++;
            end
            else begin
              blue_read_port_pagematch_release = 1;
              break;
            end
          end
          else begin
            foreach(m_axi_read_blue_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_read_blue_q.pop_front());
            end
          end
        end
      end
      forever@(write_pagematch_en) begin
        if ((m_axi_write_q.size()>0) && (write_pagematch_en == 1)) begin
          write_port_pagematch_release = 0;
          write_pop_counter = 0;
          if (pccfg_pagematch_limit == 1) begin
            if (write_pop_counter < 4) begin
              m_arbiter_read_write_q.push_back(m_axi_write_q.pop_front());
              write_pop_counter++;
            end
            else begin
              write_port_pagematch_release = 1;
              break;
            end
          end
          else begin
            foreach(m_axi_write_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_write_q.pop_front());
            end
          end
        end
      end
      forever@(trans_written_to_queue) begin
        if (((red_read_pagematch_en==0) && (blue_read_pagematch_en==0) && (write_pagematch_en==0)) || (red_read_port_pagematch_release == 1) || (blue_read_port_pagematch_release == 1) || (write_port_pagematch_release == 1)) begin
          if ((m_axi_read_red_q.size()>0) && (pcfgr_rd_port_urgent_en == 1) && (top_signals_intf.arurgentr == 1)) begin
            foreach(m_axi_read_red_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_read_red_q.pop_front());
            end
            red_port_flag=1;
            blue_port_flag=0;
            write_port_flag=0;
          end
          else if ((m_axi_read_blue_q.size()>0) && (pcfgr_rd_port_urgent_en == 1) && (top_signals_intf.arurgentb == 1)) begin
            foreach(m_axi_read_blue_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_read_blue_q.pop_front());
            end
            red_port_flag=0;
            blue_port_flag=1;
            write_port_flag=0;
          end
          else if ((m_axi_write_q.size()>0) && (pcfgw_wr_port_urgent_en == 1) && (top_signals_intf.awurgent == 1)) begin
            foreach(m_axi_write_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_write_q.pop_front());
            end
            red_port_flag=0;
            blue_port_flag=0;
            write_port_flag=1;
          end
          else if (red_queue_timeout == 0) begin
            foreach(m_axi_read_red_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_read_red_q.pop_front());
            end
          end
          else if (blue_queue_timeout == 0) begin
            foreach(m_axi_read_blue_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_read_blue_q.pop_front());
            end
          end
          else if ((write_queue_timeout_region_2 == 0) || (write_queue_timeout_region_0_1 == 0)) begin
            foreach(m_axi_write_q[i]) begin
              m_arbiter_read_write_q.push_back(m_axi_write_q.pop_front());
            end
          end
          else begin
            if ((m_axi_read_red_q.size()>0) && (port_aging_red_read_counter == 0)) begin
              foreach(m_axi_read_red_q[i]) begin
                m_arbiter_read_write_q.push_back(m_axi_read_red_q.pop_front());
              end
              port_aging_red_read_counter = 'h1F;
              red_port_flag=1;
              blue_port_flag=0;
              write_port_flag=0;
            end
            else if ((m_axi_read_blue_q.size()>0) && (port_aging_blue_read_counter == 0)) begin
              foreach(m_axi_read_blue_q[i]) begin
                m_arbiter_read_write_q.push_back(m_axi_read_blue_q.pop_front());
              end
              port_aging_blue_read_counter = 'h1F;
              red_port_flag=0;
              blue_port_flag=1;
              write_port_flag=0;
            end
            else if ((m_axi_write_q.size()>0) && (port_aging_write_counter == 0)) begin
              foreach(m_axi_write_q[i]) begin
                m_arbiter_read_write_q.push_back(m_axi_write_q.pop_front());
              end
              port_aging_write_counter = 'h1F;
              red_port_flag=0;
              blue_port_flag=0;
              write_port_flag=1;
            end
          end
        end
      end
    join
  endtask : port_arbitration
  
  //-----------------------------------------------------------------------------
  // Name        : application_to_hif_address_map
  // Argument    : None
  // Description : This method converts Application (AXI) address to HIF address.
  //-----------------------------------------------------------------------------
  task application_to_hif_address_map();
    forever @(mstr0_data_bus_width) begin
      hif_cmd_addr[40:HIF_DOWN_1] = axi_trans.addr[UMCTL2_A_ADDRW_1:AXI_DOWN_1];
      //TODO: below bits are internally generated by XPI as per controller databook, need to know how
      hif_cmd_addr[($clog2(MEMC_BURST_LENGTH)-1):(MEMC_FREQ_RATIO-1)] = 1;
      hif_cmd_addr[(MEMC_FREQ_RATIO-2):0] = 0;
    end
  endtask : application_to_hif_address_map

  //-----------------------------------------------------------------------------
  // Name        : hif_to_sdram_address_map
  // Argument    : None
  // Description : This method converts HIF address to SDRAM Mapping.
  //-----------------------------------------------------------------------------
  task hif_to_sdram_address_map();
    //TODO: Make bank, rank, column and row address from this conversion
    //TODO: assign bank hashing bank group address to SDRAM if it is enable.
  endtask : hif_to_sdram_address_map

  //-----------------------------------------------------------------------------
  // Name        : bank_hashing
  // Argument    : None
  // Description : This method updates bank address if it is enable.
  //-----------------------------------------------------------------------------
  task bank_hashing();
    bit addrmap12_bank_hash_en;
    bit [3:0] am_bg_bank, bh_bg_bank;
    bit [17:0] am_row;
    forever@(addrmap12_bank_hash_en) begin
      if (addrmap12_bank_hash_en == 1) begin
        bh_bg_bank[0] = (am_bg_bank[0] ^ am_row[0] ^ am_row[4] ^ am_row[8] ^ am_row[12] ^ am_row[16]);
        bh_bg_bank[1] = (am_bg_bank[1] ^ am_row[1] ^ am_row[5] ^ am_row[9] ^ am_row[13] ^ am_row[17]);
        bh_bg_bank[2] = (am_bg_bank[2] ^ am_row[2] ^ am_row[6] ^ am_row[10] ^ am_row[14]);
        bh_bg_bank[3] = (am_bg_bank[3] ^ am_row[3] ^ am_row[7] ^ am_row[11] ^ am_row[15]);
      end
    end
  endtask : bank_hashing

  //-----------------------------------------------------------------------------
  // Name        : rmw_generation_bypass
  // Argument    : None
  // Description : This method generates RMWs and it's bypass logic.
  //-----------------------------------------------------------------------------
  task rmw_generation_bypass();
    bit[2:0] ecccfg0_ecc_mode;
    forever@(received_axi_trans) begin
      if ((ecccfg0_ecc_mode==3'b100) && (dbictl_dm_en==0)) begin
        //TODO: Complete this with ECC
      end
    end
  endtask : rmw_generation_bypass

  //-----------------------------------------------------------------------------
  // Name        : axi_to_ddr_data_width_conversion
  // Argument    : None
  // Description : This method converts AXI data width into DDR Data Width.
  //-----------------------------------------------------------------------------
  task axi_to_ddr_data_width_conversion();
    bit[4:0] mstr0_burst_rdwr;
    forever@(mstr0_burst_rdwr) begin
      ddr_bytes = (mstr0_burst_rdwr * 2 * MEMC_DRAM_DATA_WIDTH/8);
    end
    //TODO: DDRC provides axi_trans.resp = AXI4_OKAY;
  endtask : axi_to_ddr_data_width_conversion

  //-----------------------------------------------------------------------------
  // Name        : reg_read
  // Argument    : None
  // Description : This method 
  //-----------------------------------------------------------------------------
  //function bit [31:0] reg_read (string address_type = "", string field_name = "");
  //  //TODO: Need to change the method name once register model is available
  //  return reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.dis_auto_refresh.read(address_type, field_name);
  //endfunction : reg_read

  //-----------------------------------------------------------------------------
  // Name        : page_policy_explicit_autoprecharge_intelligent_precharge
  // Argument    : None
  // Description : This method sends precharge commands to SDRAM.
  //-----------------------------------------------------------------------------
  task page_policy_explicit_autoprecharge_intelligent_precharge();
    //TODO: Assign hif_cmd_autopre with wrapper signal arautopre_0.
    bit hif_cmd_autopre=0;
    bit sched0_pageclose;
    int schedtmg0_pageclose_timer, internal_page_counter;
    //TODO: Update below forever triggering to CAM transaction
    forever @(hif_cmd_autopre, sched0_pageclose, schedtmg0_pageclose_timer) begin
      if (hif_cmd_autopre == 1) begin
        lpddr_exp_trans.mem_cmd = AMEM_PRECHARGE;
        lpddr_exp_trans.a10_ap = 'b1;
      end
      else begin
        if (sched0_pageclose == 1'b0) begin
          lpddr_exp_trans.mem_cmd = AMEM_PRECHARGE;
          lpddr_exp_trans.a10_ap = 'b0;
        end
        else if((sched0_pageclose == 1'b1) && (schedtmg0_pageclose_timer == 0)) begin
          if(m_exp_q.size()>1) begin
            lpddr_exp_trans.mem_cmd = AMEM_PRECHARGE;
            lpddr_exp_trans.a10_ap = 'b0;
          end
          else begin
            lpddr_exp_trans.mem_cmd = AMEM_PRECHARGE;
            lpddr_exp_trans.a10_ap = 'b1;
          end
        end
        else if ((sched0_pageclose == 1'b1) && (schedtmg0_pageclose_timer > 0)) begin
          if(m_exp_q.size()>0) begin
            lpddr_exp_trans.mem_cmd = AMEM_PRECHARGE;
            lpddr_exp_trans.a10_ap = 'b0;
          end
          wait(m_exp_q.size()==0);
          internal_page_counter = schedtmg0_pageclose_timer;
          if(m_exp_q.size()>0) break;
          else begin
            internal_page_counter = internal_page_counter - 1;
            if(internal_page_counter == 0) begin
              lpddr_exp_trans.mem_cmd = AMEM_PRECHARGE;
              lpddr_exp_trans.a10_ap = 'b0;
            end
          end
        end
      end
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : page_policy_explicit_autoprecharge_intelligent_precharge

  //-----------------------------------------------------------------------------
  // Name        : address_collision_write_combine
  // Argument    : None
  // Description : This method handles address Collision and write combine while
  //               transactions are out-of-order.
  //-----------------------------------------------------------------------------
  task address_collision_write_combine();
    //TODO: Assign below bit to value '0' somewhere in base as per reference doc
    bit [3:0] addrmap6_addrmap_col_b3=0;
    bit opctrl0_dis_wc, flow_control, queue_flush;
    //TODO: replace below queue with CAM Write queue
    int cam_write_queue[$];
    int cam_addr, cam_data, saved_addr, saved_data, ddr_addr, ddr_data;
    //TODO: Update below event with write CAM Queue
    forever@(trans_written_to_write_queue) begin
      if (current_write_combine_state == IDLE) begin
        if (opctrl0_dis_wc == 1) begin
          saved_addr = cam_addr;
          saved_data = cam_data;
          next_write_combine_state = COMBINE;
        end
        else begin
          flow_control = 1;
          saved_addr = cam_addr;
          saved_data = cam_data;
          next_write_combine_state = BUFFER;
        end
      end
      else if (current_write_combine_state == COMBINE) begin
        if (cam_addr == saved_addr) begin
          saved_data = cam_data;
        end
        else begin
          ddr_addr = saved_addr;
          ddr_data = saved_data;
          next_write_combine_state = IDLE;
        end
      end
      else if (current_write_combine_state == BUFFER) begin
        if (!queue_flush) begin
          queue_flush = 1;
          ddr_addr = saved_addr;
          ddr_data = saved_data;
          flow_control = 0;
          next_write_combine_state = IDLE;
        end
      end
      else if (current_write_combine_state == FLUSH) begin
        queue_flush = 0;
        next_write_combine_state = BUFFER;
      end
      current_write_combine_state = next_write_combine_state;
    end
  endtask : address_collision_write_combine

  //-----------------------------------------------------------------------------
  // Name        : direct_software_refresh_or_auto_refresh
  // Argument    : None
  // Description : This method implements refresh controls and management.
  //-----------------------------------------------------------------------------
  task direct_software_refresh_or_auto_refresh();
    int rfshmod0_refresh_burst;
    bit rfshctl0_dis_auto_refresh, rfshmod0_per_bank_refresh, rfmmod0_rfm_en;
    bit [31:0] oprefctrl_rank_refresh[2];
    bit [31:0] oprefstat_rank_refresh_busy[2];
    bit [1:0] rfmmod0_raadec, rfmmod0_raamult;

    fork
      forever @(oprefctrl_rank_refresh[0], oprefctrl_rank_refresh[1]) begin
        if (per_bank_refresh_arr.size() < per_bank_refresh) begin
          for(int i=0;i<2;i++) begin
            for(int j=0;j<32;j++) begin
              per_bank_refresh_arr.push_back(oprefctrl_rank_refresh[i][j]);
              oprefstat_rank_refresh_busy[i][j] = 0;
            end
          end
        end
        else begin
          for(int i=0; i<2; i++) begin
            for(int j=0;j<32;j++) begin
              oprefstat_rank_refresh_busy[i][j] = 1;
            end
          end
        end
      end
      forever @(rfshctl0_dis_auto_refresh) begin
        if(rfshctl0_dis_auto_refresh == 1) begin
          //Per-Bank Refresh
          if((rfshmod0_per_bank_refresh==1) && (!((derateen_derate_enable == 1) && (rfshmod0_auto_refab_en > 0)))) begin
            wait(m_exp_q.size()==0);
            foreach(per_bank_refresh_arr[i]) begin
              lpddr_exp_trans.mem_cmd = AMEM_REFRESH;
              if (rfshmod0_refresh_burst == 63) begin
                #(9*3.906us);
              end
              else #rfshset1tmg1_t_rfc_min; 
            end
          end
          //All Bank Refresh
          else begin
            foreach(all_bank_refresh_arr[i]) begin
              lpddr_exp_trans.mem_cmd = AMEM_REFRESH;
              #rfshset1tmg1_t_rfc_min;
            end
          end
        end
        exp_lpddr_port.write(lpddr_exp_trans);
      end
      forever @(rfshmod0_refresh_burst) begin
        //Single Refresh
        if(rfshmod0_refresh_burst == 0) begin
          #3.906us; //tREFI timing as per LPDDR spec
          lpddr_exp_trans.mem_cmd = AMEM_REFRESH;
        end
        //Burst Refresh
        else if(rfshmod0_refresh_burst > 0) begin
          repeat (rfshmod0_refresh_burst + 1) begin
            lpddr_exp_trans.mem_cmd = AMEM_REFRESH;
          end
        end
        //Speculative Refresh
        else begin
          wait(m_exp_q.size()==0);
          fork
            begin
              #rfshsrt1tmg0_refresh_to_x1_x32;
              lpddr_exp_trans.mem_cmd = AMEM_REFRESH;
            end
            begin
              wait(m_exp_q.size()>0);
            end
          join_any
        end
        exp_lpddr_port.write(lpddr_exp_trans);
      end
      //Refresh Management
      forever @(received_lpddr_trans) begin
        if (rfmmod0_rfm_en == 1) begin
          foreach(raa_counter[i]) begin
            if(lpddr_trans.mem_cmd == AMEM_ACTIVE) raa_counter[i] = raa_counter[i] + 1;
            else if (raa_counter[i] == rfmmod0_raaimt) raa_counter[i] = raa_counter[i];
            //TODO: find REFab/REFpb commands for counter decrement and uncomment below line
            //else if(lpddr_trans.mem_cmd == AMEM_REFM) raa_counter[i] = raa_counter[i] - rfmmod0_raaimt;
            else if(lpddr_trans.mem_cmd == AMEM_REFM) raa_counter[i] = raa_counter[i] - (rfmmod0_raaimt * rfmmod0_raadec);
          end
        end
      end
    join
  endtask : direct_software_refresh_or_auto_refresh

  //-----------------------------------------------------------------------------
  // Name        : automatic_temperature_derating
  // Argument    : None
  // Description : This method implement automatic temperature derating to
  //               control refresh commands.
  //-----------------------------------------------------------------------------
  task automatic_temperature_derating();
    //TODO: Take MR4 updates from VIP and use derateint_mr4_read_interval between two MR4 reads
    bit deratectl0_derate_enable, deratectl5_derate_temp_limit_intr_force, deratectl5_derate_temp_limit_intr_clr;
    bit [7:0] mr4;
    forever@(deratectl0_derate_enable) begin
      if(deratectl0_derate_enable == 1) begin
        if ((mr4[4:0]=='b01101) || (mr4[4:0]==01111))begin
          //#; //TODO: TBDs are there in the timing mentioned in reference
          lpddr_exp_trans.mem_cmd = AMEM_REFRESH;
        end
        else if ((mr4[4:0]=='b00000) || (mr4[4:0]==11111))begin
          top_signals_intf.derate_temp_limit_intr_fault = 'b10;
        end
        else if (deratectl5_derate_temp_limit_intr_force==1)begin
          top_signals_intf.derate_temp_limit_intr_fault = 'b10;
        end
        else if (deratectl5_derate_temp_limit_intr_clr==1)begin
          top_signals_intf.derate_temp_limit_intr_fault = 'b01;
        end
      end
      if(deratectl5_derate_temp_limit_intr_en == 1) begin
        if ((mr4[4:0]=='b00000) || (mr4[4:0]==11111))begin
          top_signals_intf.derate_temp_limit_intr = 1;
          top_signals_intf.derate_temp_limit_intr_fault = 'b10;
        end
        else if (deratectl5_derate_temp_limit_intr_force==1)begin
          top_signals_intf.derate_temp_limit_intr = 1;
          top_signals_intf.derate_temp_limit_intr_fault = 'b10;
        end
        else if (deratectl5_derate_temp_limit_intr_clr==1)begin
          top_signals_intf.derate_temp_limit_intr = 0;
          top_signals_intf.derate_temp_limit_intr_fault = 'b01;
        end
      end
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : automatic_temperature_derating

  //-----------------------------------------------------------------------------
  // Name        : zq_calibration
  // Argument    : None
  // Description : This method implements ZQ Calibration commands and reset.
  //-----------------------------------------------------------------------------
  task zq_calibration();
    bit zqctl2_dis_srx_zqcl, zqctl0_dis_auto_zq, opctrlcmd_zq_calib_short, opctrlstat_zq_calib_short_busy, zqctl1_zq_reset, zqstat_zq_reset_busy;
    int zqset1tmg1_t_zq_short_interval_x1024;
    forever@(received_lpddr_trans) begin
      if(zqctl2_dis_srx_zqcl == 0) begin
        wait(lpddr_trans.mem_cmd == AMEM_SELF_REF_EXT);
        lpddr_exp_trans.mem_cmd = AMEM_ZQ_CAL;
      end
      if (zqctl0_dis_auto_zq == 0) begin
        #zqset1tmg1_t_zq_short_interval_x1024;
        lpddr_exp_trans.mem_cmd = AMEM_ZQ_CAL;
      end
      else begin
        if ((opctrlcmd_zq_calib_short == 1) && (opctrlstat_zq_calib_short_busy == 0)) begin
          lpddr_exp_trans.mem_cmd = AMEM_ZQ_CAL;
        end
        opctrlstat_zq_calib_short_busy = 1;
      end
      if ((zqctl1_zq_reset == 1) && (zqstat_zq_reset_busy == 0)) begin
        //TODO: confirm below assignment once as it is not mentioned in databook
          lpddr_exp_trans.mem_cmd = AMEM_NOP;
      end
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : zq_calibration

  //-----------------------------------------------------------------------------
  // Name        : mrr_snooping
  // Argument    : None
  // Description : This method MRR Snoop Control.
  //-----------------------------------------------------------------------------
  task mrr_snooping();
    int dqsoscctl0_dqsosc_interval;
    bit dqsoscctl0_dqsosc_enable;
    bit [7:0] dqsoscruntime_dqsosc_runtime, dqsoscruntime_wck2dq0_runtime;
    forever@(dqsoscctl0_dqsosc_enable) begin
      if(dqsoscctl0_dqsosc_enable == 1) begin
        lpddr_exp_trans.mem_cmd = AMEM_MPC;
        #(dqsoscruntime_dqsosc_runtime + dramset1tmg14_t_osco);
        lpddr_exp_trans.mem_cmd = AMEM_MPC;
        #(dqsoscruntime_wck2dq0_runtime + dramset1tmg14_t_osco);
        //TODO: read different mode registers with below MRR commands, refer page: 236 from databook
        lpddr_exp_trans.mem_cmd = AMEM_MODEREG_RD;
        lpddr_exp_trans.mem_cmd = AMEM_MODEREG_RD;
        lpddr_exp_trans.mem_cmd = AMEM_MODEREG_RD;
        lpddr_exp_trans.mem_cmd = AMEM_MODEREG_RD;
        #dqsoscctl0_dqsosc_interval;
      end
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : mrr_snooping

  //-----------------------------------------------------------------------------
  // Name        : mode_reg_read_write
  // Argument    : None
  // Description : This method enables mode register read/write through software.
  //-----------------------------------------------------------------------------
  task mode_reg_read_write();
    bit mrctrl0_mr_type, mrstat_mr_wr_busy, mrctrl0_mr_wr;
    forever@(received_lpddr_trans) begin
      if(mrctrl0_mr_wr == 1) begin
        while(mrstat_mr_wr_busy == 0) begin
          if (mrctrl0_mr_type == 0) begin
            lpddr_exp_trans.mem_cmd = AMEM_MODE_RS; //MRW
          end
          else begin
            lpddr_exp_trans.mem_cmd = AMEM_MODEREG_RD; //MRR
          end
        end
      end
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : mode_reg_read_write

  //-----------------------------------------------------------------------------
  // Name        : data_bus_inversion
  // Argument    : None
  // Description : This method allows data inversion if DBI is enabled.
  //-----------------------------------------------------------------------------
  task data_bus_inversion();
    //TODO: replace below data with CAM data
    int cam_data;
    bit dbi_enable;
    bit dfimisc_phy_dbi_mode, dbictl_rd_dbi_en, dbictl_wr_dbi_en;
    forever@(cam_data) begin
      if((dfimisc_phy_dbi_mode == 0) && ((dbictl_rd_dbi_en == 1) || (dbictl_wr_dbi_en == 1))) begin
        if($countones(cam_data) > 4) begin
          dbi_enable = 1;
          cam_data = ~cam_data;
        end
        else begin
          dbi_enable = 0;
          cam_data = cam_data;
        end
      end
    end
  endtask : data_bus_inversion

  //-----------------------------------------------------------------------------
  // Name        : precharge_power_down_mode
  // Argument    : None
  // Description : This method is used to put memory in power down mode from
  //               IDLE based on a programmable idle timeout period.
  //-----------------------------------------------------------------------------
  task precharge_power_down_mode();
    bit pwrctl_powerdown_en;
    int pwrtmg_powerdown_to_x32;
    forever@(received_lpddr_trans, pwrctl_powerdown_en) begin
      if (pwrctl_powerdown_en == 1) begin
        if (lpddr_trans.mem_cmd == AMEM_NOP) begin
          #pwrtmg_powerdown_to_x32;
          lpddr_exp_trans.mem_cmd = AMEM_POWER_DOWN;
        end
        else if (m_exp_q.size()>0) lpddr_exp_trans.mem_cmd = AMEM_POWER_DOWN_EXT;
        else if ((pwrctl_selfref_sw == 1) || (pwrctl_selfref_en == 1)) lpddr_exp_trans.mem_cmd = AMEM_POWER_DOWN_EXT;
      end
      else lpddr_exp_trans.mem_cmd = AMEM_POWER_DOWN_EXT;
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : precharge_power_down_mode

  //-----------------------------------------------------------------------------
  // Name        : self_refresh_mode
  // Argument    : None
  // Description : This method is used to put memory in self-refresh mode from
  //               IDLE based on a programmable idle timeout period.
  //-----------------------------------------------------------------------------
  task self_refresh_mode();
    int pwrtmg_selfref_to_x32;
    forever@(received_lpddr_trans, pwrctl_selfref_en, pwrctl_selfref_sw) begin
      if (pwrctl_selfref_en == 1) begin
        if (m_exp_q.size()==0) begin
          #pwrtmg_selfref_to_x32;
          lpddr_exp_trans.mem_cmd = AMEM_SELF_REF;
        end
      end
      //else if (dfiphymstr_dfi_phymstr_en==1)//TODO: Complete this
      //TODO: Not sure which enum value to be used for self-refresh PowerDown mode
      else if (pwrctl_selfref_sw == 1) begin
        if (m_exp_q.size()==0) begin
          lpddr_exp_trans.mem_cmd = AMEM_SELF_REF;
        end
      end
      else if ((pwrctl_selfref_en == 0) || (m_exp_q.size()>0) || (pwrctl_selfref_sw == 0)) begin
        lpddr_exp_trans.mem_cmd = AMEM_SELF_REF_EXT;
      end
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : self_refresh_mode

  //-----------------------------------------------------------------------------
  // Name        : deep_sleep_mode
  // Argument    : None
  // Description : This method is used to put memory in deep sleep mode from
  //               IDLE based on a programmable idle timeout period.
  //-----------------------------------------------------------------------------
  task deep_sleep_mode();
    bit pwrctl_dsm_en;
    forever@(received_lpddr_trans, pwrctl_selfref_en, pwrctl_selfref_sw, pwrctl_dsm_en, hwlpctl_hw_lp_en, dfiphymstr_dfi_phymstr_en) begin
      if((pwrctl_selfref_en == 0) && (m_exp_q.size()==0) && (pwrctl_selfref_sw == 0) && (hwlpctl_hw_lp_en == 0) && (pwrctl_dsm_en == 1) && (dfiphymstr_dfi_phymstr_en == 0)) begin
        lpddr_exp_trans.mem_cmd = AMEM_DEEP_PDOWN;
      end
      else lpddr_exp_trans.mem_cmd = AMEM_DEEP_PDOWN_EXT;
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : deep_sleep_mode

  //-----------------------------------------------------------------------------
  // Name        : dfi_dram_clk_disable
  // Argument    : None
  // Description : This method asserts dfi_dram_clk_disable in power down modes.
  //-----------------------------------------------------------------------------
  task dfi_dram_clk_disable();
    bit pwrctl_en_dfi_dram_clk_disable, disable_dfi_dram_clk;
    int dfitmg0_dfi_t_ctrl_delay, dramset1tmg5_t_cksre, dfitmg1_dfi_t_dram_clk_disable, dramset1tmg5_t_cksrx, dfitmg1_dfi_t_dram_clk_enable, dramset1tmg6_t_ckcsx;
    forever@(received_lpddr_trans, pwrctl_en_dfi_dram_clk_disable) begin
      if(pwrctl_en_dfi_dram_clk_disable == 1) begin
        if(lpddr_trans.mem_cmd == AMEM_SELF_REF) begin
          disable_dfi_dram_clk = 1;
          #(dfitmg0_dfi_t_ctrl_delay+dramset1tmg5_t_cksre-dfitmg1_dfi_t_dram_clk_disable);
          disable_dfi_dram_clk = 0;
          #(dfitmg1_dfi_t_dram_clk_disable+dramset1tmg5_t_cksrx-dfitmg0_dfi_t_ctrl_delay);
          lpddr_exp_trans.mem_cmd = AMEM_SELF_REF_EXT;
        end
        else if (lpddr_trans.mem_cmd == AMEM_POWER_DOWN) begin
          disable_dfi_dram_clk = 1;
          #(dfitmg0_dfi_t_ctrl_delay+dramset1tmg5_t_cksre-dfitmg1_dfi_t_dram_clk_disable);
          disable_dfi_dram_clk = 0;
          #(dfitmg1_dfi_t_dram_clk_disable+dramset1tmg5_t_cksrx-dfitmg0_dfi_t_ctrl_delay);
          lpddr_exp_trans.mem_cmd = AMEM_POWER_DOWN_EXT;
        end
        else if ((lpddr_trans.mem_cmd != AMEM_DEEP_PDOWN) && (lpddr_trans.mem_cmd != AMEM_SELF_REF) && (lpddr_trans.mem_cmd != AMEM_POWER_DOWN)) begin
          disable_dfi_dram_clk = 1;
          #(dfitmg0_dfi_t_ctrl_delay-dfitmg1_dfi_t_dram_clk_disable);
          disable_dfi_dram_clk = 0;
          #(dfitmg1_dfi_t_dram_clk_disable+dramset1tmg6_t_ckcsx-dfitmg0_dfi_t_ctrl_delay);
          //TODO: below command will be other than SRX, PDX, DSMX
          //lpddr_exp_trans.mem_cmd = AMEM_POWER_DOWN_EXT;
        end
      end
      else disable_dfi_dram_clk = 0;
      exp_lpddr_port.write(lpddr_exp_trans);
    end
  endtask : dfi_dram_clk_disable

  //-----------------------------------------------------------------------------
  // Name        : write
  // Argument    : amem_command_class t
  // Description : The write function automatically submits the input transaction
  //               to the transform function.  If the return value of the transform
  //               function is not null then the transaction returned from the
  //               transform function is broadcast out the analysis port. 
  //-----------------------------------------------------------------------------
  virtual function void write (amem_command_class t);
    //Creating seperate copy of transaction
    assert($cast(lpddr_trans,t.clone()));
    ->received_lpddr_trans;
    `uvm_info("write_to_predictor_lpddr", $sformatf("Expected LPDDR transaction written to LPDDR scoreboard = \n%s", t.sprintf()),UVM_LOW)
    //write on port or into fifo
  endfunction : write

  //-----------------------------------------------------------------------------
  // Name        : write_from_axi
  // Argument    : mvc_sequence_item_base trans
  // Description : The write function automatically submits the input transaction
  //               to the transform function.  If the return value of the transform
  //               function is not null then the transaction returned from the
  //               transform function is broadcast out the analysis port. 
  //-----------------------------------------------------------------------------
  virtual function void write_from_axi (mvc_sequence_item_base trans);
    //Creating seperate copy of transaction
    `uvm_info("write_to_predictor_axi_1", $psprintf("Expected LPDDR transaction written to LPDDR scoreboard = \n%s", trans.sprint()),UVM_LOW)
    assert($cast(axi_trans,trans.clone()));
    `uvm_info("write_to_predictor_axi_2", $psprintf("Expected LPDDR transaction written to LPDDR scoreboard = \n%s", axi_trans.sprint()),UVM_LOW)
    ->received_axi_trans;
  endfunction : write_from_axi

endclass : lpddr_subsystem_reference_model
`endif //LPDDR_SUBSYSTEM_REFERENCE_MODEL_SV
