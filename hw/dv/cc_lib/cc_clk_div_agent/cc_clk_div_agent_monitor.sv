`ifndef CC_CLK_DIV_AGENT_MONITOR_SV
`define CC_CLK_DIV_AGENT_MONITOR_SV

class cc_clk_div_agent_monitor extends uvm_monitor;
  `uvm_component_utils(cc_clk_div_agent_monitor)

  string m_parent_name;
  cc_clk_div_agent_config m_cfg;
  int m_clks_after_reset;

  virtual cc_clk_div_agent_if m_vif;

  uvm_analysis_port#(cc_clk_div_agent_seq_item) ap;

  cc_clk_div_agent_seq_item m_trans;

  function new (string name, uvm_component parent);
    super.new (name, parent);
    m_parent_name = parent.get_name();
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    m_trans = cc_clk_div_agent_seq_item::type_id::create("m_trans", this);

    if ( ! uvm_config_db#( cc_clk_div_agent_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "cfg" ), .value( m_cfg ) ) ) begin
      `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
    end
  endfunction : build_phase

  virtual task monitor_incr ();

    `uvm_info(get_full_name(), $sformatf("Entering on monitor_incr"), UVM_HIGH)
    forever @(m_vif.mon) begin
      //wait for the posedge of enable to sample the value of the increment
      @(posedge m_vif.mon.enable)
        m_trans.m_type_enm = CLK_DIV_MON;
        m_trans.m_bv_incr = m_vif.mon.incr;
        ap.write(m_trans.do_clone());
      end
  endtask : monitor_incr

  virtual task monitor_reset ();
    //monitor a reset negedge and finish this task. By finishing this task it will restart all over again the monitor tasks
    @(negedge m_vif.reset_n);
    `uvm_info(get_full_name(), $sformatf("Reset was seen on the clock divider interface and monitor will be reset"), UVM_LOW)
    @(posedge m_vif.reset_n);
    `uvm_info(get_full_name(), $sformatf("Reset done!"), UVM_LOW)
  endtask : monitor_reset
  
  virtual task monitor_clk();
    int l_prev_incr = '1;
    int l_incr_stable_clks = 0;
    int l_threshold_stable_clks = 7;
    int l_out_clks_within_window=0;
    int l_num_clks_within_window=0;
    int l_clks_per_window=16;
    int l_expected_out_clks_within_window;
    int l_threshold_stable_reset = 7;

    forever @(m_vif.mon) begin
      //if clk is enable and not clear
      if((m_vif.mon.enable==1) && (m_vif.mon.clear==0) && (m_clks_after_reset>=l_threshold_stable_reset)) begin
        `uvm_info(get_full_name(), $sformatf("enable = 1 and clear = 0 | incr = %0d and prev_incr = %0d", m_vif.mon.incr, l_prev_incr), UVM_HIGH)
        //if increment equal to previous, then increment number of clock cycles stable
        if(m_vif.mon.incr == l_prev_incr) begin
          l_incr_stable_clks++;
          `uvm_info(get_full_name(), $sformatf("incrementing l_incr_stable_clks = %0d", l_incr_stable_clks), UVM_HIGH)
        end
        //else, then clear the number of stable clock cycles
        else begin
          l_incr_stable_clks=0;
          l_out_clks_within_window=0;
          l_num_clks_within_window=0;
          `uvm_info(get_full_name(), $sformatf("clear l_incr_stable_clks = %0d", l_incr_stable_clks), UVM_HIGH)
        end
        //save previous value of increment
        l_prev_incr=m_vif.mon.incr;

        //if the increment is stable for at least l_threshold_stable_clks cycles
        if(l_incr_stable_clks>=l_threshold_stable_clks) begin
          //if the output clock is high, then increment the number of clocks under the current clock_window
          if(m_vif.mon.cg_en) begin
            l_out_clks_within_window++;
            `uvm_info(get_full_name(), $sformatf("incrementing l_out_clks_within_window = %0d", l_out_clks_within_window), UVM_HIGH)
          end
          //increment number of clocks within window
          l_num_clks_within_window++;

          `uvm_info(get_full_name(), $sformatf("l_out_clks_within_window = %0d | l_num_clks_within_window = %0d", l_out_clks_within_window, l_num_clks_within_window), UVM_HIGH)
          //verify if the maximum number of clocks within a window was reached and check how many cycles occurred on that time
          if(l_num_clks_within_window==l_clks_per_window) begin
            if(m_vif.mon.incr==0) l_expected_out_clks_within_window = l_clks_per_window;
            else                  l_expected_out_clks_within_window = m_vif.mon.incr;
            if(l_out_clks_within_window == l_expected_out_clks_within_window) begin
              `uvm_info(get_full_name(), $sformatf("Number of clocks within the window of %0d clocks is equal to expetected (number of clocks = %0d)", l_clks_per_window, l_expected_out_clks_within_window), UVM_MEDIUM)
            end
            else begin
              `uvm_error(get_full_name(), $sformatf("Number of clocks within the window of %0d clocks is different from expetected. Expeted = %0d and observed = %0d", l_clks_per_window, l_expected_out_clks_within_window, l_out_clks_within_window))
            end
            //clear counter of the clocks within window to start for the next window
            l_num_clks_within_window=0;
            l_out_clks_within_window=0;
            `uvm_info(get_full_name(), $sformatf("clear l_out_clks_within_window = %0d and l_num_clks_within_window = %0d", l_out_clks_within_window, l_num_clks_within_window), UVM_HIGH)
          end
          //make sure the value does not rise above treshold
          l_incr_stable_clks=l_threshold_stable_clks;
        end
      end
      //else,then clear the number of stable clock cycles
      else begin
        l_prev_incr='1;
        l_incr_stable_clks=0;
        l_out_clks_within_window=0;
        l_num_clks_within_window=0;
        `uvm_info(get_full_name(), $sformatf("clear l_prev_incr = %0d | l_incr_stable_clks = %0d | l_out_clks_within_window = %0d | l_num_clks_within_window = %0d", l_prev_incr, l_incr_stable_clks, l_out_clks_within_window, l_num_clks_within_window), UVM_HIGH)
      end
    end
  endtask : monitor_clk
  
  virtual task monitor_clks_after_reset ();
    //set the maximum value of the 
    int l_max_reset_cnt = 20;
    forever begin
      @(posedge m_vif.reset_n);
      `uvm_info(get_full_name(), $sformatf("Reset done!"), UVM_LOW)
      fork
        begin
          forever @(m_vif.mon) begin
            if(m_clks_after_reset<=l_max_reset_cnt) begin
              m_clks_after_reset++;
            end
            else begin
              //if the maximum was achieved, then waits for the reset
              @(negedge m_vif.reset_n);
            end
          end
        end
        begin
          //re-start this task after a negedge of a reset
          @(negedge m_vif.reset_n);
        end
      join_any
      disable fork;

      //clear number of clocks after reset
      m_clks_after_reset=0;
    end
  endtask : monitor_clks_after_reset

  virtual task run_phase(uvm_phase phase);
    bit l_b_init_done;
    super.run_phase(phase);
    fork
      begin
        forever begin
          if (l_b_init_done==0) begin
            //wait for reset if the reset was not done yet
            monitor_reset();
            l_b_init_done = 1;
          end
          fork
            monitor_incr();
            monitor_reset();
          join_any
          disable fork;
        end
      end
      begin
        monitor_clk();
      end
      begin
        monitor_clks_after_reset();
      end
    join
  endtask : run_phase
endclass : cc_clk_div_agent_monitor



`endif // CC_CLK_DIV_AGENT_MONITOR_SV
