/**
 * Abstract:
 * SPM Monitor, primarly used to monitor the IRQ and the ecc signals
 * it takes the passive spm if from the top
 */
`ifndef GUARD_SPM_UVM_MONITOR_SV
`define GUARD_SPM_UVM_MONITOR_SV

class spm_uvm_monitor extends uvm_monitor;
    `uvm_component_utils(spm_uvm_monitor)

    virtual spm_if vif;

    uvm_event ecc_read_completed_ev, ecc_read_started_ev;

    bit enable_ecc_mon;

    typedef enum {READ_COMPLETE_EV, ECC_ERR_EV} e_complete_read_or_error;

    typedef struct {
            e_complete_read_or_error  ecc_event;
            time                      timestamp;
    } read_ecc_event_t;

    read_ecc_event_t        read_ecc_event[$];


    /** Class Constructor */
    function new (string name="spm_uvm_monitor", uvm_component parent=null);
        super.new (name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(virtual spm_if)::get(this, "", "spm_intf", vif);
        uvm_config_db#(uvm_event)::get(null, get_full_name(), "ecc_read_completed_ev", ecc_read_completed_ev);
        uvm_config_db#(uvm_event)::get(null, get_full_name(), "ecc_read_started_ev", ecc_read_started_ev);

        if(!uvm_config_db#(bit)::get(null, get_full_name(), "enable_ecc_mon", enable_ecc_mon)) begin
            `uvm_fatal(get_full_name(), $sformatf("MON: en missign"))
        end

        if(enable_ecc_mon) begin
            `uvm_info(get_full_name(), "MON: enabled", UVM_LOW)
        end else begin
            `uvm_info(get_full_name(), "MON: disabled", UVM_LOW)
        end

    endfunction


    // Monitor's main run phase
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        if(enable_ecc_mon) begin
            wait_for_reset();

            if(vif.spm_if_scp_ecc_disable) begin
                `uvm_info(get_full_name(), "MON: ecc is disabled", UVM_LOW)
                return;
            end

            forever @(posedge vif.spm_if_clk) begin
                // safety frok for the disable
                fork begin
                    fork
                        monitor_irq();
                        monitor_scp_error_status();
                    join_any
                    // Stop tasks if reset or disable signal becomes active
                    wait_for_reset();
                    disable fork;
                end join
            end
        end
    endtask

    task wait_for_reset();
        @(negedge vif.spm_if_rst_n);
        `uvm_info(get_full_name(), $sformatf("MON: reset asserted at time %0t", $time), UVM_LOW)
        @(posedge vif.spm_if_rst_n);
        `uvm_info(get_full_name(), $sformatf("MON: reset de-asserted at time %0t", $time), UVM_LOW)
    endtask


    task monitor_irq();
        forever begin
            @(posedge vif.spm_if_clk);
            if (vif.spm_if_scp_error_status.ecc_err && vif.spm_if_scp_error_status.ecc_err_type == 1'b1) begin
                @(posedge vif.spm_if_clk);
                assert (vif.spm_if_irq == 1) else begin
                    `uvm_error(get_full_name(), $sformatf("MON: Assertion failed: irq did not become 1 with 2 bits error"))
                end
            end
        end
    endtask



    task monitor_scp_error_status();
        begin
            fork begin
                fork
                    //waits for the error
                    begin
                        forever begin
                            read_ecc_event_t error_event_tmp;
                            @(posedge vif.spm_if_clk);
                            if(vif.spm_if_scp_error_status.ecc_err == 1) begin

                                error_event_tmp.timestamp = $time();
                                error_event_tmp.ecc_event = ECC_ERR_EV;

                                read_ecc_event.push_back(error_event_tmp);
                                `uvm_info(get_full_name(), $sformatf("MON: ecc err was reported at time %0t", $time), UVM_LOW)
                            end
                        end
                    end
                    begin
                        forever begin
                            read_ecc_event_t read_event_tmp;
                            ecc_read_completed_ev.wait_trigger();
                            ecc_read_completed_ev.reset();

                            read_event_tmp.timestamp = $time();
                            read_event_tmp.ecc_event = READ_COMPLETE_EV;

                            read_ecc_event.push_back(read_event_tmp);
                            `uvm_info(get_full_name(), $sformatf("MON: read was completed at time %0t", $time), UVM_LOW)
                        end
                    end

                join_any
                disable fork;
            end
            join_none
        end
    endtask


    //checkf if 2 consecutive reads or if 2 consecutive errors happpen
    function void check_phase(uvm_phase phase);
        if(enable_ecc_mon) begin
            `uvm_info(get_full_name(), $sformatf("MON: entering check_phase"), UVM_LOW)

            if(read_ecc_event.size() < 2)
                `uvm_error(get_full_name(), $sformatf("MON: too few events recorded"))


            `uvm_info(get_full_name(), $sformatf("MON: event list: %p", read_ecc_event), UVM_NONE)

            for(int i = 1; i < read_ecc_event.size(); i++) begin
                if(read_ecc_event[i].ecc_event == read_ecc_event[i-1].ecc_event) begin
                    `uvm_info(get_full_name(), $sformatf("MON: event list: %p", read_ecc_event), UVM_NONE)
                    `uvm_error(get_full_name(), $sformatf("MON: 2 consecutives events at indexes %0d and %0d", i, i-1))
                end
            end
        end

    endfunction
endclass


`endif  // GUARD_SPM_MONITOR_SV
