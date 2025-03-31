/**
 * Abstract:
 * axi_wr_rd_ecc_sequence is used by the test to perform a write followed by a read.
 * The write and read are configurable. Constraints are also available in
 * order to have the possibility to run it randomly. A check is performed (if enabled)
 * to check the data integrity
 * Execution phase: main_phase
 * Sequencer: Master agent sequencer
 */

`ifndef GUARD_AXI_WR_RD_ECC_SEQUENCE_SV
`define GUARD_AXI_WR_RD_ECC_SEQUENCE_SV

class axi_wr_rd_ecc_sequence extends axi_basic_sequence;

    bit         expect_ecc_error;

    uvm_event   ecc_write_completed_ev, ecc_backdoor_access_executed_ev, ecc_read_completed_ev, ecc_read_started_ev;

    longint my_data;

    // UVM Object Utility macro
    `uvm_object_utils(axi_wr_rd_ecc_sequence)

    // Class Constructor
    function new(string name="axi_wr_rd_ecc_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_axi_master_transaction write_tran, read_tran;

        `uvm_info("body", "Entered ...", UVM_LOW)

        super.body();


        if(!uvm_config_db #(bit)::get(uvm_root::get(), "", "expect_ecc_error", expect_ecc_error))
                `uvm_fatal(get_full_name(), "no expect error found found");

        uvm_config_db#(uvm_event)::get(null, get_full_name(), "ecc_write_completed_ev", ecc_write_completed_ev);
        uvm_config_db#(uvm_event)::get(null, get_full_name(), "ecc_read_completed_ev", ecc_read_completed_ev);
        uvm_config_db#(uvm_event)::get(null, get_full_name(), "ecc_read_started_ev", ecc_read_started_ev);
        uvm_config_db#(uvm_event)::get(null, get_full_name(), "ecc_backdoor_access_executed_ev", ecc_backdoor_access_executed_ev);

        for(int i = 0; i < sequence_length; i++) begin
            // Set up the write transaction
            `uvm_create(write_tran)

            `uvm_info("body", "created write", UVM_LOW);
            write_tran.port_cfg     = cfg;
            write_tran.xact_type    = svt_axi_transaction::WRITE;
            write_tran.addr         = addr_array[i];
            write_tran.burst_type   = burst_type[i];
            write_tran.burst_size   = burst_size[i];
            write_tran.atomic_type  = svt_axi_transaction::NORMAL;
            write_tran.burst_length = wburst_length[i];
            write_tran.addr_valid_delay = calc_delay(max_addr_valid_delay, min_addr_valid_delay);
            write_tran.bready_delay = calc_delay(max_bready_delay, min_bready_delay);
            write_tran.id = wid[i];

            write_tran.data         = new[write_tran.burst_length];
            foreach (write_tran.data[j]) begin
                write_tran.data[j] = {$urandom(), $urandom()};
            end

            write_tran.wstrb        = new[write_tran.burst_length];
            foreach (write_tran.wstrb[j]) begin
                write_tran.wstrb[j] = calc_wstrb(burst_size[i]);
            end

            write_tran.wvalid_delay = new[write_tran.burst_length];
            foreach (write_tran.wvalid_delay[j]) begin
                write_tran.wvalid_delay[j] = calc_delay(max_wvalid_delay, min_wvalid_delay);
            end


            // Send the write transaction
            start_item(write_tran);

            finish_item(write_tran);

            // Wait for the write transaction to complete
            `uvm_info("body", "waiting for response", UVM_MEDIUM);
            get_response(rsp);
            `uvm_info("body", "AXI WRITE transaction completed", UVM_MEDIUM);


            u_axe_clk_if.await_rising_edge(5);
            ecc_write_completed_ev.trigger();

            // Backdoor access on functions of hdl_top

            ecc_backdoor_access_executed_ev.wait_trigger();
            ecc_backdoor_access_executed_ev.reset();

            // Set up the read transaction
            `uvm_create(read_tran)
            read_tran.port_cfg          = cfg;

            read_tran.xact_type    = svt_axi_transaction::READ;
            read_tran.addr         = addr_array[i];
            read_tran.burst_type   = burst_type[i];
            read_tran.burst_size   = burst_size[i];
            read_tran.atomic_type  = svt_axi_transaction::NORMAL;
            read_tran.burst_length = rburst_length[i];
            read_tran.addr_valid_delay = calc_delay(max_addr_valid_delay, min_addr_valid_delay);
            read_tran.id = rid[i];

            read_tran.rresp        = new[read_tran.burst_length];
            read_tran.data         = new[read_tran.burst_length];
            read_tran.data_user    = new[read_tran.burst_length];

            read_tran.rready_delay = new[read_tran.burst_length];
            foreach (read_tran.rready_delay[j]) begin
                read_tran.rready_delay[j] = calc_delay(max_rready_delay, min_rready_delay);
            end

            `uvm_info("body", "before start read_tran", UVM_MEDIUM);
            start_item(read_tran);
            `uvm_info("body", "before finish read_tran", UVM_MEDIUM);
            finish_item(read_tran);

            ecc_read_started_ev.trigger();

            //check the rsp type

            // Wait for the read transaction to complete
            get_response(rsp);

            ecc_read_completed_ev.trigger();

            if(enable_checks) begin
                if(expect_ecc_error) begin
                    foreach (write_tran.data[k]) begin
                        assert(rsp.data[k] != write_tran.data[k]) begin
                            checks++;
                            `uvm_info("RW_Seq", $sformatf("Assertion passed: write(%0h) and read(%0h) data don't match, as expected", write_tran.data[k], rsp.data[k]), UVM_MEDIUM);
                        end
                            else `uvm_error("RW_Seq", $sformatf("Assertion failed: write(%0h) and read(%0h) data match, they shouldn't!", write_tran.data[k], rsp.data[k]));
                    end
                end else begin
                    foreach (write_tran.data[k]) begin
                        assert(rsp.data[k] == write_tran.data[k]) begin
                            checks++;
                            `uvm_info("RW_Seq", $sformatf("Assertion passed: write(%0h) and read(%0h) data match", write_tran.data[k], rsp.data[k]), UVM_MEDIUM);
                        end
                            else `uvm_error("RW_Seq", $sformatf("Assertion failed: write(%0h) and read(%0h) data don't match", write_tran.data[k], rsp.data[k]));
                    end
                end
            end

            `uvm_info("body", "AXI READ transaction completed", UVM_MEDIUM)

        end

        if(enable_checks)
            assert(checks > 0) else `uvm_error("RW_Seq", "Assertion failed: no checks performed");

        `uvm_info("body", "Exiting...", UVM_LOW)
    endtask: body

endclass: axi_wr_rd_ecc_sequence

`endif // GUARD_AXI_WR_RD_ECC_SEQUENCE_SV
