/**
 * Abstract:
 * axi_wr_rd_sequencial_sequence is used by the test to perform a series of write followed by a series of reads.
 * The write and read are configurable. Constraints are also available in
 * order to have the possibility to run it randomly.
 * A the end, a check is performed to check the data integrity
 *
 * Execution phase: main_phase
 * Sequencer: Master agent sequencer
 */

`ifndef GUARD_AXI_WR_RD_SEQUENCIAL_SEQUENCE_SV
`define GUARD_AXI_WR_RD_SEQUENCIAL_SEQUENCE_SV

class axi_wr_rd_sequencial_sequence extends axi_basic_sequence;


    // UVM Object Utility macro
    `uvm_object_utils(axi_wr_rd_sequencial_sequence)

    // Class Constructor
    function new(string name="axi_wr_rd_sequencial_sequence");
        super.new(name);
    endfunction

    virtual task body();
        svt_axi_master_transaction write_tran, read_tran;

        svt_axi_master_transaction check_write_tran [$];
        svt_axi_master_transaction check_read_tran [$];

        `uvm_info("body", "Entered ...", UVM_LOW)

        super.body();


        for(int k = 0; k < sequence_length; k++) begin
            fork
                automatic int i = k;
                begin
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
                    `uvm_info("body", "before finish write", UVM_MEDIUM);
                    finish_item(write_tran);
                end

                begin
                    // Wait for the write transaction to complete
                    `uvm_info("body", "waiting for response", UVM_MEDIUM);
                    get_response(rsp);
                    `uvm_info("body", "AXI WRITE transaction completed", UVM_MEDIUM);

                    check_write_tran.push_back(rsp);
                end
            join_any

        end

        wait fork;

        for(int j = 0; j < sequence_length; j++) begin
            fork
                automatic int i = j;
                begin
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

                    start_item(read_tran);
                    `uvm_info("body", "before finish read_tran", UVM_MEDIUM);
                    finish_item(read_tran);
                end

                begin
                // Wait for the read transaction to complete
                get_response(rsp);
                check_read_tran.push_back(rsp);

                `uvm_info("body", "AXI READ transaction completed", UVM_MEDIUM)
                end
            join_any


        end

        wait fork;

        if(enable_checks) begin
            foreach (check_write_tran[tr]) begin
                foreach (check_write_tran[tr].data[dt]) begin
                    assert(check_read_tran[tr].data[dt] == check_write_tran[tr].data[dt]) begin
                        checks++;
                    end
                        else `uvm_error("RW_Seq", $sformatf("Assertion failed: write and read data don't match. Read value: %0d, Write value %0d", check_read_tran[tr].data[dt], check_write_tran[tr].data[dt]));
                end
            end

            assert(checks > 0) `uvm_info("body", $sformatf("%0d checks completed!", checks), UVM_LOW) else `uvm_error("RW_Seq", "Assertion failed: no checks performed");
        end
        `uvm_info("body", "Exiting...", UVM_LOW)
    endtask: body

endclass: axi_wr_rd_sequencial_sequence

`endif // GUARD_AXI_WR_RD_SEQUENCIAL_SEQUENCE_SV
