// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

module fifo_v3 #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter type dtype_t                = logic [DATA_WIDTH-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
)(
    input  wire  i_clk,            // Clock
    input  wire  i_rst_n,           // Asynchronous reset active low
    input  logic  flush_i,          // flush the queue
    // test_mode to bypass clock gating
    input  logic  testmode_i,       // ASO-UNUSED_INPUT : Testmode is historical and no longer used in fifo_v3
    // status flags
    output logic  full_o,           // queue is full
    output logic  empty_o,          // queue is empty
    output logic  [ADDR_DEPTH-1:0] usage_o,  // fill pointer
    // as long as the queue is not full we can push new data
    input  dtype_t  data_i,           // data to push into the queue
    input  logic  push_i,           // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    output dtype_t  data_o,           // output data
    input  logic  pop_i             // pop head from queue
);
    // local parameter
    // FIFO depth - handle the case of pass-through, synthesizer will do constant propagation
    localparam int unsigned FifoDepth = (DEPTH > 0) ? DEPTH : 1;
    // Update the pointers
    logic update_write_pointer;
    logic update_read_pointer;
    logic update_status_pointer;
    // pointer to the read and write section of the queue
    logic [ADDR_DEPTH - 1:0] read_pointer_q, write_pointer_q;
    // keep a counter to keep track of the current queue status
    // this integer will be truncated by the synthesis tool
    logic [ADDR_DEPTH:0] status_cnt_n, status_cnt_q;
    // actual memory
    dtype_t mem_q[FifoDepth];

    always_comb usage_o = status_cnt_q[ADDR_DEPTH-1:0];

    if (DEPTH == 0) begin : gen_pass_through
        assign empty_o     = ~push_i;
        assign full_o      = ~pop_i;
    end else begin : gen_fifo
        assign full_o       = (status_cnt_q == FifoDepth[ADDR_DEPTH:0]);
        assign empty_o      = (status_cnt_q == 0) & ~(FALL_THROUGH & push_i);
    end
    // status flags

    always_comb begin : proc_mem_pointers
        update_write_pointer = 1'b0;
        update_read_pointer  = 1'b0;

        if (!(FALL_THROUGH && (status_cnt_q == 0) && push_i && pop_i)) begin
            if (push_i && !full_o)  update_write_pointer = 1'b1;
            if (pop_i  && !empty_o) update_read_pointer  = 1'b1;
        end
    end

    always_comb begin : proc_status_pointer
        status_cnt_n          = status_cnt_q;
        update_status_pointer = 1'b0;

        unique case ({update_write_pointer, update_read_pointer})
            2'b10: begin
                status_cnt_n          = status_cnt_q + 1;
                update_status_pointer = 1'b1;
            end
            2'b01: begin
                status_cnt_n          = status_cnt_q - 1;
                update_status_pointer = 1'b1;
            end
            default: /*use defaults */;
        endcase
    end

    always_comb begin : proc_output_data
        if (FALL_THROUGH && (status_cnt_q == 0) && push_i) data_o = data_i;
        else data_o = (DEPTH == 0) ? data_i : mem_q[read_pointer_q];
    end

    // sequential process
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if(~i_rst_n) begin
          read_pointer_q  <= '0;
          write_pointer_q <= '0;
          status_cnt_q    <= '0;
        end else begin
          if (flush_i) begin
            read_pointer_q  <= '0;
            write_pointer_q <= '0;
            status_cnt_q    <= '0;
          end else begin
            if (update_read_pointer)   read_pointer_q  <= (read_pointer_q  == ADDR_DEPTH'(FifoDepth - 1)) ? ADDR_DEPTH'(0) : read_pointer_q  + ADDR_DEPTH'(1);
            if (update_write_pointer)  write_pointer_q <= (write_pointer_q == ADDR_DEPTH'(FifoDepth - 1)) ? ADDR_DEPTH'(0) : write_pointer_q + ADDR_DEPTH'(1);
            if (update_status_pointer) status_cnt_q    <= status_cnt_n;
          end
        end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            foreach (mem_q[i]) mem_q[i] <= dtype_t'(0);
        end else if (update_write_pointer) begin
            mem_q[write_pointer_q] <= data_i;
        end
    end

// pragma translate_off
`ifndef SYNTHESIS
`ifndef VERILATOR
    initial begin
        assert (DEPTH > 0)             else $error("DEPTH must be greater than 0.");
    end

    full_write : assert property(
        @(posedge i_clk) disable iff (~i_rst_n) (full_o |-> ~push_i))
        else $fatal (1, "Trying to push new data although the FIFO is full.");

    empty_read : assert property(
        @(posedge i_clk) disable iff (~i_rst_n) (empty_o |-> ~pop_i))
        else $fatal (1, "Trying to pop data although the FIFO is empty.");
`endif
`endif
// pragma translate_on

endmodule // fifo_v3
