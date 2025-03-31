// Copyright 2018 ETH Zurich and University of Bologna. Copyright and related
// rights are licensed under the Solderpad Hardware License, Version 0.51 (the
// “License”); you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law or
// agreed to in writing, software, hardware and materials distributed under this
// License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, either express or implied. See the License for the specific
// language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich / Axelera AI
// Date: 15/07/2017 Description: A RISC-V privilege spec 1.11 (WIP) compatible
// CLINT (core local interrupt controller)
//

// Platforms provide a counter, exposed as a memory-mapped machine-mode
// register, mtime. mtime must run at constant frequency, and the platform must
// provide a mechanism for determining the timebase of mtime (device tree).

module gc_clint #(
  parameter int unsigned AxiAddrWidth = 64,
  parameter int unsigned AxiDataWidth = 64,
  parameter int unsigned AxiIdWidth   = 10,
  parameter int unsigned NrHarts       = 1, // Number of cores therefore also the number of timecmp registers and timer interrupts
  parameter type         axi_req_t     = logic,
  parameter type         axi_resp_t    = logic
) (
  input  logic               clk_i,       // Clock
  input  logic               rst_ni,      // Asynchronous reset active low
  input  axi_req_t           axi_req_i,
  output axi_resp_t          axi_resp_o,
  output logic [NrHarts-1:0] timer_irq_o, // Timer interrupts
  output logic [NrHarts-1:0] ipi_o        // software interrupt (a.k.a inter-process-interrupt)
);

  // register offset
  localparam logic [15:0] MSIP_BASE     = 16'h0;
  localparam logic [15:0] MTIMECMP_BASE = 16'h4000;
  localparam logic [15:0] MTIME_BASE    = 16'hbff8;

  localparam int unsigned AddrSelWidth = cc_math_pkg::index_width(NrHarts);

  // signals from AXI 4 Lite
  logic [AxiAddrWidth-1:0] address;
  logic                    en;
  logic                    we;
  logic [63:0]             wdata;
  logic [63:0]             rdata;
  logic                    error;

  // bit 11 and 10 are determining the address offset
  logic [15:0] register_address;
  assign register_address = address[15:0];
  // actual registers
  logic [63:0]              mtime_d, mtime_q;
  logic [NrHarts-1:0][63:0] mtimecmp_d, mtimecmp_q;
  logic [NrHarts-1:0]       msip_d, msip_q;

  // -----------------------------
  // AXI Interface Logic
  // -----------------------------
  axi_lite_interface #(
    .AxiAddrWidth ( AxiAddrWidth ),
    .AxiDataWidth ( AxiDataWidth ),
    .AxiIdWidth   ( AxiIdWidth   ),
    .axi_req_t    ( axi_req_t    ),
    .axi_resp_t   ( axi_resp_t   )
  ) axi_lite_interface_i (
    .clk_i      ( clk_i      ),
    .rst_ni     ( rst_ni     ),
    .axi_req_i  ( axi_req_i  ),
    .axi_resp_o ( axi_resp_o ),
    .address_o  ( address    ),
    .en_o       ( en         ),
    .we_o       ( we         ),
    .data_i     ( rdata      ),
    .data_o     ( wdata      ),
    .error_i    ( error      )
  );

  // -----------------------------
  // Register Update Logic
  // -----------------------------
  // APB register write logic
  always_comb begin
    mtime_d    = mtime_q;
    mtimecmp_d = mtimecmp_q;
    msip_d     = msip_q;
    // RTC says we should increase the timer
    mtime_d = mtime_q + 1;

    rdata = 'b0;
    error = 1'b0;
    // written from APB bus - gets priority
    if (en && we) begin
      case (register_address) inside
        [MSIP_BASE:MSIP_BASE+16'(4*NrHarts)]: begin
          msip_d[$unsigned(address[AddrSelWidth-1+2:2])] = wdata[32*address[2]];
        end

        [MTIMECMP_BASE:MTIMECMP_BASE+16'(8*NrHarts)]: begin
          mtimecmp_d[$unsigned(address[AddrSelWidth-1+3:3])] = wdata;
        end

        MTIME_BASE: begin
          mtime_d = wdata;
        end
        default: error = 1'b1;
      endcase
    end else if (en && !we) begin
      case (register_address) inside
        [MSIP_BASE:MSIP_BASE+16'(4*NrHarts)]: begin
          rdata[NrHarts-1] = msip_q[$unsigned(address[AddrSelWidth-1+2:2])];
        end

        [MTIMECMP_BASE:MTIMECMP_BASE+16'(8*NrHarts)]: begin
          rdata = mtimecmp_q[$unsigned(address[AddrSelWidth-1+3:3])];
        end

        MTIME_BASE: begin
          rdata = mtime_q;
        end
        default: error = 1'b1;
      endcase
    end
  end

    // -----------------------------
    // IRQ Generation
    // -----------------------------
    // The mtime register has a 64-bit precision on all RV32, RV64, and RV128
    // systems. Platforms provide a 64-bit memory-mapped machine-mode timer
    // compare register (mtimecmp), which causes a timer interrupt to be posted
    // when the mtime register contains a value greater than or equal (mtime >=
    // mtimecmp) to the value in the mtimecmp register. The interrupt remains
    // posted until it is cleared by writing the mtimecmp register. The
    // interrupt will only be taken if interrupts are enabled and the MTIE bit
    // is set in the mie register.
    for (genvar i = 0; i < NrHarts; i++) begin : gen_irqs
      assign timer_irq_o[i] = mtime_q >= mtimecmp_q[i];
    end

    // Registers
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
        mtime_q <= '0;
        mtimecmp_q <= '0;
        msip_q <= '0;
      end else begin
        mtime_q <= mtime_d;
        mtimecmp_q <= mtimecmp_d;
        msip_q <= msip_d;
      end
    end

    assign ipi_o = msip_q;

    // -------------
    // Assertions
    // --------------
    //pragma translate_off
    // Static assertion check for appropriate bus width
    initial begin
      assert (AxiDataWidth == 64) else $fatal("Timer needs to interface with a 64 bit bus, everything else is not supported");
    end
    //pragma translate_on

endmodule


module axi_lite_interface #(
    parameter int unsigned AxiAddrWidth = 64,
    parameter int unsigned AxiDataWidth = 64,
    parameter int unsigned AxiIdWidth   = 10,
    parameter type         axi_req_t     = logic,
    parameter type         axi_resp_t    = logic
) (
    input logic                     clk_i,
    input logic                     rst_ni,

    input  axi_req_t                axi_req_i,
    output axi_resp_t               axi_resp_o,

    output logic [AxiAddrWidth-1:0] address_o,
    output logic                    en_o,
    output logic                    we_o,
    input  logic [AxiDataWidth-1:0] data_i,
    output logic [AxiDataWidth-1:0] data_o,
    input  logic                    error_i
);

    // The RLAST signal is not required, and is considered asserted for every
    // transfer on the read data channel.
    typedef enum logic [1:0] {IDLE, READ, WRITE, WRITE_B} interface_state_e;
    interface_state_e state_q, state_d;
    // save the trans id, we will need it for reflection otherwise we are not
    // plug compatible to the AXI standard
    logic [AxiIdWidth-1:0]   trans_id_d, trans_id_q;
    // address register
    logic [AxiAddrWidth-1:0] address_d,  address_q;
    logic                    error_d,    error_q;
    // pass through read data on the read data channel
    assign axi_resp_o.r.data = data_i;
    // send back the transaction id we've latched
    assign axi_resp_o.r.id = trans_id_q;
    assign axi_resp_o.b.id = trans_id_q;
    // set r_last to one as defined by the AXI4 - Lite standard
    assign axi_resp_o.r.last = 1'b1;
    // output data which we want to write to the slave
    assign data_o = axi_req_i.w.data;
    // ------------------------
    // AXI4-Lite State Machine
    // ------------------------
    always_comb begin
        // default signal assignment
        state_d    = state_q;
        address_d  = address_q;
        trans_id_d = trans_id_q;
        error_d    = error_q;
        // we'll answer a write request only if we got address and data
        axi_resp_o.aw_ready = 1'b0;
        axi_resp_o.w_ready  = 1'b0;
        axi_resp_o.b_valid  = 1'b0;
        axi_resp_o.b.resp   = 2'b0;

        axi_resp_o.ar_ready = 1'b0;
        axi_resp_o.r_valid  = 1'b0;
        axi_resp_o.r.resp   = 2'b0;

        address_o      = '0;
        we_o           = 1'b0;
        en_o           = 1'b0;

        case (state_q)
          // we are ready to accept a new request
          IDLE: begin
            // we've git a valid write request, we also know that we have
            // asserted the aw_ready
            if (axi_req_i.aw_valid) begin
              axi_resp_o.aw_ready = 1'b1;
              // this costs performance but the interconnect does not obey the
              // AXI standard e.g.: we could wait for aw_valid && w_valid to do
              // the transaction.
              state_d = WRITE;
              // save address
              address_d = axi_req_i.aw.addr;
              // save the transaction id for reflection
              trans_id_d = axi_req_i.aw.id;
            // we've got a valid read request, we also know that we have
            // asserted the ar_ready
            end else if (axi_req_i.ar_valid) begin
              axi_resp_o.ar_ready = 1'b1;
              state_d = READ;
              // save address
              address_d = axi_req_i.ar.addr;
              // save the transaction id for reflection
              trans_id_d = axi_req_i.ar.id;
              end
            end
            // We've got a read request at least one cycle earlier so data_i
            // will already contain the data we'd like tor read
            READ: begin
              // enable the ram-like
              en_o       = 1'b1;
              // further assert the correct address
              address_o = address_q;
              // the read is valid
              axi_resp_o.r_valid = 1'b1;
              axi_resp_o.r.resp = {1'b0, error_i};
              // check if we got a valid r_ready and go back to IDLE
              if (axi_req_i.r_ready) state_d = IDLE;
            end
            // We've got a write request at least one cycle earlier wait here
            // for the data
            WRITE: begin
              if (axi_req_i.w_valid) begin
                axi_resp_o.w_ready = 1'b1;
                // use the latched address
                address_o = address_q;
                en_o = 1'b1;
                we_o = 1'b1;
                // close this request
                state_d = WRITE_B;
                error_d = error_i;
              end
            end

            WRITE_B: begin
              axi_resp_o.b_valid  = 1'b1;
              axi_resp_o.b.resp   = {1'b0, error_q};
              // we've already performed the write here so wait for the ready
              // signal
              if (axi_req_i.b_ready) state_d = IDLE;
            end
            default:;
        endcase
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
        state_q <= IDLE;
        address_q <= '0;
        trans_id_q <= '0;
        error_q <= '0;
      end else begin
        state_q <= state_d;
        address_q <= address_d;
        trans_id_q <= trans_id_d;
        error_q <= error_d;
      end
    end

    // ------------------------
    // Assertions
    // ------------------------
    // Listen for illegal transactions
    //pragma translate_off
    // check that burst length is just one
    assert property (@(posedge clk_i) axi_req_i.ar_valid |->  ((axi_req_i.ar.len == 8'b0)))
    else begin $error("AXI Lite does not support bursts larger than 1 or byte length unequal to the native bus size"); $stop(); end
    // do the same for the write channel
    assert property (@(posedge clk_i) axi_req_i.aw_valid |->  ((axi_req_i.aw.len == 8'b0)))
    else begin $error("AXI Lite does not support bursts larger than 1 or byte length unequal to the native bus size"); $stop(); end
    //pragma translate_on
endmodule
