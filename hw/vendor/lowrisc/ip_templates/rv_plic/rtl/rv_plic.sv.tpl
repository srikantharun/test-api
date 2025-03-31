// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RISC-V Platform-Level Interrupt Controller compliant INTC
//
//   Current version doesn't support MSI interrupt but it is easy to add
//   the feature. Create one external register and connect qe signal to the
//   gateway module (as edge-triggered)
//
//   Consider to set MAX_PRIO as small number as possible. It is main factor
//   of area increase if edge-triggered counter isn't implemented.
//
// Verilog parameter
//   MAX_PRIO: Maximum value of interrupt priority

module ${module_instance_name} import ${module_instance_name}_reg_pkg::*; #(
<%doc>
  Note: Our version of the CSR reggen does not support alerts
  parameter logic [NumAlerts-1:0] AlertAsyncOn  = {NumAlerts{1'b1}},
</%doc>
  // OpenTitan IP standardizes on level triggered interrupts,
  // hence LevelEdgeTrig is set to all-zeroes by default.
  // Note that in case of edge-triggered interrupts, CDC handling is not
  // fully implemented yet (this would require instantiating pulse syncs
  // and routing the source clocks / resets to the PLIC).
  parameter logic [NumSrc-1:0]    LevelEdgeTrig = '0, // 0: level, 1: edge
  // Number of synchronization stages for the irq synchronizers
  parameter int unsigned          SyncStages = 3,
  // derived parameter
  localparam int SRCW    = $clog2(NumSrc)
) (
  input  wire   clk_i,
  input  wire   rst_ni,

  // Bus Interface (device)
% if csr_bus_protocol == "axi":
  input  ${module_instance_name}_reg_pkg::axi_a_ch_h2d_t axi_aw_i,
  output logic axi_awready,
  input  ${module_instance_name}_reg_pkg::axi_a_ch_h2d_t axi_ar_i,
  output logic axi_arready,
  input  ${module_instance_name}_reg_pkg::axi_w_ch_h2d_t axi_w_i,
  output logic axi_wready,
  output ${module_instance_name}_reg_pkg::axi_b_ch_d2h_t axi_b_o,
  input  logic axi_bready,
  output ${module_instance_name}_reg_pkg::axi_r_ch_d2h_t axi_r_o,
  input  logic axi_rready,
% else:
  input  ${module_instance_name}_reg_pkg::apb_h2d_t apb_i,
  output ${module_instance_name}_reg_pkg::apb_d2h_t apb_o,
% endif
  // Config
  input logic devmode_i, // If 1, explicit error return for unmapped register access
<%doc>
  Note: Not tlul for us
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,
</%doc>
  // Interrupt Sources
  input  logic [NumSrc-1:0] intr_src_i,
<%doc>
  Note: Our version of the CSR reggen does not support alerts
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
</%doc>
  // Interrupt notification to targets
  output logic [NumTarget-1:0] irq_o,
  output logic [SRCW-1:0]      irq_id_o [NumTarget],

  output logic [NumTarget-1:0] msip_o
);
  `ifndef SYNTHESIS
  `include "prim_assert.sv"
  `endif

  ${module_instance_name}_reg2hw_t reg2hw;
  ${module_instance_name}_hw2reg_t hw2reg;

  localparam int MAX_PRIO    = ${prio};
  localparam int PRIOW = $clog2(MAX_PRIO+1);

  logic [NumSrc-1:0] ip;

  logic [NumSrc-1:0] ie [NumTarget];

  logic [NumTarget-1:0] claim_re; // Target read indicator
  logic [SRCW-1:0]      claim_id [NumTarget];
  logic [NumSrc-1:0]    claim; // Converted from claim_re/claim_id

  logic [NumTarget-1:0] complete_we; // Target write indicator
  logic [SRCW-1:0]      complete_id [NumTarget];
  logic [NumSrc-1:0]    complete; // Converted from complete_re/complete_id

  logic [SRCW-1:0]      cc_id [NumTarget]; // Write ID

  logic [NumSrc-1:0][PRIOW-1:0] prio;

  logic [PRIOW-1:0] threshold [NumTarget];

  // Glue logic between ${module_instance_name}_reg_top and others
  assign cc_id = irq_id_o;

  always_comb begin
    claim = '0;
    for (int i = 0 ; i < NumTarget ; i++) begin
      if (claim_re[i]) claim[claim_id[i]] = 1'b1;
    end
  end
  always_comb begin
    complete = '0;
    for (int i = 0 ; i < NumTarget ; i++) begin
      if (complete_we[i]) complete[complete_id[i]] = 1'b1;
    end
  end

`ifndef SYNTHESIS
  //`ASSERT_PULSE(claimPulse, claim_re[i])
  //`ASSERT_PULSE(completePulse, complete_we[i])

  `ASSERT(onehot0Claim, $onehot0(claim_re))

  `ASSERT(onehot0Complete, $onehot0(complete_we))
`endif

  //////////////
  // Priority //
  //////////////
% for s in range(src):
  assign prio[${s}] = reg2hw.prio${s}.q;
% endfor

  //////////////////////
  // Interrupt Enable //
  //////////////////////
% for t in range(target):
  for (genvar s = 0; s < ${src}; s++) begin : gen_ie${t}
    assign ie[${t}][s] = reg2hw.ie${t}[s].q;
  end
% endfor

  ////////////////////////
  // THRESHOLD register //
  ////////////////////////
% for t in range(target):
  assign threshold[${t}] = reg2hw.threshold${t}.q;
% endfor

  /////////////////
  // CC register //
  /////////////////
% for t in range(target):
  assign claim_re[${t}]    = reg2hw.cc${t}.re;
  assign claim_id[${t}]    = irq_id_o[${t}];
  assign complete_we[${t}] = reg2hw.cc${t}.qe;
  assign complete_id[${t}] = reg2hw.cc${t}.q;
  assign hw2reg.cc${t}.d   = cc_id[${t}];
% endfor

  ///////////////////
  // MSIP register //
  ///////////////////
% for t in range(target):
  assign msip_o[${t}] = reg2hw.msip${t}.q;
% endfor

  ////////
  // IP //
  ////////
  for (genvar s = 0; s < ${src}; s++) begin : gen_ip
    assign hw2reg.ip[s].de = 1'b1; // Always write
    assign hw2reg.ip[s].d  = ip[s];
  end

  //////////////
  // Gateways //
  //////////////
  logic [NumSrc-1:0] intr_src_synced;
<%doc>
  Note: We use a proper axt_tcl synchronizer instead
  // Synchronize all incoming interrupt requests.
  prim_flop_2sync #(
    .Width(NumSrc)
  ) u_prim_flop_2sync (
    .clk_i,
    .rst_ni,
    .d_i(intr_src_i),
    .q_o(intr_src_synced)
  );
</%doc>
  for (genvar irq_idx = 0; unsigned'(irq_idx) < NumSrc; irq_idx++) begin : gen_irq_sync
    axe_tcl_seq_sync #(
      .SyncStages(SyncStages),
      .ResetValue(1'b0)
    ) u_irq_sync (
      .i_clk  (clk_i),
      .i_rst_n(rst_ni),
      .i_d    (intr_src_i[irq_idx]),
      .o_q    (intr_src_synced[irq_idx])
    );
  end

  ${module_instance_name}_gateway #(
    .N_SOURCE   (NumSrc)
  ) u_gateway (
    .clk_i,
    .rst_ni,

    .src_i      (intr_src_synced),
    .le_i       (LevelEdgeTrig),

    .claim_i    (claim),
    .complete_i (complete),

    .ip_o       (ip)
  );

  ///////////////////////////////////
  // Target interrupt notification //
  ///////////////////////////////////
  for (genvar i = 0 ; i < NumTarget ; i++) begin : gen_target
    ${module_instance_name}_target #(
      .N_SOURCE    (NumSrc),
      .MAX_PRIO    (MAX_PRIO)
    ) u_target (
      .clk_i,
      .rst_ni,

      .ip_i        (ip),
      .ie_i        (ie[i]),

      .prio_i      (prio),
      .threshold_i (threshold[i]),

      .irq_o       (irq_o[i]),
      .irq_id_o    (irq_id_o[i])

    );
  end

<%doc>
  Note: Our version of the CSR reggen does not support alerts
  ////////////
  // Alerts //
  ////////////

  logic [NumAlerts-1:0] alert_test, alerts;

  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[i]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end
</%doc>

  ////////////////////////
  // Register interface //
  ////////////////////////
  //  Limitation of register tool prevents the module from having flexibility to parameters
  //  So, signals are manually tied at the top.
  ${module_instance_name}_reg_top u_reg (
    .clk_i,
    .rst_ni,

% if csr_bus_protocol == "axi":
    .axi_aw_i,
    .axi_awready,
    .axi_ar_i,
    .axi_arready,
    .axi_w_i,
    .axi_wready,
    .axi_b_o,
    .axi_bready,
    .axi_r_o,
    .axi_rready,
% else:
    .apb_i,
    .apb_o,
% endif

    .reg2hw,
    .hw2reg,

<%doc>
  Note: Our version of the CSR reggen does not support alerts
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(alerts[0])
</%doc>
    .devmode_i
  );

  ////////////////
  // Assertions //
  ////////////////
`ifndef SYNTHESIS
<%doc>
  Note: Our version of the CSR reggen does not support alerts
  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
</%doc>
  `ASSERT_KNOWN(IrqKnownO_A, irq_o)
  `ASSERT_KNOWN(MsipKnownO_A, msip_o)
  for (genvar k = 0; k < NumTarget; k++) begin : gen_irq_id_known
    `ASSERT_KNOWN(IrqIdKnownO_A, irq_id_o[k])
  end

  // Assume
  `ASSUME(Irq0Tied_A, intr_src_i[0] == 1'b0)

<%doc>
  Note: Our version of the CSR reggen does not support alerts
  // This assertion should be provable in FPV because we don't have a block-level DV environment. It
  // is trying to say that any integrity error detected inside the register block (u_reg) will cause
  // an alert to be asserted within at most _SEC_CM_ALERT_MAX_CYC cycles.
  //
  // This isn't *quite* true because there are two extra requirements for prim_alert_sender to send
  // an alert with alert_p high:
  //
  //  - The multi-phase alert handshake might not be in the expected phase. Rather than adding an
  //    assumption that says alert_rx_i acks a signal when it is raised, we cheat and add a
  //    precondition about the initial state of the prim_alert_sender FSM, guaranteeing that we're
  //    not waiting for an ack.
  //
  //  - The prim_alert_sender musn't detect a signal integrity issue on the alert signal coming in
  //    (alert_rx_i). Normally FpvSecCm tests get analysed with an FPV_ALERT_NO_SIGINT_ERR define,
  //    but we don't have that defined here. To avoid this happening, we want an assertion of the
  //    form "If no integrity error is detected for _SEC_CM_ALERT_MAX_CYC cycles, the alert_p signal
  //    must go high". To encode this cleanly in SVA, we actually say "We can't have neither an
  //    integrity error nor an alert signal for too many cycles".
  `ASSERT(FpvSecCmBusIntegrity_A,
          ($rose(u_reg.intg_err) &&
           gen_alert_tx[0].u_prim_alert_sender.state_q == gen_alert_tx[0].u_prim_alert_sender.Idle)
          |->
          not ((!gen_alert_tx[0].u_prim_alert_sender.sigint_detected && !alert_tx_o[0].alert_p)
               [*`_SEC_CM_ALERT_MAX_CYC]))

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
</%doc>
`endif
endmodule
