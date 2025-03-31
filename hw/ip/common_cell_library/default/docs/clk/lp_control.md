---
title: Low Power Control
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

::: hw/ip/common_cell_library/default/rtl/axe_ccl_clk_lp_control.sv:axe_ccl_clk_lp_control

## Q-Channel handshake
The handshaking between device and controller is following the AMBA Low Power interface [protocol](https://developer.arm.com/documentation/ihi0068/latest/).

The clock will only be gated when the device is in the state Q_STOPPED.

<script type="WaveDrom">
{signal: [
  {name: 'gated clk', wave: 'p|......l|...p.....'},
  {name: 'QREQn',     wave: '1..0........1......'},
  {name: 'QACCEPTn',  wave: '1......0........1..'},
  {name: 'state',     wave: '2..2...2....2...2..', data:['Q_RUN', 'Q_REQUEST', 'Q_STOPPED', 'Q_EXIT', 'Q_RUN']},
]}
</script>

## QActive
Qactive is being used to kick off QREQn and to open the gate as soon as possible when needed.

Once qactive is low and the configured idle delay passed, the low power sequence will start.

<script type="WaveDrom">
{signal: [
  {name: 'gated clk', wave: 'p|...|....l|..p....'},
  {name: 'QACTIVE',   wave: '1..0.|......1......'},
  {name: 'QREQn',     wave: '1....|.0.....1.....'},
  {name: 'QACCEPTn',  wave: '1....|...0......1..'},
  {name: 'state',     wave: '2..2...2.2...2..2..', data:['Q_RUN', 'Q_RUN wait idle count', 'Q_REQ', 'Q_STOPPED', 'Q_EXIT', 'Q_RUN']},
]}
</script>
