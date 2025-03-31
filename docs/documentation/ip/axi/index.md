---
title: Axi
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

This library provides modules to build on-chip communication networks adhering to the
[AXI4 or AXI4-Lite standards](https://developer.arm.com/documentation/ihi0022/hc).

!!! note "Credits"

    These modules are based on the [Pulp-Platform Open Souce AXI Library](https://github.com/pulp-platform/axi).


The **design goals** are:
- **Topology Independence**: Provide elementary building blocks such as protocol [multiplexers](mux.md) and
    [demultiplexers](demux.md) that allow users to implement any network topology.  Also provide commonly used
    interconnecting components such as a [crossbar](xbar.md).
- **Modularity**: Favor design by composition over design by configuration where possible.  Strive to apply the
    *Unix philosophy* to hardware: make each module do one thing well.  This means you will more often instantiate the
    modules back-to-back than change a parameter value to build more specialized networks.
- **Fit for Heterogeneous Networks**: The modules are parametrizable in terms of data width and transaction concurrency.
    This allows to create optimized networks for a wide range of performance (e.g., bandwidth, concurrency, timing),
    power, and area requirements.  Provide modules such as [data width converters](dw_converter.md) and
    [ID width converters](id_remap.md) that allow to join subnetworks with different properties, creating heterogeneous
    on-chip networks.
- **Full AXI Standard Compliance**.
- **Compatibility** with a [wide range of (recent versions of) EDA tools](#which-eda-tools-are-supported) and
    implementation in standardized synthesizable SystemVerilog.
