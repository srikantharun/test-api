## P Wrapper Configuration File Specification

This document outlines the configuration specifications for the configuration file(`_p.hjson`), which guides the wrapper generator script to produce the intended SystemVerilog file. Below, we explore each section of the HJSON file, detailing its purpose and effective usage.

### 1. General Design Specifications

This section specifies basic identifiers and file paths necessary for configuring the SystemVerilog design wrapper.

```json
{
  "design_name": "l2",
  "wrapper_name": "l2_p",
  "design_file": "{REPO_ROOT}/hw/impl/europa/blocks/l2/rtl/l2_impl.sv",
  "wrapper_file": "{REPO_ROOT}/hw/impl/europa/blocks/l2/rtl/l2_p.sv",
  "wrap_p": true
}
```

- **`design_name`**: Name of the design block.
- **`wrapper_name`**: Specifies the SystemVerilog wrapper module's name.
- **`design_file`**: Path to the original SystemVerilog design file.
- **`wrapper_file`**: Target path for the generated SystemVerilog wrapper file.
- **`wrap_p`**: Boolean flag to enable or disable wrapper generation.

### 2. Port Configuration

Defines the I/O ports and protocol bus interfaces, specifying their configurations for the wrapper.

```json
"ports": {
  "clk": ["i_clk"],
  "rst": ["i_rst_n"],
  "axi": {
    "defaults": {
      "pipe": true,
      "rate_adapter": false,
      "clock": "i_clk",
      "reset": "i_rst_n"
    }
  },
  "axis": {
    "defaults": {
      "pipe": false,
      "rate_adapter": false,
      "clock": "i_clk",
      "reset": "i_rst_n"
    }
  }
  ocpl:{
    "defaults" : {
      "pipe" : 2 # if more pipelines needed, put the number of that here
      "rate_adapter" : false
      "clock" : i_clk
      "reset" : i_rst_n
    }
  }
}
```

- **`clk`, `rst`**: Lists of clock and reset signals.
- **Subsections (e.g., `axi`, `axis`, `tokens`, `ocpl`)**: Specify configurations for different protocol interfaces.
  - **`defaults`**: Default settings for each bus interface, such as pipelining (`pipe`), rate adaptation, and associated clocks and resets.
    - **`pipe`**: When set, enables spill register pipelines; a true/numeric value auto-generates these registers and their connections.
    - **`rate_adapter`**: Toggles rate adapter functionality for the bus.
    - **`clock`**: Specifies the default clock for operations on the bus.
    - **`reset`**: Designates the default reset for operations on the bus.

### 3. Clocks and Resets

Details specifications for clock and reset signals, including attributes like synchronization and clock gating/dividers, which are currently not handled by the script.

```json
"clocks": {
  "i_clk": {
    "freq": 1200,
    "divider": {
      "reset": "i_rst_n"
    },
    "gate": false
  }
},
"resets": {
  "i_rst_n": {
    "i_clk": {
      "synchronise": false
    }
  }
}
```

- **`clocks`**: Describes each clock with attributes like frequency, potential dividers, and gating.
- **`resets`**: Configures resets linked to their respective clocks and details synchronization settings.

### 4. Package Information

Specifies SystemVerilog package files necessary for the block, particularly when pipelining is enabled, to fetch constants for spill register parameters.

```json
"pkg_info": [
  "{REPO_ROOT}/hw/impl/europa/asic/rtl/pkg/chip_pkg.sv",
  "{REPO_ROOT}/hw/ip/axi/default/rtl/pkg/axi_pkg.sv"
]
```

### 5. Partition Controller

Enables the generation of the partition controller interface and its instantiation by adding the `pctl` section. This requires specific parameter details for the generated partition controller which should be explicitly provided as seen in the example below.

```json
"pctl": {
  "params": {
    "N_FAST_CLKS": 1,
    "N_RESETS": 1,
    "CLKRST_MATRIX": "1'b1",
    "PLL_CLK_IS_I_CLK": "1'b1",
    "AUTO_RESET_REMOVE": "1'b0",
    "paddr_t": "chip_syscfg_addr_t",
    "pdata_t": "chip_apb_syscfg_data_t",
    "pstrb_t": "chip_apb_syscfg_strb_t"
  }
}
```

### 5.1 Partition Controller Connections

When working with partition controllers, you can override its default connections using the `override_con` parameter within the partition controller (`pctl`) configuration. This allows you to customize how signals are routed to different components within your design.

#### Example of `override_con`

```json
pctl: {
    override_con: {
      i_clk: i_ref_clk
      i_pll_clk: i_clk
    }
  }
```

In this example:

- **`i_clk: i_ref_clk`**: This line specifies that the input clock (`i_clk`) for the partition controller should be connected to `i_ref_clk`, which might be a reference clock used elsewhere in the design.

### 6. DFT Interface

Set the `dft` flag to the desired interface type to generate the DFT interface. Available types include `default`, `ssn`, and `no_mem`, defined in `./hw/scripts/gen_files/templates/dft_interface.mako`.

```json
"dft": "default"
```

### 7. AO CSRs

To generate AO CSRs in the wrapper set the `ao_csr` flag to true.

```json
"ao_csr": true
```

```verilog
l2_csr_reg_pkg::l2_csr_reg2hw_t             reg2hw;
l2_csr_reg_pkg::l2_csr_hw2reg_t             hw2reg;

l2_csr_reg_top u_l2_ao_csr (
  .clk_i    (i_clk),
  .rst_ni   (o_ao_rst_sync_n),
  .apb_i    (o_ao_csr_apb_req),
  .apb_o    (i_ao_csr_apb_rsp),
  .reg2hw,
  .hw2reg,
  .devmode_i(1'b1)
);
```

### 8. PVT Sensor

Activates the PVT sensor in the wrapper by setting `pvt_sensor` to true, generating the sensor and exposing its connections on the interface.

```json
"pvt_sensor": true
```

#### PVT Probe Example

```verilog
// PVT probe:
tu_tem0501ar01_ln05lpe_4007002 pvt_probe (
  .IBIAS_TS(i_ibias_ts),
  .VSENSE_TS(i_vsense_ts)
);
```

### 9. Custom IP connections

To optionally add custom connections for the block, set the `ip_con_file` to point to the sv file to be included. This file will be included in the block's connection definitions.

To do this:

In the HJSON add the directive poinint to the file:

```json
ip_con_file: l2_con.sv
```

This will generate the following include in the _p file.

```verilog
--
...
  .o_axi_s_arready(o_axi_s_subip_arready),
  .o_axi_s_rvalid(o_axi_s_subip_rvalid),
  .o_axi_s_rlast(o_axi_s_subip_rlast),
  .o_axi_s_rid(o_axi_s_subip_rid),
  .o_axi_s_rdata(o_axi_s_subip_rdata),
  .o_axi_s_rresp(o_axi_s_subip_rresp),
  `include "l2_con.sv"
);
```

Also, any connections added to the file defined in `ip_con_file` will also need to be part of hjson config to specifically force the script to not make default connections for these ports using `ip_ignore_conn` as shown below:

```json
ip_ignore_conn:[
    o_irq
    i_scp_ecc_disable
    o_scp_error_status_ecc_err_present
    o_scp_error_status_ecc_err_index
]
```

### 10. Override Default IP Connections
An alternative way to handle IP connections more dynamically and in a more manageable manner using the HJSON configuration format is using `ip_override_con`

`ip_override_con` allows designers to specify custom port connections for IP blocks directly within the HJSON configuration file.

#### Example of `ip_override_con`

```json
  ip_override_con: {
      i_clk: i_ref_clk
  }
```

In this configuration:

- **`i_clk`**: This is the port on the IP block that is being configured.
- **`i_ref_clk`**: This is the external signal or clock that you want to connect to the `i_clk` port of the IP.

### 11. Run the flow

e.g.

make gen_p_wrappers P_WRAPPER_BLOCK_NAMES=aic_infra
