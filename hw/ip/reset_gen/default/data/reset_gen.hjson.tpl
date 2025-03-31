// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
{ name: "reset_gen",
  clocking: [{clock: "clk_i", reset: "rst_ni"}],
  bus_interfaces: [
    { protocol: "tlul", direction: "device" }
  ],
  regwidth: "32",
  addrcap: "0x10000",
  registers: [
    % for c in cfg['stages']:
    { name: "RST_CFG_${c['name'].upper()}",
      desc: "Reset configuration for stage `${c['name']}`.",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        {
          bits: "${cfg['resets']-1}:0"
          name: "RST_SRC_MASK",
          desc: "Mask source for register `{c['name']}`."
          resval: "${2**cfg['resets'] - 1}"
        },
        {
          bits: "27:16",
          name: "RST_STRETCH",
          desc: "Stretch reset for register `{c['name']}`."
          resval: "${c['stretch_val']}"
        }
      ],
    },
    { name: "RST_SW_${c['name'].upper()}",
      desc: "Software reset (Active Low) for stage `${c['name']}`.",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        {
    % if c['num_ips']>1:
          bits: "${c['num_ips']-1}:0"
    % else:
          bits: "0"
    % endif
          name: "RST_SW",
          desc: "Reset stage `{c['name']}`. (active low)"
          resval: "${2**(c['num_ips']*c['sw_rstn'])-1}"
        }
      ],
    }
  % endfor
    { name: "DBNC_TIMER",
      desc: "Debounce Timer.",
      hwext: "true",
      swaccess: "rw",
      hwaccess: "hrw",
      hwqe: "true"
      fields: [
        {
            name: "dbnc_timer_val"
            bits: "31:0",
            desc: '''button reset debouncer timer value'''
            resval: 20
        }
      ],
    },
    { name: "DBNC_TIMER_PCIE_BTN_RST",
      desc: "Debounce Timer for PCIE Button Reset.",
      hwext: "true",
      swaccess: "rw",
      hwaccess: "hrw",
      hwqe: "true"
      fields: [
        {
            name: "dbnc_timer_pcie_btn_val"
            bits: "31:0",
            desc: '''PCIE button reset debouncer timer value'''
            resval: 20
        }
      ],
    },
  ]
}
