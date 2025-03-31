<%namespace name="wrapper_defs" file="wrapper_defs.mako"/>
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
##// Description: ${description}
##// Owner: ${owner} (${email})

module ${wrapper_name}
%if imports:
%for p in imports:
  import ${p}::*;
%endfor
%endif

#(
%if localparam:
%for p_type, p_items in localparam.items():
<%last='' if loop.last and not param else ','%>\
%for name, value in p_items.items():
  localparam ${p_type} ${name} = ${value}${last}
%endfor
%endfor
%endif
%if param:
% for parameter, type in param.items():
<%last='' if loop.last else ','%>\
  parameter type ${parameter} = ${type}${last}
% endfor
%endif
)(
  //-------------------------------
  // interface signals
  //-------------------------------

  //-------------------------------
  // wrapper io
  //-------------------------------
%for clock in clocks:
  input  wire   ${clock},
%endfor
%for reset in resets:
  input  wire   ${reset},
%endfor
%for port, port_dict in ports['misc'].items():
%if (module != "pcie" or (module == "pcie" and (port not in ["axi_lp_m_rst_n", "axi_lp_s_rst_n", "axi_dbi_s_rst_n"]))) and not 'tie' in port_dict and not ('internal' in port_dict and port_dict['internal']) and port not in clocks and port not in resets:
<% last = '' if loop.last and len(ports['axis'])==0 and len(ports['ocpl'])==0 and len(ports['token'])==0 and len(ports['axi'])==0 and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ',' %>\
<%if (ip_ignore_conn and port in ip_ignore_conn) or (ip_override_con and port in ip_override_con):
  continue
%>\
  ${port_dict['dir'].replace('logic', port_dict['symbol_id']) if port_dict['symbol_id'] and port_dict['symbol_id'].split('::')[0] not in port_dict['packed_dim'] else port_dict['dir']} ${"" if isinstance(port_dict['packed_dim'], int) else port_dict['packed_dim']} ${port}${last}
%endif
%endfor

  //-------------------------------
  // protocol ports
  //-------------------------------
%for intf, port_dict in ports['axis'].items():
<%last='' if loop.last and len(ports['token'])==0 and len(ports['axi'])==0 and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ','%>\
<%include file="wrapper_templates/axis_io.mako" args="port_dict=port_dict, last=last, intf=intf, lo=False"/>\
%endfor
%for intf, port_dict in ports['ocpl'].items():
<%last='' if loop.last and len(ports['token'])==0 and len(ports['axi'])==0 and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ','%>\
<%include file="wrapper_templates/ocpl_io.mako" args="port_dict=port_dict, last=last, intf=intf, lo=False"/>\
%endfor
%for intf, port_dict in ports['token'].items():
<%last='' if loop.last and len(ports['axi'])==0 and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ','%>\
<%include file="wrapper_templates/token_io.mako" args="port_dict=port_dict, last=last, intf=intf, lo=False"/>\
%endfor
%for intf, port_dict in ports['axi'].items():
<%last='' if loop.last and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ','%>\
<%include file="wrapper_templates/axi_io.mako" args="port_dict=port_dict, except_dict=except_dict, last=last, intf=intf, lo=False"/>\
%endfor

% if pctl: 
  //-------------------------------
  // Partition Controller Interface
  //-------------------------------
<%
pctl_signals = [
("i_ref_clk",                "input",  "wire",    1),
("i_ao_rst_n",               "input",  "wire",    1),
("i_global_rst_n",           "input",  "wire",    1),
("o_ao_rst_sync_n",          "output", "wire",    1),
("o_noc_async_idle_req",     "output", "logic",   1),
("i_noc_async_idle_ack",     "input",  "logic",   1),
("i_noc_async_idle_val",     "input",  "logic",   1),
("o_noc_clken",              "output", "logic",   "N_FAST_CLKS"),
("i_cfg_apb4_s_paddr",       "input",  "paddr_t", 1),
("i_cfg_apb4_s_pwdata",      "input",  "pdata_t", 1),
("i_cfg_apb4_s_pwrite",      "input",  "logic",   1),
("i_cfg_apb4_s_psel",        "input",  "logic",   1),
("i_cfg_apb4_s_penable",     "input",  "logic",   1),
("i_cfg_apb4_s_pstrb",       "input",  "pstrb_t", 1),
("i_cfg_apb4_s_pprot",       "input",  "logic",   3),
("o_cfg_apb4_s_pready",      "output", "logic",   1),
("o_cfg_apb4_s_prdata",      "output", "pdata_t", 1),
("o_cfg_apb4_s_pslverr",     "output", "logic",   1),
("o_noc_rst_n",              "output", "wire",    1),
]

max_name_len = max(len(sig[0]) for sig in pctl_signals)
max_dir_len  = max(len(sig[1]) for sig in pctl_signals)
max_spec_len = max(len(pctl['params'][sig[2]] if sig[2] in pctl['params'] else sig[2]) for sig in pctl_signals)
max_size_len = max(len(f"[{sig[3]-1}:0]") if isinstance(sig[3], int) and sig[3] > 1 else len("    ") for sig in pctl_signals)
%>\
% for sig_item in pctl_signals:
<%
  sig_name  = sig_item[0]
  sig_dir   = sig_item[1]
  sig_spec  = sig_item[2]
  sig_width = ""
  size_width = sig_item[3]
  # Determine the width based on the type of size_width (int or string parameter key)
  if sig_spec in pctl['params']:
    sig_spec = pctl['params'][sig_spec]
  if isinstance(size_width, str):
    if size_width in pctl['params']:
      param_value = pctl['params'][size_width]
      if isinstance(param_value, int) and param_value > 1:
        sig_width = f'[{param_value}-1:0]'
    else:
      sig_width = f'[{size_width}-1:0]'
  elif isinstance(size_width, int) and size_width > 1:
    sig_width = f'[{size_width}-1:0]'
  last = ","
%>\
  ${sig_dir.ljust(max_dir_len)} ${sig_spec.ljust(max_spec_len)} ${sig_width.ljust(max_size_len)} ${sig_name.ljust(max_name_len)}${last}
% endfor
% endif
%if pvt_sensor:

  //-------------------------------
  // PVT Probe Interface
  //-------------------------------
  inout wire io_ibias_ts,
  inout wire io_vsense_ts,
%endif
%if dft:
  <%include file="dft_interface.mako" args="ignore_ports=ports['misc'].keys()"/>\
%endif
);

//-------------------------------
// Protocols
//-------------------------------
## AXIS spill registers
<%include file="wrapper_templates/axis_spill.mako" args="module_dict=axis_spill, axis_intf=ports['axis'], clocks=clocks, resets=resets"/>\
## Token spill registers
<%include file="wrapper_templates/token_spill.mako" args="module_dict=token_spill, token_intf=ports['token'], clocks=clocks, resets=resets"/>\
## OCPL spill registers
<%include file="wrapper_templates/ocpl_spill.mako" args="module_dict=ocpl_spill, ocpl_intf=ports['ocpl'], clocks=clocks, resets=resets"/>\
## AXI functional wrapping (spill register, logger, sva monitor)
<%include file="wrapper_templates/axi_spill.mako" args="module_dict=axi_spill, axi_intf=ports['axi'], clocks=clocks, resets=resets"/>\
%if ao_csr:
//-------------------------------
// AO Reg
//-------------------------------
${design_name}_csr_reg_pkg::${design_name}_csr_reg2hw_t             reg2hw;
${design_name}_csr_reg_pkg::${design_name}_csr_hw2reg_t             hw2reg;
%endif
%if ao_csr or pctl:
pctl_ao_csr_reg_pkg::apb_h2d_t ao_csr_apb_req;
pctl_ao_csr_reg_pkg::apb_d2h_t ao_csr_apb_rsp;
%endif
//-------------------------------
// Wrapped module instantiation
//-------------------------------
${module} u_${module} (
%for port, port_dict in ports['misc'].items():
<%if ip_ignore_conn and port in ip_ignore_conn:
    continue
%>\
<% last = '' if loop.last and len(ports['axis'])==0 and len(ports['ocpl'])==0 and len(ports['token'])==0 and len(ports['axi'])==0 and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ',' %>\
%if port_dict['is_new']:
<%continue%>\
%elif ip_override_con and port in ip_override_con:
  .${port}(${ip_override_con[port]})${last}
%elif port_dict['is_clock']:
  .${port}(${clocks[port]['internal_signal']})${last}
%elif port_dict['is_reset']:
<%
connection = port
for clock in resets[port]:
  if resets[port][clock]['synchronise']:
    connection = resets[port][clock]['internal_signal']
    break
%>\
  .${port}(${connection})${last}
%elif port_dict['pipe']:
  .${port}(${port}_subip)${last}
%elif 'tie' in port_dict:
  .${port}(${port_dict['tie']})${last}
%else:
  .${port}(${port})${last}
%endif
%endfor
%for k,v in ports['axis'].items():
<% last_intf = loop.last%>\
%for port in v['ports']:
<% last = '' if loop.last and last_intf and len(ports['token'])==0 and len(ports['axi'])==0 and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ',' %>\
<%
if not port['replace']:
  repport = port['port']
else:
  repport = port['replacement']
## If port has pipeline stage, name of the port has the change on the module side
if v['pipe']:
  repport = '_'.join(repport.split('_')[:-1]) + '_subip_' + repport.split('_')[-1]
%>\
  .${port['port']}(${repport})${last}
%endfor
%endfor
%for k,v in ports['ocpl'].items():
<% last_intf = loop.last%>\
%for port in v['ports']:
<% last = '' if loop.last and last_intf and len(ports['axi'])==0 and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ',' %>\
<%
if not port['replace']:
  repport = port['port']
else:
  repport = port['replacement']
## If port has pipeline stage, name of the port has the change on the module side
if v['pipe']:
  repport = '_'.join(repport.split('_')[:-1]) + '_subip_' + repport.split('_')[-1]
%>\
  .${port['port']}(${repport})${last}
%endfor
%endfor
%for k,v in ports['token'].items():
<% last_intf = loop.last%>\
%for port in v['ports']:
<% last = '' if loop.last and last_intf and len(ports['axi'])==0 and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 else ',' %>\
<%
if not port['replace']:
  repport = port['port']
else:
  repport = port['replacement']
## If port has pipeline stage, name of the port has the change on the module side
if v['pipe']:
  repport = '_'.join(repport.split('_')[:-1]) + '_subip_' + repport.split('_')[-1]
%>\
  .${port['port']}(${repport})${last}
%endfor
%endfor
%for k,v in ports['axi'].items():
<% last_intf = loop.last%>\
%for port in v['ports']:
<% last = '' if loop.last and last_intf and len(ports['apb_v3'])==0 and len(ports['apb_v4'])==0 and not ip_con_file else ',' %>\
<%
if not port['replace']:
  repport = port['port']
else:
  repport = port['replacement']
## If port has pipeline stage, name of the port has the change on the module side
if v['pipe']:
  repport = '_'.join(repport.split('_')[:-1]) + '_subip_' + repport.split('_')[-1]
%>\
  .${port['port']}(${repport})${last}
%endfor
%endfor
%if ip_con_file:
  `include "${ip_con_file}"
%endif
);
% if pctl: 

always_comb o_noc_rst_n = ${design_name}_rst_n;
//-------------------------------
// Partition controller Instance
//-------------------------------
logic                          int_shutdown_ack ;
  ${partition["instance_name"]} #(
% for key, value in pctl['params'].items():
    .${key} (${value})${',' if not loop.last else ''}
% endfor
  ) u_${partition["instance_name"]} (
  %for sig in partition["sig"]:
  % if 'override_con' in pctl and sig in pctl['override_con']:
    .${sig}(${pctl['override_con'][sig]})${',' if not loop.last else ''}
  % else:
  % if any(signal[0] == sig for signal in pctl_signals) or 'clk' in sig:
    .${sig}(${sig})${',' if not loop.last else ''}
  % else:
    .${sig}(${sig[2:]})${',' if not loop.last else ''}
  % endif
  %endif
  %endfor
  );
%endif
%if ao_csr:

//-------------------------------
// AO CSR
//-------------------------------
${design_name}_csr_reg_top u_${design_name}_ao_csr (
  .clk_i    (i_clk),
  .rst_ni   (o_ao_rst_sync_n),
  .apb_i    (ao_csr_apb_req),
  .apb_o    (ao_csr_apb_rsp),
  .reg2hw,
  .hw2reg,
  .devmode_i(1'b1)
);
%endif
%if pvt_sensor:

// PVT probe:
pvt_probe_wrapper pvt_probe (
  .io_ibias_ts (io_ibias_ts ),
  .io_vsense_ts(io_vsense_ts)
);
%endif
## Commented for now - Expected to be inserted by Tessent
##//-------------------------------
##// DFT Instance
##//-------------------------------
##%if dft:
##<%include file="dft_instance.mako"/>\
##%endif

endmodule
