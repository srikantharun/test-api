<%page args="module_dict, axi_intf, clocks, resets"/>
<%
processed_interfaces = set()
def find_and_match_dir(sig_channel, sig, bus, match=True):
    for other_bus, bus_dict in axi_intf.items():
        if bus[2:] == other_bus[2:]:
            # print(f"Buses are the same: {other_bus[2:]}")
            for port in bus_dict['ports']:
                if sig_channel in port['port'] and (module_dict["info"][sig]["dir"] == port['dir']) == match:
                        return other_bus
    return ""
%>
%for intf, port_dict in axi_intf.items():
% if port_dict['pipe']:
//-------------------------------
// AXI SPILL for ${intf}
//-------------------------------
## Generate the logic connection between spill registers and block
%for sig in module_dict["sig"]:
<%
sig_channel = "_"+"".join(sig.split('_')[-2:])
%>\
%for port in port_dict['ports']:
<%
conn_width = (f"logic {port['packed_dim']}" if type(port['packed_dim']) is str else 'logic') if port['packed_dim'] != "" else (port['width'][0] if port['width'] else "logic")
%>\
%if sig_channel in port['port'] and module_dict["info"][sig]["dir"] != port['dir']:
  ${conn_width} ${intf}_subip${sig_channel.ljust(8)};
%endif
%endfor
%endfor
<%
modified_intf = intf[2:]
%>
%if modified_intf not in processed_interfaces:
<%
processed_interfaces.add(modified_intf)
%>
%else:
## generate the spill register
${module_dict["instance_name"]} #(
%if module_dict['params']:
% for key, data in module_dict['params'].items():
% if key == intf[2:]:
% for param, value in data.items(): 
  .${param} (${value})${','}
% endfor
% endif
% endfor
%endif
  .NumCuts(${port_dict['pipe'] if not isinstance(port_dict['pipe'], bool) else "1"})
  ) ${intf}_spill_flat (
%for sig in module_dict["sig"]:
<%
last = ',' if not loop.last else ''
clock_name  = clocks[port_dict['clock']]['internal_signal']
reset_name  = resets[port_dict['reset']][clock_name]['internal_signal']
sig_channel = "_"+"".join(sig.split('_')[-2:])
%>\
%if '_clk' in sig:
    .${sig}(${clock_name})${last}
%elif '_rst' in sig:
    .${sig}(${reset_name})${last}
%elif find_and_match_dir(sig_channel, sig, intf, True):
    .${sig}(${find_and_match_dir(sig_channel, sig, intf, True)}${sig_channel})${last}
%elif find_and_match_dir(sig_channel, sig, intf, False):
    .${sig}(${find_and_match_dir(sig_channel, sig, intf, False)}_subip${sig_channel})${last}
% else:
    .${sig}(1'b0)${last}
%endif
%endfor
);
%endif
%endif
%endfor
