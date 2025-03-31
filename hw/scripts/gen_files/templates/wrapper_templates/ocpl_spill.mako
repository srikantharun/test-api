<%page args="module_dict, ocpl_intf, clocks, resets"/>
<%
processed_interfaces = set()
def find_and_match_dir(sig_channel, sig, bus, match=True):
    for other_bus, bus_dict in ocpl_intf.items():
        if bus[2:] == other_bus[2:]:
            # print(f"Buses are the same: {other_bus[2:]}")
            for port in bus_dict['ports']:
                if sig_channel in port['port'] and (module_dict["info"][sig]["dir"] == port['dir']) == match:
                  return other_bus
    return ""
%>
%for intf, port_dict in ocpl_intf.items():
% if port_dict['pipe']:
//-------------------------------
// OCPL SPILL for ${intf}
//-------------------------------
## Generate the logic connection between spill registers and block
%for sig in module_dict["sig"]:
<%
sig_channel = {"mcmd": "mcmd", "maddr": "maddr", "mdata": "mdata", "scmd_accept": "scmdaccept"}.get(sig.split('_')[-1], sig.split('_')[-1])
%>\
%for port in port_dict['ports']:
<%
conn_width = f"{port['symbol_id']}" if port['symbol_id'] else 'logic'
num_ocpls = port['symbol_id']
%>\
%if sig_channel in port['port'] and module_dict["info"][sig]["dir"] != port['dir']:
%for i in range(1 if port_dict['pipe'] is True else port_dict['pipe']):
%if i == 0:
${conn_width} ${intf}_subip_${sig_channel.ljust(3)};
%else:
${conn_width} ${intf}_subip_pipe_${i}_${sig_channel.ljust(3)};
%endif
%endfor
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
%for i in range(1 if port_dict['pipe'] is True else port_dict['pipe']):
<%
## TODO: check if we need this
## Keep all but the outer most pipeline stage running on the internal clock to maximize idle power savings when the internal clock is gated
## clk_name = port_dict['clock'] if port_dict['rate_adapter'] and i == port_dict['pipe']-1 else clocks[port_dict['clock']]['internal_signal']
%>\
## generate the spill register
${module_dict["instance_name"]} #(
  %if module_dict['params']:
  % for key, data in module_dict['params'].items():
  % if key == intf[2:]:
  % for param, value in data.items(): 
  <%
  last = ',' if not loop.last else ''
  %>\
  ## Hardcoding package name "chip_pkg" as for OCPL ports the package name is not being propogated through
  .${param}(logic[chip_pkg::${value}-1:0])${last}
  % endfor
  % endif
  % endfor
  %endif
  ) ${intf}_spill${f"_{i}" if i >= 1 else ""} (
%for sig in module_dict["sig"]:
<%
last = ',' if not loop.last else ''
clock_name  = clocks[port_dict['clock']]['internal_signal']
reset_name  = resets[port_dict['reset']][clock_name]['internal_signal']
sig_channel = {"mcmd": "mcmd", "maddr": "maddr", "mdata": "mdata", "accept": "scmdaccept"}.get(sig.split('_')[-1], sig.split('_')[-1])
%>\
%if '_clk' in sig:
    .${sig}(${clock_name})${last}
%elif '_rst' in sig:
    .${sig}(${reset_name})${last}
%elif find_and_match_dir(sig_channel, sig, intf, True):
%if i == 0:
    .${sig}(${find_and_match_dir(sig_channel, sig, intf, True)}_${sig_channel})${last}
%else:
    .${sig}(${find_and_match_dir(sig_channel, sig, intf, True)}_subip_pipe_${i}_${sig_channel})${last}
%endif
%elif find_and_match_dir(sig_channel, sig, intf, False):
%if i == port_dict['pipe']-1:
    .${sig}(${find_and_match_dir(sig_channel, sig, intf, False)}_subip_${sig_channel})${last}
%else:
    .${sig}(${find_and_match_dir(sig_channel, sig, intf, False)}_subip_pipe_${i+1}_${sig_channel})${last}
%endif
% else:
    .${sig}(1'b0)${last}
%endif
%endfor
);
%endfor
%endif
%endif
%endfor
