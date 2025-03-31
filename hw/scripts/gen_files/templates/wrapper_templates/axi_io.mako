<%namespace name="wrapper_defs" file="../wrapper_defs.mako"/>\
<%page args="port_dict, except_dict, last, intf, lo, noc_len=False, wires_post_fix=''"/>\

<%
max_port_dir_len  = max(len(port['dir']) for port in port_dict['ports'])
max_port_dim_len  = max(len(str(port['packed_dim'])) for port in port_dict['ports'])
max_port_name_len = max(len(port['port']) for port in port_dict['ports'])
%>\
  //-------------------------------
  // AXI4 ${intf}
  //-------------------------------
  % for port in port_dict['ports']:
  %if port['packed_dim'] != "":
  ${f"{port['dir'].ljust(max_port_dir_len)} {(port['packed_dim'] if type(port['packed_dim']) is str else '').ljust(max_port_dim_len)} {port['port'].ljust(max_port_name_len)},"}
  %elif len(port['width']) > 0:
  ${f"{port['dir'].split(' ')[0].ljust(max_port_dir_len)} {port['width'][0].ljust(max_port_dim_len)} {port['port'].ljust(max_port_name_len)},"}
  %else:
  ${f"{port['dir'].ljust(max_port_dir_len)} {port['port'].ljust(max_port_name_len)},"}
  %endif
  % endfor
