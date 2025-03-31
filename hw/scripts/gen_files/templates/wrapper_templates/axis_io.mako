<%page args="port_dict, last, intf, lo, post_fix=''"/>\

  //-------------------
  // AXIS ${intf}
  //-------------------

  % for port in port_dict['ports']:
  %if port['packed_dim'] != "":
  ${f"{port['dir']} {port['packed_dim'] if type(port['packed_dim']) is str else ''} {port['port']},"}
  %elif len(port['width']) > 0:
  ${f"{port['dir'].split(' ')[0]} {port['width'][0]} {port['port']},"}
  %else:
  ${f"{port['dir']} {port['port']},"}
  %endif
  % endfor
