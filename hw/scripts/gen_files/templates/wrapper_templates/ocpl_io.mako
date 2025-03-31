<%page args="port_dict, last, intf, lo, post_fix=''"/>\
  //-------------------------------
  // OCPL ${intf}
  //-------------------------------
%for ocpl_port in port_dict['ocpl_ports']:
  ${port_dict['ocpl_ports'][ocpl_port]['direction']} ${port_dict['ocpl_ports'][ocpl_port]['nr_tokens']} ${port_dict['ocpl_ports'][ocpl_port]['name']}${';' if lo else ','}
%endfor
