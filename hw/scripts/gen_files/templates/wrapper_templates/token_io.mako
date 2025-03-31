<%page args="port_dict, last, intf, lo, post_fix=''"/>\
<%!
    import re
    def generate_dimensions_ocpl(nr_tokens):
        return '[' + ']['.join(f"{dim}:0" for dim in nr_tokens) + ']'

    def update_intf_prefix(intf, direction):
        # Remove existing direction prefix if present
        if intf.startswith('i_') or intf.startswith('o_'):
            intf = intf[2:]  # Remove the first two characters
            # Prepend the correct prefix based on the direction
            prefix = 'i_' if 'input' in direction else 'o_'
            return prefix + intf
        else:
          return intf
%>\
<%
if post_fix != '':
  to_post_fix = '_' + post_fix
  from_post_fix = '_' + post_fix
else :
  to_post_fix = ''
  from_post_fix = ''
%>\
%if port_dict['direction']=='output':
  //-------------------------------
  // Token ${intf}
  //-------------------------------
  ${'input  ' if not lo else ''}logic ${port_dict['ports'][0]['packed_dim']} ${update_intf_prefix(intf, 'input')}${to_post_fix}_rdy  ${';' if lo else ','}
  ${'output ' if not lo else ''}logic ${port_dict['ports'][0]['packed_dim']} ${update_intf_prefix(intf, 'output')}${from_post_fix}_vld  ${';' if lo else ','}
%elif port_dict['direction']=='input':
  //-------------------------------
  // Token ${intf}
  //-------------------------------
  ${'output ' if not lo else ''}logic ${port_dict['ports'][0]['packed_dim']} ${update_intf_prefix(intf, 'output')}${from_post_fix}_rdy  ${';' if lo else ','}
  ${'input  ' if not lo else ''}logic ${port_dict['ports'][0]['packed_dim']} ${update_intf_prefix(intf, 'input')}${to_post_fix}_vld  ${';' if lo else ','}
%endif
