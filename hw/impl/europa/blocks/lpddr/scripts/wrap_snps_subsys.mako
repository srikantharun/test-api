// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Wrapper of snps LPDDR subsys to align snps naming with our naming convention. 
// This is the actual LPDDR module instanciated inside lpddr_p. 
// Auto generated using wrap_snps_subsys.py/hjson/mako
// Owner: Roel Uytterhoeven

module lpddr_subsys_wrapper (
<% ports_added = [] %>\
%for ax_port in port_map.values():
<%
if ax_port.tie or ax_port.unconnected or ax_port.dont_expose or ax_port.name in ports_added:
    continue
else:
    ports_added.append(ax_port.name)
%>\
    ${ax_port.direction} ${ax_port.type} ${f'[{ax_port.width-1}:0]' if ax_port.width > 1 else ''} ${ax_port.name}${',' if not loop.last else ''}
%endfor
);
## If we have local connections that are not exposed in an io declaration, we still need to declare the signal here.
%for ax_port in set(port_map.values()):
%if ax_port.local and ax_port.dont_expose:
    ${ax_port.type} ${f'[{ax_port.width-1}:0]' if ax_port.width > 1 else ''} ${ax_port.name};
%endif
%endfor

    snps_ddr_subsystem snps_ddr_subsystem_inst (
%for snps_port, ax_port in port_map.items():
<%
if ax_port.unconnected:
    connection_str = '';
else:
    connection_str = f"{ax_port.name}"
%>\
        .${snps_port.name}(${connection_str})${',' if not loop.last else ''}
%endfor
    );

endmodule
