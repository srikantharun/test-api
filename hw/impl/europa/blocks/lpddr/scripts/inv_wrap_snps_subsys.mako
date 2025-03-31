// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Inverse wrapper of lpddr_p and lpddr_subsys_wrapper.sv to return to snps names as much as possible and bypass lpddr_p wrapper logic when required. Auto generated using wrap_snps_subsys.py/hjson/mako
// Owner: Roel Uytterhoeven

module lpddr_subsys_inv_wrapper (
%for snps_port, ax_port in port_map.items():
    ${snps_port.direction} ${ax_port.type} ${f'[{snps_port.width-1}:0]' if snps_port.width > 1 else ''} ${snps_port.name}${',' if not loop.last else ''}
%endfor
);

    lpddr_p axelera_lpddr_top_inst (
        // Ports that have no direct relation to SNPS ports
%for wrapper_port, wrapper_port_conn in wrapper_port_map.items():
        .${wrapper_port.name}(${wrapper_port_conn}),
%endfor
        // Ports that have a direct relation to SNPS ports (i.e. renamed or passed through spill reg)
<% ports_added = [] %>\
%for snps_port, ax_port in port_map.items():
<%
if ax_port.tie or ax_port.unconnected or ax_port.not_on_p_wrapper or snps_port.dont_expose or ax_port.dont_expose or ax_port in ports_added:
    continue
else:
    ports_added.append(ax_port)
%>\
        .${ax_port.name}(${snps_port.name})${',' if not loop.last else ''}
%endfor
    );

    // Force outputs that axelera does not connect in their wrapper to directly connect with the ports of the snps subsys
    initial begin
%for snps_port, ax_port in port_map.items():
% if ax_port.unconnected:
        force ${snps_port.name} = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.${snps_port.name};
%endif
%endfor
    end

    // Force the output of the pctl lpddr_clk to be exactly the same as the core_ddrc_core_clk to avoid delays between both due to the clock gate in the pctl.
    initial begin
        force axelera_lpddr_top_inst.lpddr_clk = core_ddrc_core_clk;
        force axelera_lpddr_top_inst.ctrl_rst_n = aresetn_0;
    end
    
    // Force inputs that axelera ties-off in their wrapper to directly connect with their original signal names.
    initial begin
%for snps_port, ax_port in port_map.items():
% if ax_port.tie:
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.${snps_port.name} = ${snps_port.name};
%endif
%endfor
    end

    // Force signals that end in the axelera lpddr_p module, either in a csr or some other logic that is not just unconnected or tie.
    initial begin
%for snps_port in port_map.keys():
%if snps_port.force:
%if snps_port.direction == "input":
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.${snps_port.name} = ${snps_port.name};
%elif snps_port.direction == "output":
        force ${snps_port.name} = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.${snps_port.name};
%else:
        Error, inout port should not be forced.
%endif
%endif
%endfor
    end

endmodule
