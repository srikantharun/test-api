<%namespace name="wrapper_defs" file="wrapper_defs.mako"/>
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: ${owner} (${email})

`ifndef ${moduleName.upper()}_SV
`define ${moduleName.upper()}_SV

module ${moduleName}
%if imports:
<%imports.sort()%>
%for p in imports:
  import ${p}::*;
%endfor
%endif

##TODO, section for parameter if needed

##interface signals
(
%for sig in topInf:
<%
  last = '' if loop.last else ','
%>\
  ${topInf[sig]["dir"]} ${wrapper_defs.packed_to_string(width_array=topInf[sig]["width"], packed_dim="")} ${sig}${last}
%endfor
## start here inst, and connectivity
);

%if localparam:
%for p_type, p_items in localparam.items():
%for name, value in p_items.items():
  localparam ${p_type} ${name} = ${value};
%endfor
%endfor
%endif

## interconnection
%for sig in internalSig:
  ${internalSig[sig]["type"]} ${wrapper_defs.packed_to_string(width_array=internalSig[sig]["width"], packed_dim=internalSig[sig]["packed_dim"])} ${sig};
%endfor

## inst
<%include file="module_inst.sv.mako"/>\

endmodule
`endif  // ${moduleName.upper()}_SV
