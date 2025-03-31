<%namespace name="wrapper_defs" file="wrapper_defs.mako"/>
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
##// Description: ${description}
##// Owner: ${owner} (${email})
module ${wrapperName}
%if imports:
%for p in imports:
  import ${p}::*;
%endfor
%endif

##TODO, section for parameter if needed

##interface signals
(
%for sig in interfaceSig["sig"]:
<%
  last = '' if (loop.last and not dft) else ','
%>\
%if sig in clkList+rstList:
  input wire ${sig}${last}
%else:
<%
  sig_dir = interfaceSig["info"][sig]["dir"]
  if isinstance(interfaceSig["info"][sig]["width"], list):
    if len(interfaceSig["info"][sig]["width"]) == 1 and interfaceSig["info"][sig]["width"][0].endswith("_t"):
      sig_dir = interfaceSig["info"][sig]["dir_only"]
    elif len(interfaceSig["info"][sig]["width"]) == 2 and "pkg" in interfaceSig["info"][sig]["width"][0]:
      sig_dir = interfaceSig["info"][sig]["dir_only"]
%>
  ${sig_dir} ${wrapper_defs.packed_to_string(width_array=interfaceSig["info"][sig]["width"], packed_dim=interfaceSig["info"][sig]["packed_dim"])} ${interfaceSig["info"][sig]["newName"]}${last}
%endif
%endfor

%if dft:
<%include file="dft_interface.mako"/>\
%endif

## start here inst, and connectivity
);

  ${designName} u_${designName} (
%for sig in interfaceSig["sig"]:
<%
  last = '' if loop.last else ','
%>
  .${sig}(${interfaceSig["info"][sig]["newName"]})${last}\
%endfor

  );

## TODO enable this part when dft module is available
##%if dft:
##<%include file="dft_instance.mako"%/>\
##%endif

endmodule
