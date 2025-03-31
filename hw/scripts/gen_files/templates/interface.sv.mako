<%namespace name="wrapper_defs" file="wrapper_defs.mako"/>
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
##// Description: ${description}
##// Owner: ${owner} (${email})
module ${name}
%if imports:
%for p in imports:
  import ${p}::*;
%endfor
%endif
%if pkgEn:
  import ${name}_pkg::*;
%endif

##TODO, section for parameter if needed

##interface signals
(

%for sig in clkIn["sig"]:
<%
  last = '' if loop.last and (not rstIn["sig"]) and (not sigIn["sig"]) and (not sigOut["sig"]) and (not sigInOut["sig"]) and (not sigBus["sig"]) else ','
%>\
  input wire ${wrapper_defs.packed_to_string(width_array=clkIn["info"][sig], packed_dim="")} ${sig}${last}
%endfor
%for sig in rstIn["sig"]:
<%
  last = '' if loop.last and (not sigIn["sig"]) and (not sigOut["sig"]) and (not sigInOut["sig"]) and (not sigBus["sig"]) else ','
%>\
  input wire ${wrapper_defs.packed_to_string(width_array=rstIn["info"][sig], packed_dim="")} ${sig}${last}
%endfor
%for sig in sigIn["sig"]:
<%
  last = '' if loop.last and (not sigOut["sig"]) and (not sigInOut["sig"]) and (not sigBus["sig"]) else ','
%>\
  input logic ${wrapper_defs.packed_to_string(width_array=sigIn["info"][sig], packed_dim="")} ${sig}${last}
%endfor
%for sig in sigOut["sig"]:
<%
  last = '' if loop.last and (not sigInOut["sig"]) and (not sigBus["sig"]) else ','
%>\
  output logic ${wrapper_defs.packed_to_string(width_array=sigOut["info"][sig], packed_dim="")} ${sig}${last}
%endfor
%for sig in sigInOut["sig"]:
<%
  last = '' if loop.last and (not sigBus["sig"]) else ','
%>\
  inout wire ${wrapper_defs.packed_to_string(width_array=sigInOut["info"][sig], packed_dim="")} ${sig}${last}
%endfor
%for sig in sigBus["sig"]:
<%
  last = '' if loop.last else ','
  dir = ""
  type = "logic"
  width = ""
  if "in" in sigBus["info"][sig]["dir"]:
    dir = "input"
  elif "out" in sigBus["info"][sig]["dir"]:
    dir = "output"
  else:
    dir = "inout"
  if dir == "inout":
    type = "wire"
  if sigBus["info"][sig]["dw"].endswith("_t"):
    type = ""
    width = sigBus["info"][sig]["dw"]
  else:
    width = wrapper_defs.packed_to_string(width_array=sigBus["info"][sig]["dw"], packed_dim="")
%>\
  ${dir} ${type} ${width} ${sig}${last}
%endfor

## start here inst, and connectivity
);

endmodule

