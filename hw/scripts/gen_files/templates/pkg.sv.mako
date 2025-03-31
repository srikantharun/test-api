<%namespace name="wrapper_defs" file="wrapper_defs.mako"/>
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
##// Description: ${description}
##// Owner: ${owner} (${email})
<% defStr = f'{name}_pkg_sv'.upper() %>
`ifndef ${defStr}
`define ${defStr}

package ${name}_pkg;

%for para in sigPara:
  parameter ${para} = ${sigPara[para]};
%endfor

endpackage
`endif
