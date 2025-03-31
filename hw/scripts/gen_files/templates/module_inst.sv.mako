<%sortedDict = dict(sorted(sigLinkedInfo.items()))%>
<%unConn = {}%>
%for moduleInst in sortedDict:
<%moduleName = ipInstMapping[moduleInst]%>\
<%unConn[moduleInst] = {}%>\
<%unConn[moduleInst]["in"] = []%>\
<%unConn[moduleInst]["out"] = []%>\
<%unConn[moduleInst]["inout"] = []%>\
<%moduleInstDef = moduleInst.replace("u_","",1).upper()+"_STUB"%>\
<%moduleStub = moduleName + "_stub"%>\
% if stub == "true":
`ifdef ${moduleInstDef}
${moduleStub} ${moduleInst} (
`else
${moduleName} ${moduleInst} (
`endif
% else:
${moduleName} ${moduleInst} (
% endif
% for sig in ipInterfaceInfo[moduleName]:
<%last = "" if loop.last else ","%>\
<%sig_unconn = ""%>\
% if sig in sigLinkedInfo[moduleInst]:
<% first_key = next(iter(sigLinkedInfo[moduleInst][sig]["wire"])) %>\
% if len(sigLinkedInfo[moduleInst][sig]["wire"]) == 1:
  .${sig} (${first_key})${last}
% else:
  .${sig} ({
% if "acc_fix" in sigLinkedInfo[moduleInst][sig] and sigLinkedInfo[moduleInst][sig]["acc_fix"]:
  ${sigLinkedInfo[moduleInst][sig]["acc_fix"]}'b0,
% endif
% for wire in sigLinkedInfo[moduleInst][sig]["wire"]:
%if wire.endswith("_unconn"):
<%sig_unconn = wire%>\
<%sigLinkedInfo[moduleInst][sig]["wire"].pop(wire)%>\
<%break%>\
%endif
% endfor
% if sig_unconn:
  ${sig_unconn},
% endif
<%
  sorted_sigLinkedInfo = sorted(sigLinkedInfo[moduleInst][sig]["wire"], reverse=True)
  if all(value is not None for value in sigLinkedInfo[moduleInst][sig]["wire"].values()):
    sorted_sigLinkedInfo = dict(sorted(sigLinkedInfo[moduleInst][sig]["wire"].items(), key=lambda item: item[1], reverse=True))
%>\
% for wire in sorted_sigLinkedInfo:
<% wire_last = "})," if loop.last else "," %>\
  ${wire}${wire_last}
% endfor
% endif
% elif moduleInst in sigConst:
% if sig in sigConst[moduleInst]:
  .${sig} (${sigConst[moduleInst][sig]})${last}
% else:
% if "input" in ipInterfaceInfo[moduleName][sig]["dir"]:
  .${sig} ('0)${last}
<%unConn[moduleInst]["in"].append(sig)%>\
% elif "output" in ipInterfaceInfo[moduleName][sig]["dir"]:
  .${sig} ()${last}
<%unConn[moduleInst]["out"].append(sig)%>\
% elif "inout" in ipInterfaceInfo[moduleName][sig]["dir"]:
  .${sig} ()${last}
<%unConn[moduleInst]["inout"].append(sig)%>\
% endif
% endif
% else:
% if "input" in ipInterfaceInfo[moduleName][sig]["dir"]:
  .${sig} ('0)${last}
<%unConn[moduleInst]["in"].append(sig)%>\
% elif "output" in ipInterfaceInfo[moduleName][sig]["dir"]:
  .${sig} ()${last}
<%unConn[moduleInst]["out"].append(sig)%>\
% elif "inout" in ipInterfaceInfo[moduleName][sig]["dir"]:
  .${sig} ()${last}
<%unConn[moduleInst]["inout"].append(sig)%>\
% endif
% endif
% endfor
);
% endfor

% for moduleInst in unConn:
<%print("***************")%>\
<%print(moduleInst)%>\
<%print("***************")%>\
<%print("---> input:")%>\
% for sig in unConn[moduleInst]["in"]:
<%print(sig)%>\
% endfor
<%print("<--- output:")%>\
% for sig in unConn[moduleInst]["out"]:
<%print(sig)%>\
% endfor
<%print("<---> inout:")%>\
% for sig in unConn[moduleInst]["inout"]:
<%print(sig)%>\
% endfor
% endfor
