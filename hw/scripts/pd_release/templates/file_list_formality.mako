set search_path_initial $search_path

%if srcs:
<% lib_type = "-r" if type=="ref" else "-i"%>\
%for src in srcs:
<%
  cmdType = "read_sverilog "+lib_type if src["file_type"] == "verilog" else "read_vhdl "+lib_type
%>
set search_path $search_path_initial
%if src["incdirs"]:
%for inc in src["incdirs"]:
lappend search_path "${inc}"
%endfor
%endif
if {0 == [${cmdType} ${'\\'}
%if src["file_type"] != "vhdl":
%if src["defines"]:
    -define {${'\\'}
%for define in src["defines"]:
<%
  key = define[0]
  value = f'={define[1]}' if define[1] else ""
%>\
      ${key}${value} ${'\\'}
%endfor
    } ${"\\"}
%endif
%endif
%if src["files"]:
    {
%for file in src["files"]:
<%pre_fix = ""
if (type=="impl" and not file.startswith("/")):
  pre_fix = "$@release_path_ini@/"
%>\
    "${pre_fix}${file}" ${'\\'}
%endfor
    }
%endif
]} {return 1}

%endfor
%endif
