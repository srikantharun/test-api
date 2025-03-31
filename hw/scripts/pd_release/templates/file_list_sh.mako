set search_path_initial $search_path

%if srcs:
%for src in srcs:
<%
  fileType = "sv" if src["file_type"] == "verilog" else "vhdl"
%>
set search_path $search_path_initial
%if src["incdirs"]:
%for inc in src["incdirs"]:
lappend search_path "${inc}"
%endfor
%endif
if {0 == [analyze -format ${fileType} ${'\\'}
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
    "${file}" ${'\\'}
%endfor
    }
%endif
]} {return 1}

%endfor
%endif
