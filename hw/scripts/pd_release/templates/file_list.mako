%if incDir:
%for dir in incDir:
+incdir+${incDir[dir]}
%endfor
%endif

%if defines:
%for define in defines:
<%
  name = define
  last = f"={defines[define]}" if defines[define] else ""
%>
+define+${name}${last}
%endfor
%endif

%if files:
%for file in files:
${file}
%endfor
%endif

