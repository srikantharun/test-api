<%def name="packed_to_string(width_array, packed_dim)">\
%if isinstance(width_array, int):
%if width_array == 1:
  \
%else:
 [${width_array-1}:0]\
%endif
%elif isinstance(width_array,str):
%if width_array=="1":
 \
%else:
 [${width_array}-1:0]\
%endif
%elif width_array==[]:
 \
%elif len(width_array)==1:
  %if isinstance(width_array[0],str) and width_array[0].endswith("_t"):
 ${width_array[0]}\
  %else:
 ${width_array[0]}\
  %endif
%elif len(width_array)==2:
  %if isinstance(width_array[0],str) and 'pkg' in width_array[0]:
${width_array[0]}::${width_array[1]}\
  %else:
 [${width_array[0]}:${width_array[1]}]\
  %endif
%elif len(width_array)==3:
 [${width_array[0]}-${width_array[1]}:${width_array[2]}]\
%elif len(width_array)==4:
  %if 'pkg' in width_array[0]:
 [${width_array[0]}::${width_array[1]}-${width_array[2]}:${width_array[3]}]\
  %else:
 [${width_array[0]}/${width_array[1]}-${width_array[2]}:${width_array[3]}]\
  %endif
%elif len(width_array)==5:
 [${width_array[0]}-${width_array[1]}:${width_array[2]}][${width_array[3]}:${width_array[4]}]\
%elif len(width_array)>=6:
 ${packed_dim} \
%else:
  Error: Wrapper_defs.mako does not define what to do with packed dim of size ${len(width_array)}
%endif
</%def>

<%def name="unpacked_to_string(unpacked_array)">\
%if len(unpacked_array) == 0:
${''}\
%elif len(unpacked_array) == 1:
[${unpacked_array[0]}]\
%elif len(unpacked_array) == 2:
  %if 'pkg' in unpacked_array[0]:
[${unpacked_array[0]}::${unpacked_array[1]}]\
  %else:
[${unpacked_array[0]}-${unpacked_array[1]}]\
  %endif
%elif len(unpacked_array) == 3:
[${unpacked_array[0]}-${unpacked_array[1]}:${unpacked_array[2]}]\
%elif len(unpacked_array) == 4 and 'pkg' in unpacked_array[0]:
[${unpacked_array[0]}::${unpacked_array[1]}-${unpacked_array[2]}:${unpacked_array[3]}]\
%else:
  Error: Wrapper_defs.mako does not define what to do with unpacked dim of size ${len(unpacked_array)}
%endif
</%def>

<%def name="packed_value(width_array)">\
%if width_array==[]:
${'1'}\
%elif len(width_array)==1:
${width_array[0]}\
%elif len(width_array)==2:
${width_array[0]}\
%elif len(width_array)==3:
${width_array[0]}\
%elif len(width_array)==4:
  %if 'pkg' in width_array[0]:
${width_array[0]}::${width_array[1]}\
  %else:
${width_array[0]}/${width_array[1]}\
  %endif
%elif len(width_array)==5:
${width_array[0]}*${width_array[3]}:${width_array[4]}\
%else:
  Error: Wrapper_defs.mako does not define what to do with packed dim of size ${len(width_array)}
%endif
</%def>

<%def name="unpacked_to_dec(unpacked_array)">\
%if len(unpacked_array) == 0:
${'1'}\
%elif len(unpacked_array) == 1:
${unpacked_array[0]}\
%elif len(unpacked_array) == 2:
${unpacked_array[0]}-${unpacked_array[1]} + 1\
%elif len(unpacked_array) == 3:
${unpacked_array[0]}-${unpacked_array[1]}-${unpacked_array[2]} + 1\
%else:
  Error: Wrapper_defs.mako does not define what to do with unpacked dim of size ${len(unpacked_array)}
%endif
</%def>

<%def name="unpacked_to_idx(unpacked_array)">\
%if len(unpacked_array) == 0:
${''}\
%elif len(unpacked_array) == 1:
${'[i]'}\
%elif len(unpacked_array) == 2:
${'[i]'}\
%elif len(unpacked_array) == 3:
${'[i]'}\
%else:
  Error: Wrapper_defs.mako does not define what to do with unpacked dim of size ${len(unpacked_array)}
%endif
</%def>

<%def name="msb_lsb_to_idx_range(msb_idx, lsb_idx)">\
%if isinstance(msb_idx, int) and isinstance(lsb_idx, int):
%if msb_idx==-1 and lsb_idx==-1:
${''}\
%elif msb_idx==lsb_idx:
${'[' + str(msb_idx) + ']'}\
%else:
${'[' + str(msb_idx) + ':' + str(lsb_idx) + ']'}\
%endif
%else:
%if msb_idx==lsb_idx:
${'[' + msb_idx + ']'}\
%else:
${'[' + msb_idx + ':' + lsb_idx + ']'}\
%endif
%endif
</%def>
