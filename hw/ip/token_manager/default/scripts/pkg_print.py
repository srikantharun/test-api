
def str_conv(str):
  return str.upper().replace("-","_")

def header(ip="aic"):
  lines=[]
  # lines.append out package:
  # header:
  lines.append(f'// AUTO GENERATED, DON\'T MANUALLY EDIT!!\n\
// (C) Copyright Axelera AI 2024\n\
// All Rights Reserved\n\
// *** Axelera AI Confidential ***\n\
//\n\
// Description: Automatic generated package with mapping for token mgr\n\
// Owner: scripts/conv_mapping.py\n\
\n\
\n\
package token_mgr_mapping_{ip.lower()}_pkg;\n\
\n')
  return lines

def csr_idx_enum():
  lines=[f"\
  // anoying requirement for spylgass, redeclare indexes...\n\
  typedef enum int {{\n\
    tok_swep_prod_idx = token_manager_pkg::swep_prod_idx,\n\
    tok_swep_cons_idx = token_manager_pkg::swep_cons_idx,\n\
    tok_irq_swep_prod_sat_idx = token_manager_pkg::irq_swep_prod_sat_idx,\n\
    tok_irq_en_swep_prod_sat_idx = token_manager_pkg::irq_en_swep_prod_sat_idx,\n\
    tok_irq_swep_cons_sat_idx = token_manager_pkg::irq_swep_cons_sat_idx,\n\
    tok_irq_en_swep_cons_sat_idx = token_manager_pkg::irq_en_swep_cons_sat_idx,\n\
    tok_irq_swep_cons_non_zero_idx = token_manager_pkg::irq_swep_cons_non_zero_idx,\n\
    tok_irq_en_swep_cons_non_zero_idx = token_manager_pkg::irq_en_swep_cons_non_zero_idx,\n\
    tok_irq_prod_idx = token_manager_pkg::irq_prod_idx,\n\
    tok_irq_en_prod_idx = token_manager_pkg::irq_en_prod_idx,\n\
    tok_prod_cnt_idx = token_manager_pkg::prod_cnt_idx,\n\
    tok_irq_cons_idx = token_manager_pkg::irq_cons_idx,\n\
    tok_irq_en_cons_idx = token_manager_pkg::irq_en_cons_idx,\n\
    tok_cons_cnt_idx = token_manager_pkg::cons_cnt_idx,\n\
    tok_irq_top_map_idx = token_manager_pkg::irq_top_map_idx\n\
  }} tok_mgr_csr_sel_e;\n\n"]
  return lines

def widths(ctype, amounts, pref="", postf=""):
  lines=[]
  for d in amounts:
    for k in d:
      lines.append(f'  parameter int unsigned {pref}_{str_conv(k)}_NR_TOK_{str_conv(ctype)}{postf} = 32\'d{d[k]};\n')
  return lines

def width_array(ctype, amounts, pref=""):
  lines=[]
  str=f'  parameter int {pref}_DEV_{str_conv(ctype)}_WIDTH[{pref}_CFG.nr_loc_devs] = \'{{'
  for i, d in enumerate(amounts):
    for k in d:
      if(i!=0):
        str=f'{str},'
      if (i%12==11): # add a line break after a few:
        str=f'{str}\n   '
      str=f'{str} 32\'d{d[k]}'
  lines.append(f'{str}}};\n')
  return lines

def dev_idx(clist, pref=""):
  lines=[]
  for idx, d in enumerate(clist):
    lines.append(f'  parameter int unsigned {pref}_{str_conv(d)}_DEV_IDX = 32\'d{idx};\n')
  return lines

def sw_ep_idx(tot_list, clist, pref=""):
  lines=[]
  for idx, d in enumerate(tot_list):
    if d in clist:
      lines.append(f'  parameter int unsigned {pref}_{str_conv(d)}_SW_EP_IDX = 32\'d{idx};\n')
  return lines

def dev_id(clist, dev_list=-1, pref=""):
  lines=[]
  lines.append(f'  parameter int {pref}_DEV_ID[{pref}_CFG.nr_loc_devs] = \'{{')
  for idx, pr in enumerate(clist):
    if(idx!=0):
      lines.append(', ')
    lines.append(f"32'd{dev_list[pr]}")
  lines.append("};\n")
  return lines

def mapping(ctype, connections, clist, max_w, pref="", dev_list=0, to_str="", top=0):
  lines=[]
  otype = "cons" if ctype=="prod" else "prod"

  max_w = max_w - 1 if not top else max_w # compensate for the SWEP not being defined for non tops

  str=f'  parameter int {pref}_{str_conv(ctype)}_TO_{to_str}[{pref}_CFG.nr_loc_devs][{pref}_CFG.max_num_{ctype}{"-1" if not top else ""}] = \'{{'
  for idx, pr in enumerate(clist):
    res=list(filter(lambda d: d[ctype] in pr, connections))
    # if len(res) > 0:
    str=f'{str}\n      \'{{'
    i=0
    for i, d in enumerate(res):
      if(i!=0):
        str=f'{str},'
      val = dev_list[d[otype]] if dev_list and top else d["prod_nr"]
      if (i%12==11): # add a line break after a few:
        str=f'{str}\n   '
      str=f'{str} 32\'d{val}'
    for n in range((max_w) - len(res)):
      if(len(res)>0 or n !=0):
        str=f'{str},'
      if ((i+n)%12==11): # add a line break after a few:
        str=f'{str}\n   '
      str=f'{str} -32\'d1'
    str=f'{str}}}'
    if(idx<len(clist)-1):
       str=f'{str},'
  lines.append(f'{str}\n  }};\n')
  return lines

def dev_con_idx(ctype, connections, clist, top=0, pref=""):
  lines=[]
  if ctype=="prod":
    otype = "cons"
  else:
    otype = "prod"
  for idx, pr in enumerate(clist):
    lines.append(f'  //   {str_conv(pr)}:\n')
    res=list(filter(lambda d: d[ctype] in pr, connections))
    if not top:
      lines.append(f'  parameter int unsigned {pref}_{str_conv(pr)}_TOK_{str_conv(ctype)}_SW_EP_IDX = 0;\n')
    for i, d in enumerate(res):
      # lines.append(d)
      lines.append(f'  parameter int unsigned {pref}_{str_conv(pr)}_TOK_{str_conv(ctype)}_{str_conv(d[otype])}_IDX = {d[ctype+"_idx"]};\n')
  return lines

def footer():
  lines=[]
  lines.append('\n\
endpackage\n\
\n')
  return lines
