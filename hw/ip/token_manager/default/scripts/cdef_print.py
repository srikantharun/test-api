
def header():
  # Print out package:
  # header:
  print('// AUTO GENERATED, DON\'T MANUALLY EDIT!!\n\
// (C) Copyright Axelera AI 2021\n\
// All Rights Reserved\n\
// *** Axelera AI Confidential ***\n\
//\n\
// Description: Automatic generated defs file with info related to the tokens\n\
// Owner: scripts/conv_mapping.py\n\
\n\
#ifndef __TOKEN_MGR_DEFS_H__\n\
#define __TOKEN_MGR_DEFS_H__\n\
\n\
')

def widths(ctype, amounts):
  for d in amounts:
    for k in d:
      print(f'#define TOK_MGR_NR_{ctype.upper()}_{k.upper()} {d[k]}')

def sw_ep_idx(tot_list, clist):
  for idx, d in enumerate(tot_list):
    if d in clist:
      print(f'#define TOK_MGR_SW_EP_IDX_{d.upper()} {idx}')

def dev_con_idx(ctype, connections, clist):
  if ctype=="prod":
    otype = "cons"
  else:
    otype = "prod"
  for idx, pr in enumerate(clist):
    print(f'  //   {pr.upper()}:')
    res=list(filter(lambda d: d[ctype] in pr, connections))
    print(f'#define TOK_MGR_{pr.upper()}_{ctype.upper()}_SW_EP_IDX 0')
    for i, d in enumerate(res):
      # print(d)
      print(f'#define TOK_MGR_{pr.upper()}_{ctype.upper()}_{d[otype].upper()}_IDX {d[ctype+"_idx"]}')

def footer():
  print('\n\
#endif  //__TOKEN_MGR_DEFS_H__\n\
')
