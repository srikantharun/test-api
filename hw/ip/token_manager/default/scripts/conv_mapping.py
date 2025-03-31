#!/usr/bin/env python3

import argparse
import os
import string
import sys
from math import ceil, log2

import pandas as pd

import cdef_print as cp
import hjson_print as hp
import pkg_print as pp


def get_amount(ctype, ckey, connections, top=0):
  return len(list(filter(lambda d: d[ctype] in ckey, connections))) + (0 if top else 1)

def get_amounts(ctype, clist, connections, top):
  amounts=list()
  max=0

  for ckey in clist:
    amount=get_amount(ctype, ckey, connections, top)
    amounts.append({ckey:amount})
    if amount>max:
      max = amount
  return (amounts, max)

def get_align(w):
  return int(pow(2, ceil(log2(w))))

def main():
  parser = argparse.ArgumentParser(
      description='Conversion script for the token mapping.')
  parser.add_argument('-l',
                      '--loc_mapping_csv',
                      metavar='input',
                      type=str,
                      help='Local token mapping file.')
  parser.add_argument('-t',
                      '--top_mapping_csv',
                      metavar='input',
                      type=str,
                      help='Top token mapping file.')
  parser.add_argument('-po',
                      '--pkg_out',
                      metavar='output file',
                      type=str,
                      default="out_pkg.sv",
                      help='Output path for the package')
  parser.add_argument('-ho',
                      '--hjson_out',
                      metavar='output file',
                      type=str,
                      default="out.hjson",
                      help='Output path for the hjson')
  parser.add_argument('-ip',
                      '--current_ip',
                      metavar='IP (AIC0/APU/SDMA0)',
                      type=str,
                      default="aic",
                      help='IP to generate it for.')
  parser.add_argument('-sw_only',
                      '--sw_endpoint_only',
                      action='store_true',
                      default=False,
                      help='Top network SW endpoint only')
#   parser.add_argument('-v',
#                       '--verbose',
#                       action='store_true',
#                       default=False,
#                       help='print extra debug messages')
  parser.add_argument('-w',
                      '--cntr_w',
                      type=int,
                      default=8,
                      help='Counter width')
  parser.add_argument('-tpw',
                      '--top_prod_cntr_w',
                      type=int,
                      default=8,
                      help='Counter width for producer at top network')
  parser.add_argument('-tcw',
                      '--top_cons_cntr_w',
                      type=int,
                      default=8,
                      help='Counter width for consumer at top network')
  parser.add_argument('-idw',
                      '--idw',
                      type=int,
                      default=7,
                      help='AXI ID width')

  args = parser.parse_args()

  csv_files = []
  dev_uid_map={}

  if (args.loc_mapping_csv):
    with open(args.loc_mapping_csv, 'r') as mapping_file:
      mapping_csv = pd.read_csv(mapping_file,index_col=0)
      csv_files.append({"mapping": mapping_csv, "top": 0, "file": args.loc_mapping_csv})
  if (args.top_mapping_csv):
    with open(args.top_mapping_csv, 'r') as top_mapping_file:
      top_mapping_csv = pd.read_csv(top_mapping_file,index_col=0)
      with open(args.top_mapping_csv.replace(".csv","_uid.lst"), 'r') as f_order:
        for line in f_order:
          l=line.rstrip().split(":")
          dev_uid_map[l[0]] = l[1]
        top_mapping_csv = top_mapping_csv[[l for l in dev_uid_map]]
      csv_files.append({"mapping": top_mapping_csv, "top": 1, "file": args.top_mapping_csv})

  ip_name = args.current_ip.rstrip(string.digits)

  hp_lines = []
  pkg_lines = [[],[],[],[]]
  r2h_lsb=0
  h2r_lsb=0


  hp_lines.append(hp.header(ip_name, idw=args.idw))
  pkg_lines[0].append(pp.header(ip_name))
  pkg_lines[1].append(['\n'])
  pkg_lines[1].append(pp.csr_idx_enum())
  print(f"Generating required token files for IP {args.current_ip}:")
  for cfg in csv_files:
    print(f"Parsing {cfg['file']}...")
    pkg_prefix="TOK_MGR_TOP" if cfg["top"] else "TOK_MGR"
    prod_connections = list()
    cons_connections = list()
    lsb_track = [] # track struct bit position in package, so we can use the vector as is.

    prod_filt     = filter(lambda d: "Unnamed" not in d, cfg["mapping"].columns)
    prod_top_filt = filter(lambda d: d.startswith(args.current_ip) or not cfg["top"], prod_filt)
    prod_list = list(prod_top_filt if cfg["top"] else prod_filt)

    cons_filt     = filter(lambda d: type(d) is str and "Unnamed" not in d, cfg["mapping"].index)
    cons_top_filt = filter(lambda d: d.startswith(args.current_ip) or not cfg["top"], cons_filt)
    cons_list = list(cons_top_filt if cfg["top"] else cons_filt)

    if(len(prod_list) != len(cons_list)):
      print("Consumer and produced list are not of the same size!")
      exit(1)

    conn_prod_list=[]
    conn_cons_list=[]

    # Construct mapping:
    for col in range(len(cfg["mapping"].columns)):
      prod = cfg["mapping"].columns[col]
      for key, row in cfg["mapping"].iterrows():
        cons = key
        if row.iloc[col] == "x":
          prod_tidx=get_amount("prod", prod, prod_connections, cfg["top"])
          cons_tidx=get_amount("cons", cons, cons_connections, cfg["top"])
          if (not cfg["top"]) or (prod in prod_list):
            prod_connections.append({"prod":prod,"cons":cons, "prod_idx": prod_tidx, "cons_idx": cons_tidx, "prod_nr": len(prod_connections)})
            # simple list to check what is connected:
            if cons not in conn_cons_list:
              conn_cons_list.append(cons)
          if (not cfg["top"]) or (cons in cons_list):
            cons_connections.append({"prod":prod,"cons":cons, "prod_idx": prod_tidx, "cons_idx": cons_tidx, "prod_nr": len(cons_connections)})
            # simple list to check what is connected:
            if prod not in conn_prod_list:
              conn_prod_list.append(prod)
    (prod_amounts, max_nr_prod)=get_amounts("prod", prod_list, prod_connections, cfg["top"])
    (cons_amounts, max_nr_cons)=get_amounts("cons", cons_list, cons_connections, cfg["top"])

    # for non top network we assume swep for all, not connected to current IP:
    if not cfg["top"]:
      conn_prod_list = prod_list
      conn_cons_list = cons_list

    # hjson for reggen:
    print(f" - Constructing hjson...")
    pref="TOP_" if cfg["top"] else ""
    cntr_prod_w = args.top_prod_cntr_w if cfg["top"] else args.cntr_w
    cntr_cons_w = args.top_cons_cntr_w if cfg["top"] else args.cntr_w

    if (not cfg["top"]) or args.sw_endpoint_only:
      lines = hp.swep("prod", conn_prod_list, get_align(cntr_prod_w), cntr_prod_w, pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"swep_prod", "amount": len(conn_prod_list), "r2h": cntr_prod_w+1, "h2r": cntr_prod_w})

      lines = hp.swep("cons", conn_cons_list, get_align(cntr_cons_w), cntr_cons_w, pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"swep_cons", "amount": len(conn_cons_list), "r2h": cntr_cons_w+2, "h2r": cntr_cons_w})

      lines = hp.irq_swep_status(list(conn_prod_list), "PROD_SAT", "saturation", "saturated", "prod", pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_swep_prod_sat", "amount": len(conn_prod_list), "r2h": 1, "h2r": 2})

      lines = hp.irq_swep_en(list(conn_prod_list), "PROD_SAT", "saturation", "saturated", "prod", pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_en_swep_prod_sat", "amount": len(conn_prod_list), "r2h": 1, "h2r": 0})

      lines = hp.irq_swep_status(list(conn_cons_list), "CONS_SAT", "saturation", "saturated", "cons", pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_swep_cons_sat", "amount": len(conn_cons_list), "r2h": 1, "h2r": 2})

      lines = hp.irq_swep_en(list(conn_cons_list), "CONS_SAT", "saturation", "saturated", "cons", pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_en_swep_cons_sat", "amount": len(conn_cons_list), "r2h": 1, "h2r": 0})

      lines = hp.irq_swep_status(list(conn_cons_list), "CONS_NON_ZERO", "non zero", "is non zero", "cons", pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_swep_cons_non_zero", "amount": len(conn_cons_list), "r2h": 1, "h2r": 2})

      lines = hp.irq_swep_en(list(conn_cons_list), "CONS_NON_ZERO", "non zero", "is non zero", "cons", pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_en_swep_cons_non_zero", "amount": len(conn_cons_list), "r2h": 1, "h2r": 0})
    else:
      lsb_track.append({"name": f"swep_prod", "amount": 0, "r2h": cntr_prod_w+1, "h2r": cntr_prod_w})
      lsb_track.append({"name": f"swep_cons", "amount":0, "r2h": cntr_cons_w+2, "h2r": cntr_cons_w})
      lsb_track.append({"name": f"irq_swep_prod_sat", "amount": 0, "r2h": 1, "h2r": 2})
      lsb_track.append({"name": f"irq_en_swep_prod_sat", "amount": 0, "r2h": 1, "h2r": 0})
      lsb_track.append({"name": f"irq_swep_cons_sat", "amount": 0, "r2h": 1, "h2r": 2})
      lsb_track.append({"name": f"irq_en_swep_cons_sat", "amount": 0, "r2h": 1, "h2r": 0})
      lsb_track.append({"name": f"irq_swep_cons_non_zero", "amount": 0, "r2h": 1, "h2r": 2})
      lsb_track.append({"name": f"irq_en_swep_cons_non_zero", "amount": 0, "r2h": 1, "h2r": 0})

    lines, fields = hp.irq_gen_status(prod_connections, prod_list, pref=pref, ctype="prod")
    hp_lines.append(lines)
    lsb_track.append({"name": f"irq_prod", "amount": fields, "r2h": 1, "h2r": 2})

    lines, fields = hp.irq_gen_en(prod_connections, prod_list, pref=pref, ctype="prod")
    hp_lines.append(lines)
    lsb_track.append({"name": f"irq_en_prod", "amount": fields, "r2h": 1, "h2r": 0})

    lines, fields = hp.gen_cnt(prod_connections, prod_list, get_align(cntr_prod_w), cntr_prod_w, pref=pref, ctype="prod")
    hp_lines.append(lines)
    lsb_track.append({"name": f"prod_cnt", "amount": fields, "r2h": 0, "h2r": cntr_prod_w})

    if cfg["top"]:
      lines, fields = hp.irq_gen_status(cons_connections, cons_list, pref=pref, ctype="cons")
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_cons", "amount": fields, "r2h": 1, "h2r": 2})

      lines, fields = hp.irq_gen_en(cons_connections, cons_list, pref=pref, ctype="cons")
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_en_cons", "amount": fields, "r2h": 1, "h2r": 0})

      lines, fields = hp.gen_cnt(cons_connections, cons_list, get_align(cntr_cons_w), cntr_cons_w, pref=pref, ctype="cons")
      hp_lines.append(lines)
      lsb_track.append({"name": f"cons_cnt", "amount": fields, "r2h": 0, "h2r": cntr_cons_w})

      lines = hp.irq_top_map(prod_list, pref=pref)
      hp_lines.append(lines)
      lsb_track.append({"name": f"irq_top_map", "amount": len(prod_list), "r2h": 1, "h2r": 2})
    else:
      lsb_track.append({"name": f"irq_cons", "amount": 0, "r2h": 1, "h2r": 2})
      lsb_track.append({"name": f"irq_en_cons", "amount": 0, "r2h": 1, "h2r": 0})
      lsb_track.append({"name": f"cons_cnt", "amount": 0, "r2h": 0, "h2r": cntr_cons_w})
      lsb_track.append({"name": f"irq_top_map", "amount": 0, "r2h": 1, "h2r": 2})

    # print package:
    print(f" - Constructing package...")
    pkg_lines[0].append([f"  parameter token_manager_pkg::tokmgr_cfg_t {pkg_prefix}_CFG = '{{\n"])
    pkg_lines[0].append([f"      present: 1'b1,\n"])
    pkg_lines[0].append([f"      max_num_prod: 32'd{max_nr_prod},\n"])
    pkg_lines[0].append([f"      max_num_cons: 32'd{max_nr_cons},\n"])
    pkg_lines[0].append([f"      nr_loc_devs:  32'd{len(prod_list)},\n"])
    pkg_lines[0].append([f"      nr_cntrs: 32'd{len(prod_connections)},\n"])
    pkg_lines[0].append([f"      prod_cntr_width: 32'd{cntr_prod_w},\n"])
    pkg_lines[0].append([f"      cons_cntr_width: 32'd{cntr_cons_w},\n"])
    pkg_lines[0].append([f"      loc_is_sw_only: 1'b{1 if args.sw_endpoint_only and cfg['top'] else 0}\n"])
    pkg_lines[0].append([f"  }};\n"])

    pkg_lines[1].append(["\n  // Array that can be used for the token manager port widths (vld/rdy):\n"])
    pkg_lines[1].append(pp.width_array("prod", prod_amounts, pref=pkg_prefix))
    pkg_lines[1].append(pp.width_array("cons", cons_amounts, pref=pkg_prefix))
    if not cfg["top"]:
      pkg_lines[1].append(["\n  // Token mapping array, from producer input to generic array:\n"])
      pkg_lines[1].append(pp.mapping("prod", prod_connections, prod_list, max_nr_prod, pref=pkg_prefix, to_str="GEN", top=cfg["top"]))
      pkg_lines[1].append(["\n  // Token mapping array, from generic array to consumer output:\n"])
      pkg_lines[1].append(pp.mapping("cons", cons_connections, cons_list, max_nr_cons, pref=pkg_prefix, to_str="GEN", top=cfg["top"]))

    if cfg["top"]:
      pkg_lines[1].append(["\n  // Dev id:\n"])
      pkg_lines[1].append(pp.dev_id(prod_list, dev_list=dev_uid_map, pref=pkg_prefix))
      pkg_lines[1].append(["\n  // Token mapping array, from producer input to top device:\n"])
      pkg_lines[1].append(pp.mapping("prod", prod_connections, prod_list, max_nr_prod, pref=pkg_prefix, dev_list=dev_uid_map, to_str="DEV", top=cfg["top"]))
      pkg_lines[1].append(["\n  // Token mapping array, from generic array to top device:\n"])
      pkg_lines[1].append(pp.mapping("cons", cons_connections, cons_list, max_nr_cons, pref=pkg_prefix, dev_list=dev_uid_map, to_str="DEV", top=cfg["top"]))

    pkg_lines[2].append(["\n  // For other devices, to get the token width:\n"])
    pkg_lines[2].append(pp.widths("prod", prod_amounts, pref=pkg_prefix))
    pkg_lines[2].append(pp.widths("cons", cons_amounts, pref=pkg_prefix))
    pkg_lines[2].append(["\n  // Device index for the token manager:\n"])
    pkg_lines[2].append(pp.dev_idx(prod_list, pref=pkg_prefix))
    if (not cfg["top"]) or args.sw_endpoint_only:
      pkg_lines[2].append(["\n  // Device index for the software endpoint:\n"])
      pkg_lines[2].append(pp.sw_ep_idx(cfg["mapping"].columns, prod_list, pref=pkg_prefix))
    pkg_lines[2].append(["\n  // Producer token mapping per device, what is connected (could be used for testbenches for example):\n"])
    pkg_lines[2].append(pp.dev_con_idx("prod", prod_connections, cons_list, cfg["top"], pref=pkg_prefix))
    pkg_lines[2].append(["\n  // Consumer token mapping per device, what is connected (could be used for testbenches for example):\n"])
    pkg_lines[2].append(pp.dev_con_idx("cons", cons_connections, cons_list, cfg["top"], pref=pkg_prefix))

    pkg_lines[1].append([f"  parameter token_manager_pkg::TokMgrCsrInfo_t {pref.upper()}TOK_MAN_CSR_INFO = '{{\n"])
    for idx, l in enumerate(lsb_track):
        comma = "," if idx<len(lsb_track)-1 else ""
        h2r_dw=l["amount"] * l["h2r"]
        r2h_dw=l["amount"] * l["r2h"]
        pkg_lines[1].append([f"    tok_{l['name'].lower()}_idx: '{{\n"])
        pkg_lines[1].append([f"      r2h_lsb:32'd{r2h_lsb},\n"])
        pkg_lines[1].append([f"      r2h_dw:32'd{r2h_dw},\n"])
        pkg_lines[1].append([f"      h2r_lsb:32'd{h2r_lsb},\n"])
        pkg_lines[1].append([f"      h2r_dw:32'd{h2r_dw}\n"])
        pkg_lines[1].append([f"    }}{comma}\n"])
        h2r_lsb+=h2r_dw
        r2h_lsb+=r2h_dw
    pkg_lines[1].append([f"  }};\n"])

  hp_lines.append(hp.footer())
  pkg_lines[3].append(pp.footer())

  print(f"Writing files...")
  with open(args.pkg_out, 'w') as fp_pkg:
    for section in pkg_lines:
      for l in section:
        fp_pkg.writelines(l)
  with open(args.hjson_out, 'w') as fp_hjson:
    for l in hp_lines:
      fp_hjson.writelines(l)

  print(f"All done!")
    # # Info:
    # print(f'## Token connections / headers')
    # print(f'### Producer header bitfields:')
    # prod=""
    # for c in sorted(prod_connections, key=lambda d: (prod_list.index(d['prod']), d['prod_idx'])):
    #   if c["prod"]!=prod:
    #     prod = c["prod"]
    #     print(f'\n{c["prod"]}:')
    #     print(f' - 0: SWendpoint')
    #   print(f' - {c["prod_idx"]}: {c["cons"]}')
    # print("")
    # print(f'### Consumer header bitfields:')
    # cons=""
    # for c in sorted(cons_connections, key=lambda d: (cons_list.index(d['cons']), d['cons_idx'])):
    #   if c["cons"]!=cons:
    #     cons = c["cons"]
    #     print(f'\n{c["cons"]}:')
    #     print(f' - 0: SWendpoint')
    #   print(f' - {c["cons_idx"]}: {c["prod"]}')
    # print(f'## SW endpoint counters')
    # print(f'\nProducer SWendpoint:')
    # for p in prod_list:
    #   print(f' - {list(cfg["mapping"].columns).index(p)}: {p}')
    # print(f'\nConsumer SWendpoint:')
    # for c in cons_list:
    #   print(f' - {list(cfg["mapping"].columns).index(c)}: {c}')

    # # cdefs:
    # cp.header()

    # print("// The amount of active producer token lines per device:")
    # cp.widths("prod", prod_amounts)
    # print("")
    # print("// The amount of active consumer token lines per device:")
    # cp.widths("cons", cons_amounts)

    # print("\n// Device index for the software endpoint:")
    # cp.sw_ep_idx(cfg["mapping"].columns, prod_list)

    # print("\n// Producer token mapping per device, what is connected to what bit idx:")
    # cp.dev_con_idx("prod", prod_connections, cons_list)

    # print("\n// Consumer token mapping per device, what is connected to what bit idx:")
    # cp.dev_con_idx("cons", cons_connections, cons_list)
    # cp.footer()

if __name__ == "__main__":
  exit_code = main()
  sys.exit(exit_code)
