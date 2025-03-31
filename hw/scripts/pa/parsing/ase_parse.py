#!/usr/bin/env python3

import argparse
import glob
import os
import re
import sys

CWD = os.getcwd()
script_dir=os.path.dirname(os.path.realpath(__file__))

def frm(f):
  if os.path.exists(f):
    os.remove(f)

def main():
  parser = argparse.ArgumentParser(
      description='Report ungated flops after qsyn.')
  parser.add_argument('-v',
                      '--verbose',
                      action='store_true',
                      default=False,
                      help="Verbose")
  parser.add_argument('-t',
                      '--threshold',
                      default=3,
                      type=int,
                      help='Only report vector if wider then this value')
  parser.add_argument('-o',
                       '--output_dir',
                       type=str,
                       default=f"{CWD}/parsed_reports",
                       help="Output directory for the parse reports")
  parser.add_argument('-b',
                       '--build_dir',
                       type=str,
                       default=f"{CWD}/report",
                       help="Build directory of the PowerArtist run")

  args = parser.parse_args()

  rpt_fns = glob.glob(f"{args.build_dir}/report/*_static_efficiency_detailed.rpt")

  for rpt_fn in rpt_fns:
    if not os.path.isfile(rpt_fn):
      print("ERROR! Report %s not present!" % (rpt_fn))
      sys.exit(1)
    try:
      f = open(rpt_fn, 'r')
    except:
      print("Can't open %s, skipping it" % rpt_fn)
      sys.exit(1)

    ip=rpt_fn.split('/')[-1].split('_static_efficiency_detailed')[0]
    file=f.readlines()
    f.close()

    in_section=0
    summary=list()
    all_vect_flops=list()
    tied_one_flops=list()
    ungated_mems=list()
    tied_one_mems=list()
    tied_zero_mems=list()
    for line in file:
      # Section checking
      if "1. Summary" in line:
        in_section="1"
      if "2. Detailed" in line:
        in_section="2"
      m = re.search("(2.\d+) (Registers|Instantiated|Ungated|Untraced|Memories|Unregistered)", line)
      if m:
        in_section = m[1]

      if in_section=="1": # summary
        summary.append(line)
      elif in_section=="2.1": # tied high
        path_pat="(\d+)\s+(\d+)\s+(\d+)\s+(.+)#r\d+\s+\/(.+)"
        match=re.search(path_pat, line)

        if(match):
          f = dict()
          f["amount"] = int(match[2])
          f["path"] = match[5]
          tied_one_flops.append(f)
      elif in_section=="2.7": # ungated
        path_pat="(\d+)\s+(.+)#r\d+\s+\/(.+)"
        match=re.search(path_pat, line)

        if(match):
          f = dict()
          f["amount"] = int(match[1])
          f["path"] = match[3]
          all_vect_flops.append(f)
      elif in_section=="2.9": # ungated memories
        path_pat="(\w+\/.+)\s+(.+)"
        match=re.search(path_pat, line)

        if(match):
          f = dict()
          f["path"] = match[1]
          ungated_mems.append(f)
      elif in_section=="2.10": # mem tied high enables
        path_pat="(\w+\/.+)\s+(.+)"
        match=re.search(path_pat, line)

        if(match):
          f = dict()
          f["path"] = match[1]
          f["clk_en"] = match[2]
          tied_one_mems.append(f)
      elif in_section=="2.11": # mem tied low enables
        path_pat="(\w+\/.+)\s+(.+)"
        match=re.search(path_pat, line)

        if(match):
          f = dict()
          f["path"] = match[1]
          f["clk_en"] = match[2]
          tied_zero_mems.append(f)

    rep_paths = [p for p in all_vect_flops if p['amount'] >= args.threshold]
    pr_arr=list()
    pr_arr.append(f"Ungated flops (with threshold {args.threshold}):\n")
    pr_arr.append(f"======================================\n")
    for rp in sorted(rep_paths, key=lambda x: (x['amount'], x['path']),reverse=True):
      pr_arr.append(f"{rp['amount']}:\t{rp['path']}\n")
    pr_arr.append(f"===================================\n")
    pr_arr.append(f"Total:          {sum(item['amount'] for item in all_vect_flops)}\n")
    pr_arr.append(f"Total filtered: {sum(item['amount'] for item in rep_paths)}\n")

    hier=dict()
    for p in all_vect_flops:
      c = dict()
      sp=p["path"].split('/')
      c["level"] = len(sp)-1
      c["path"] = sp[:-1]
      c["reg"] = sp[-1]
      c["amount"] = p["amount"]
      for i, sub_p in enumerate(c["path"]):
        cp='/'.join(c["path"][0:i+1])
        hier[cp]=c["amount"] + (0 if cp not in hier else hier[cp])

    RED='\033[1;31m'
    NC='\033[0m' # No Color

    print("Results:")
    print(f" Ungated flops (with threshold {args.threshold}):\t{sum(item['amount'] for item in rep_paths)}")
    print(f" Ungated flops (without threshold {args.threshold}):\t{sum(item['amount'] for item in all_vect_flops)}")
    print(f" Flops with enabled tied to 1:\t\t{sum(item['amount'] for item in tied_one_flops)}")
    print(f" Memories with enabled tied to 1:\t{len(tied_one_mems)}")
    print(f" Memories with enabled tied to 0:\t{len(tied_zero_mems)}")
    print(f" Memories with ungated clock:\t\t{len(ungated_mems)}")

    print(f"\nReports written to: {args.output_dir}")

    res_fn = f"{args.output_dir}/summary.{ip}.rpt"
    frm(res_fn)
    print(f" - summary.{ip}.rpt")
    f = open(res_fn, 'w')
    f.writelines(summary)
    f.close()

    res_fn = f"{args.output_dir}/ungated_flops.{ip}.rpt"
    frm(res_fn)
    print(f" - ungated_flops.{ip}.rpt")
    f = open(res_fn, 'w')
    f.writelines(pr_arr)
    f.close()

    res_fn = f"{args.output_dir}/ungated_flops.hier.{ip}.rpt"
    pr_arr = [f"{p}: {hier[p]}\n" for p in hier.keys()]
    frm(res_fn)
    print(f" - ungated_flops.hier.{ip}.rpt")
    f = open(res_fn, 'w')
    f.writelines(pr_arr)
    f.close()

    res_fn = f"{args.output_dir}/tied_one_flops.{ip}.rpt"
    frm(res_fn)
    if len(tied_one_flops) > 0:
      pr_pre=list()
      pr_pre.append(f"Flops with enable tied to 1:\n")
      pr_pre.append(f"============================\n")
      pr_arr = [f"{p['amount']}:\t{p['path']}\n" for p in  sorted(tied_one_flops, key=lambda x: x['amount'], reverse=True)]
      print(f" - {RED}tied_one_flops.{ip}.rpt{NC}")
      f = open(res_fn, 'w')
      f.writelines(pr_pre+pr_arr)
      f.close()

    res_fn = f"{args.output_dir}/ungated_mems.{ip}.rpt"
    frm(res_fn)
    if len(ungated_mems) > 0:
      pr_pre=list()
      pr_pre.append(f"Memories with ungated clock:\n")
      pr_pre.append(f"============================\n")
      pr_arr = [f"{p['path']}\n" for p in ungated_mems]
      print(f" - ungated_mems.{ip}.rpt")
      f = open(res_fn, 'w')
      f.writelines(pr_pre+pr_arr)
      f.close()

    res_fn = f"{args.output_dir}/tied_1_mems.{ip}.rpt"
    frm(res_fn)
    if len(tied_one_mems) > 0:
      pr_pre=list()
      pr_pre.append(f"Memories with enabled tied to one:\n")
      pr_pre.append(f"============================\n")
      pr_arr = [f"{p['path']}\n" for p in tied_one_mems]
      print(f" - {RED}tied_1_mems.{ip}.rpt{NC}")
      f = open(res_fn, 'w')
      f.writelines(pr_pre+pr_arr)
      f.close()

    res_fn = f"{args.output_dir}/tied_0_mems.{ip}.rpt"
    frm(res_fn)
    if len(tied_zero_mems) > 0:
      pr_pre=list()
      pr_pre.append(f"Memories with enabled tied to zero:\n")
      pr_pre.append(f"============================\n")
      pr_arr = [f"{p['path']}\n" for p in tied_zero_mems]
      print(f" - tied_0_mems.{ip}.rpt")
      f = open(res_fn, 'w')
      f.writelines(pr_pre+pr_arr)
      f.close()

    res_fn = f"{args.output_dir}/table_summary.{ip}.rpt"
    frm(res_fn)
    l = list()
    l.append(f"| ip | ungated flops | ungated flops >= {args.threshold} | tied 1 flops | tied 1 mems |\n")
    l.append(f"| {ip} | {sum(item['amount'] for item in all_vect_flops)} | {sum(item['amount'] for item in rep_paths)} | {sum(item['amount'] for item in tied_one_flops)} | {len(tied_one_mems)}\n")
    f = open(res_fn, 'w')
    f.writelines(l)
    f.close()

if __name__ == "__main__":
  exit_code = main()
  sys.exit(exit_code)
