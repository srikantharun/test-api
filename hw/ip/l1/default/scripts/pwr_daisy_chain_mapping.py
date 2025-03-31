#!/usr/bin/env python3
import sys
import argparse

def mbank_to_cfg(idx, mbank):
    sbank = mbank%4
    minibank = mbank//4
    return f'{idx}: l1_pkg::mem_map_cfg_t\'{{sb:{sbank}, mb:{minibank}, m:0}}'

def main():
  parser = argparse.ArgumentParser(
      description='Generate daisy chain config for L1.')
  parser.add_argument('-ml',
                      '--mbank_list',
                      metavar='input',
                      type=str,
                      help='mbank list file; the mbank order as defined by PD, comma seperated.')

  args = parser.parse_args()

  idx=0
  mb_list=[]
  with open(args.mbank_list) as file:
    for l in file:
      mbanks = l.split(",")
      for mb in mbanks:
        mb = int(mb)
        if type(mb) is int:
          if mb in mb_list:
            print(f"ERROR: mbank {mb} already parsed! Each entry should be unique!")
            sys.exit(1)
            
          mb_list.append(mb)
          print(mbank_to_cfg(idx,mb))
          idx+=1

if __name__ == "__main__":
  main()
