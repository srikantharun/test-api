#!/usr/bin/env python3

# A simple pre-process script. Supporting:
# %%include:{file}

import argparse
import os
import re

gitRepo=os.environ['REPO_ROOT']

def parse_args():
    parser = argparse.ArgumentParser(
            description='Pre-process a (hjson) file')
    parser.add_argument('file', help='File to pre-process')
    parser.add_argument('-o','--output', help='output file')

    return parser.parse_args()

def get_file(file):
    with open(file) as f:
        lines = f.readlines()
    return lines

def pre_process_line(line=""):
    lines=[line]

    # take care of includes:
    if line.startswith("%%include:"):
        matches = re.findall('%%include:"(.*)"', line)
        if matches:
            incl_file=matches[0].replace("{REPO_ROOT}",gitRepo)
            incl_lines=get_file(incl_file)
            lines=incl_lines

    return lines

def pre_process_file(f):
    print("Pre process " + f)
    oup_lines=[]
    orig_lines=get_file(f)

    for l in orig_lines:
        ret_lines=pre_process_line(l)
        for rl in ret_lines:
            oup_lines.append(rl)
    
    return oup_lines

if __name__ == '__main__':
    args = parse_args()
    outp = pre_process_file(args.file)

    oup_file_name = args.file.replace("_pre","") if not args.output else args.output
    
    print("Writing out process file to "+oup_file_name)
    with open(f"{oup_file_name}", "w") as outfile:
        outfile.writelines(outp)

