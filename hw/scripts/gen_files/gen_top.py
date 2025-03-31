#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: top-level gen
# Owner: Luyi <yi.lu@axelera.ai>

import os
import sys
import argparse
import hjson
import subprocess
import csv
import pathlib
import math
import numbers
from difflib import SequenceMatcher
from mako.template import Template
from mako.lookup import TemplateLookup
from conn_info import conn_info
from inf_info import inf_info
from para_info import para_info
from protocol_info import protocol_info

parser = argparse.ArgumentParser(
  description="arguments"
)
parser.add_argument(
  "-i", "--info", type=str, default=""
)
parser.add_argument(
  "-r", "--ratio", type=float, default=1.0
)
parser.add_argument(
  "-p", "--protocol", type=str, default=""
)
parser.add_argument(
  "-owner", "--owner", type=str, default="Axelera"
)

parser.add_argument(
  "-email", "--email", type=str, default="Axelera@axelera.ai"
)

parser.add_argument(
  "-s", "--stub", type=str, default="false"
)

class gen_top:
  owner = "" # owner of the generated file
  email = "" # email of the owner for the generated file
  info_src = "" # path of the hjson file which contains: 0. top io signals, 1. ip file path, 2. ip inst connection info
  conn_info_obj = None
  para_info_obj = None
  inf_info_obj = None
  protocol_info_obj = None

  full_conn_info = {} #info of each signal's connection
  sig_link_info = {}  #info of all internal signals
  inter_sig_info = {} #all wires

  git_repo = ""
  temp_lookup = ""

  def __init__(self, info_src, protocol_src, owner, email, stub):
    self.owner = owner
    self.email = email
    self.stub = stub
    self.info_src = info_src
    self.git_repo = self._get_repo_top()
    self.temp_lookup = TemplateLookup(directories=[f'{self.git_repo}/hw/scripts/gen_files/templates'])

    # create protocol_info object
    self.protocol_info_obj = protocol_info(protocol_src)
    # create conn_info object
    self.conn_info_obj = conn_info(info_src)
    # create para_info object
    pkg_info = self.conn_info_obj.get_pkg_info()
    if pkg_info:
      pkg_info = [pkg.replace("{REPO_ROOT}", self.git_repo) for pkg in pkg_info]
    self.para_info_obj = para_info(pkg_info)
    # create inf_info object
    ip_info = self.conn_info_obj.get_ip_info()
    if ip_info:
      ip_info = {key : value.replace("{REPO_ROOT}", self.git_repo) for key, value in ip_info.items()}
    self.inf_info_obj = inf_info(ip_info, self.para_info_obj, self.protocol_info_obj)
    top_module = self.conn_info_obj.get_top_name()
    top_ports = self.conn_info_obj.get_top_ports()
    self.inf_info_obj.set_top_sig(top_module, top_ports)


  def _get_repo_top(self):
    return subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                          check=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip()

  def _find_sig_match(self, ip, ip_sig_list, ip_pattern, pair_ip, pair_ip_sig_list, pair_ip_pattern):
    top_module_name = self.conn_info_obj.get_top_name()
    pair_ip_is_top = True if pair_ip == top_module_name else False
    match_sig = []


    for ip_sig in ip_sig_list:
      ip_sig_dir = self.inf_info_obj.get_sig_dir(ip, ip_sig)
      sig_match_ratio = 0
      pair_sig_found = ""
      for pair_ip_sig in pair_ip_sig_list:
        pair_ip_sig_dir = self.inf_info_obj.get_sig_dir(pair_ip, pair_ip_sig)
        if not (("inout" in ip_sig_dir) and ("inout" in pair_ip_sig_dir)):
          if pair_ip_is_top:
            if pair_ip_sig_dir != ip_sig_dir:
              continue
          else:
            if pair_ip_sig_dir == ip_sig_dir:
              continue
        ip_sig_clean = ip_sig
        pair_ip_sig_clean = pair_ip_sig
        if ip_sig.startswith("i_"):
          ip_sig_clean = ip_sig[2:]
        elif ip_sig.startswith("o_"):
          ip_sig_clean = ip_sig[2:]
        elif ip_sig.startswith("io_"):
          ip_sig_clean = ip_sig[3:]
        if pair_ip_sig.startswith("i_"):
          pair_ip_sig_clean = pair_ip_sig[2:]
        elif pair_ip_sig.startswith("o_"):
          pair_ip_sig_clean = pair_ip_sig[2:]
        elif pair_ip_sig.startswith("io_"):
          pair_ip_sig_clean = pair_ip_sig[3:]

        ip_sig_clean = ip_sig_clean.replace(ip_pattern, "")
        pair_ip_sig_clean = pair_ip_sig_clean.replace(pair_ip_pattern, "")

        tempRatio = SequenceMatcher(None, ip_sig_clean.lower(), pair_ip_sig_clean.lower()).ratio()
        if tempRatio == 1.0:
          pair_sig_found = pair_ip_sig
      if not pair_sig_found:
        continue

      match_sig.append((ip_sig, pair_sig_found))
      if pair_ip_is_top:
        _, sig_width, _ = self.inf_info_obj.get_sig_width(ip, ip_sig)
        self.inf_info_obj.set_top_sig_width(pair_sig_found, sig_width)

      pair_ip_sig_list.remove(pair_sig_found)
    return match_sig

  def _acc_sig_width_admin(self, ip_inst, sig):
    conn_sig_resolved = []
    conn_sig_not_resolved = []
    conn_sig_full_resolved = True
    for sig_conn in self.full_conn_info[ip_inst][sig]["conn"]:
      conn_ip_inst = sig_conn.split(".")[0]
      conn_ip_sig = sig_conn.split(".")[-1]
      conn_ip_name = self.conn_info_obj.get_ip_name_from_inst(conn_ip_inst)
      width_resolved, width_update, packed_dim = self.inf_info_obj.get_sig_width(conn_ip_name, conn_ip_sig)
      if width_resolved:
        conn_sig_resolved.append(width_update)
      else:
        conn_sig_not_resolved.append(width_update)
        conn_sig_full_resolved = False
    # calculate the total width of all resolved width of these connection signals
    sum_all_resolved_width = sum([int(i) for i in conn_sig_resolved])
    sum_all_not_resolved_width = "+".join(conn_sig_not_resolved)
    # check info of ip
    ip_name = self.conn_info_obj.get_ip_name_from_inst(ip_inst)
    width_resolved, width_update, packed_dim = self.inf_info_obj.get_sig_width(ip_name, sig)
    sig_dir = self.inf_info_obj.get_sig_dir(ip_name, sig)
    sig_dir_type = self.inf_info_obj.get_sig_dir_type(ip_name, sig)
    if width_resolved and conn_sig_full_resolved:
      if sum_all_resolved_width > width_update:
        info = (ip_inst, sig, width_update, sum_all_resolved_width)
        self.report["acc_sig_mis"].append(info)
      if sum_all_resolved_width < width_update:
        self.sig_link_info[ip_inst][sig]["acc_fix"] = str(int(width_update) - sum_all_resolved_width)
        if sig_dir == "output" or sig_dir == "inout":
          inter_sig_name = f'{ip_inst}_{sig}_unconn'
          self.inter_sig_info[inter_sig_name] = {}
          self.inter_sig_info[inter_sig_name]["width"] = self.sig_link_info[ip_inst][sig]["acc_fix"]
          self.inter_sig_info[inter_sig_name]["packed_dim"] = self.sig_link_info[ip_inst][sig]["acc_fix"]
          self.inter_sig_info[inter_sig_name]["type"] = sig_dir_type
          self.sig_link_info[ip_inst][sig]["wire"][inter_sig_name] = -1
          self.sig_link_info[ip_inst][sig]["acc_fix"] = False

  def get_ip_conn_info(self):
    all_ip_inst_list = self.conn_info_obj.get_all_ip_insts()
    for ip_inst in all_ip_inst_list:
      ip_name = self.conn_info_obj.get_ip_name_from_inst(ip_inst)
      inst_pairs = self.conn_info_obj.get_inst_pair(ip_inst)
      for sig_pattern in inst_pairs:
        pair_ip_inst = inst_pairs[sig_pattern]["pair_ip_inst"]
        pair_ip_sig_pattern = inst_pairs[sig_pattern]["pair_sig_pattern"]
        pair_ip_sig_acc = inst_pairs[sig_pattern]["acc"]
        pair_ip_sig_acc_idx = inst_pairs[sig_pattern]["acc_idx"]
        pair_ip_name = self.conn_info_obj.get_ip_name_from_inst(pair_ip_inst)
        sig_pattern_list = self.inf_info_obj.get_pattern_sig_list(ip_name, sig_pattern)
        pair_sig_pattern_list = self.inf_info_obj.get_pattern_sig_list(pair_ip_name, pair_ip_sig_pattern)
        match_sigs = self._find_sig_match(ip_name, sig_pattern_list, sig_pattern, pair_ip_name, pair_sig_pattern_list, pair_ip_sig_pattern)
        for match_item in match_sigs:
          ip_sig = match_item[0]
          pair_ip_sig = match_item[1]
          ip_sig_full_name = f'{ip_inst}.{ip_sig}'
          pair_ip_sig_full_name = f'{pair_ip_inst}.{pair_ip_sig}'
          if ip_inst not in self.full_conn_info:
            self.full_conn_info[ip_inst] = {}
          if ip_sig not in self.full_conn_info[ip_inst]:
            self.full_conn_info[ip_inst][ip_sig] = {}
            self.full_conn_info[ip_inst][ip_sig]["dir"] = self.inf_info_obj.get_sig_dir(ip_name, ip_sig)
            self.full_conn_info[ip_inst][ip_sig]["acc"] = pair_ip_sig_acc if "output" in self.full_conn_info[ip_inst][ip_sig]["dir"] else False
            self.full_conn_info[ip_inst][ip_sig]["conn"] = {}
          self.full_conn_info[ip_inst][ip_sig]["conn"][pair_ip_sig_full_name] = {}
          self.full_conn_info[ip_inst][ip_sig]["conn"][pair_ip_sig_full_name]["dir"] = self.inf_info_obj.get_sig_dir(pair_ip_name, pair_ip_sig)
          self.full_conn_info[ip_inst][ip_sig]["conn"][pair_ip_sig_full_name]["acc_idx"] = pair_ip_sig_acc_idx
          if pair_ip_inst not in self.full_conn_info:
            self.full_conn_info[pair_ip_inst] = {}
          if pair_ip_sig not in self.full_conn_info[pair_ip_inst]:
            self.full_conn_info[pair_ip_inst][pair_ip_sig] = {}
            self.full_conn_info[pair_ip_inst][pair_ip_sig]["dir"] = self.inf_info_obj.get_sig_dir(pair_ip_name, pair_ip_sig)
            self.full_conn_info[pair_ip_inst][pair_ip_sig]["acc"] = pair_ip_sig_acc
            self.full_conn_info[pair_ip_inst][pair_ip_sig]["conn"] = {}
          if ip_sig_full_name not in self.full_conn_info[pair_ip_inst][pair_ip_sig]["conn"]:
            self.full_conn_info[pair_ip_inst][pair_ip_sig]["conn"][ip_sig_full_name] = {}
            self.full_conn_info[pair_ip_inst][pair_ip_sig]["conn"][ip_sig_full_name]["dir"] = self.inf_info_obj.get_sig_dir(ip_name, ip_sig)
            self.full_conn_info[pair_ip_inst][pair_ip_sig]["conn"][ip_sig_full_name]["acc_idx"] = pair_ip_sig_acc_idx

  def process_conn_info(self):
    ## use output signal of each ip to define the interconnect signals, and link to input of IP

    if self.full_conn_info:
      io_sig_skip = {}
      for ip_inst in self.full_conn_info:
        ip_is_top = True if ip_inst == self.conn_info_obj.get_top_name() else False
        ip_name = self.conn_info_obj.get_ip_name_from_inst(ip_inst)
        if ip_inst not in self.sig_link_info:
          self.sig_link_info[ip_inst] = {}
        inter_sig_name = ""
        for sig in self.full_conn_info[ip_inst]:
          if sig not in self.sig_link_info[ip_inst]:
            self.sig_link_info[ip_inst][sig] = {}
            self.sig_link_info[ip_inst][sig]["wire"] = {}
          if not ip_is_top:
            if "input" in self.full_conn_info[ip_inst][sig]["dir"]:
              continue
            elif "inout" in self.full_conn_info[ip_inst][sig]["dir"]:
              if ip_inst in io_sig_skip:
                if sig in io_sig_skip[ip_inst]:
                  continue
              else:
                if self.full_conn_info[ip_inst][sig]["acc"]:
                  io_sig_skip[ip_inst] = []
                  io_sig_skip[ip_inst].append(sig)
                  continue
                else:
                  pair_ip_inst_name = next(iter(self.full_conn_info[ip_inst][sig]["conn"])).split(".")[0]
                  pair_sig_name = next(iter(self.full_conn_info[ip_inst][sig]["conn"])).split(".")[-1]
                  if pair_ip_inst_name not in io_sig_skip:
                    io_sig_skip[pair_ip_inst_name] = []
                  if pair_sig_name not in io_sig_skip[pair_ip_inst_name]:
                    io_sig_skip[pair_ip_inst_name].append(pair_sig_name)
          else:
            if "output" in self.full_conn_info[ip_inst][sig]["dir"]:
              continue
          pair_ip_insts = [key.split(".")[0] for key in self.full_conn_info[ip_inst][sig]["conn"]]
          one_pair_ip_inst = True if ([pair_ip_insts[0]]*len(pair_ip_insts) == pair_ip_insts) else False
          for pair_sig_conn in self.full_conn_info[ip_inst][sig]["conn"]:
            pair_ip_inst_name = pair_sig_conn.split(".") [0]
            pair_ip_name = self.conn_info_obj.get_ip_name_from_inst(pair_ip_inst_name)
            pair_sig_name = pair_sig_conn.split(".")[-1]
            pair_ip_is_top = True if (pair_ip_inst_name == self.conn_info_obj.get_top_name()) else False
            pair_sig_acc_idx = self.full_conn_info[ip_inst][sig]["conn"][pair_sig_conn]["acc_idx"]
            sig_acc = self.full_conn_info[ip_inst][sig]["acc"]
            acc_idx_append = f"_{pair_sig_acc_idx}" if (pair_sig_acc_idx is not None) else ""
            if pair_ip_inst_name not in self.sig_link_info:
              self.sig_link_info[pair_ip_inst_name] = {}
            if pair_sig_name not in self.sig_link_info[pair_ip_inst_name]:
              self.sig_link_info[pair_ip_inst_name][pair_sig_name] = {}
              self.sig_link_info[pair_ip_inst_name][pair_sig_name]["wire"] = {}
            if ip_is_top:
              inter_sig_name = sig
            else:
              if pair_ip_is_top:
                inter_sig_name = pair_sig_name
              else:
                if one_pair_ip_inst:
                  inter_sig_name = f"{ip_inst}_to_{pair_ip_inst_name}__{sig}"
                  if sig_acc and len(self.full_conn_info[ip_inst][sig]["conn"])>1:
                    inter_sig_name = f"{ip_inst}_to_{pair_ip_inst_name}__{sig}__{pair_sig_name}{acc_idx_append}"
                else:
                  if not sig_acc:
                    inter_sig_name = f"{ip_inst}_to_multi__{sig}"
                  else:
                    inter_sig_name = f"{ip_inst}_to_{pair_ip_inst_name}__{sig}{acc_idx_append}"
            inter_sig_name = inter_sig_name.lower()
            if inter_sig_name not in self.sig_link_info[pair_ip_inst_name][pair_sig_name]["wire"]:
              self.sig_link_info[pair_ip_inst_name][pair_sig_name]["wire"][inter_sig_name] = pair_sig_acc_idx
            if inter_sig_name not in self.sig_link_info[ip_inst][sig]["wire"]:
              self.sig_link_info[ip_inst][sig]["wire"][inter_sig_name] = pair_sig_acc_idx

            if not ip_is_top and not pair_ip_is_top:
              if inter_sig_name not in self.inter_sig_info:

                ## TODO, need to handle situation that tar and dest are both split
                if self.full_conn_info[ip_inst][sig]["acc"] and len(self.full_conn_info[ip_inst][sig]["conn"])>1:
                  resolved, width_update, packed_dim = self.inf_info_obj.get_sig_width(pair_ip_name, pair_sig_name)
                else:
                  resolved, width_update, packed_dim = self.inf_info_obj.get_sig_width(ip_name, sig)
                sig_dir_type = self.inf_info_obj.get_sig_dir_type(ip_name, sig)
                self.inter_sig_info[inter_sig_name] = {}
                self.inter_sig_info[inter_sig_name]["width"] = width_update
                self.inter_sig_info[inter_sig_name]["packed_dim"] = packed_dim
                self.inter_sig_info[inter_sig_name]["type"] = sig_dir_type

      for ip_inst in self.full_conn_info:
        for sig in self.full_conn_info[ip_inst]:
          if self.full_conn_info[ip_inst][sig]["acc"] and len(self.full_conn_info[ip_inst][sig]["conn"])>1:
            self._acc_sig_width_admin(ip_inst, sig)

      if self.conn_info_obj.get_top_name() in self.sig_link_info:
        del self.sig_link_info[self.conn_info_obj.get_top_name()]

  def topRender(self):
    cfg = {}
    cfg["owner"] = self.owner
    cfg["email"] = self.email
    cfg["stub"] = self.stub
    cfg["moduleName"] = self.conn_info_obj.get_top_name()
    cfg["localparam"] = self.conn_info_obj.get_localparam()
    cfg["internalSig"] = self.inter_sig_info
    cfg["sigLinkedInfo"] = self.sig_link_info
    cfg["ipInstMapping"] = self.conn_info_obj.get_inst_to_ip_dict()
    cfg["sigConst"] = self.conn_info_obj.get_inst_const()
    cfg["ipInterfaceInfo"] = self.inf_info_obj.get_inf_info()
    cfg["imports"] = self.inf_info_obj.get_imports()
    cfg["topInf"] = self.inf_info_obj.get_top_info()

    t = Template(f"<%include file='module.sv.mako'/>",lookup=self.temp_lookup)
    renderedOut = t.render(**cfg)
    # write to file
    filePath = self.conn_info_obj.get_top_file_path().replace("{REPO_ROOT}", self.git_repo)
    with open(filePath, 'wb') as file:
      file.write(renderedOut.encode())

  def printDatabase(self):
    print("@@@@ ipInterfaceInfo @@@@")
    print(self.ipInterfaceInfo)
    print("@@@@ ipInstInfo @@@@")
    print(self.ipInstInfo)
    print("@@@@ sigFullConnInfo @@@@")
    print(self.sigFullConnInfo)
    print("@@@@ interSigInfo @@@@")
    print(self.interSigInfo)
    print("@@@@ sigLinkedInfo @@@@")
    print(self.sigLinkedInfo)

def main():
  args = parser.parse_args()
  info_src = args.info
  protocol_src = args.protocol
  ratio = args.ratio
  owner = args.owner
  email = args.email
  stub = args.stub


  top = gen_top(info_src, protocol_src, owner, email, stub)
  top.get_ip_conn_info()
  top.process_conn_info()
  top.topRender()
  #top.printDatabase()

if __name__ == "__main__":
  main()
