#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: class for connecticity info
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
import re
from difflib import SequenceMatcher
from mako.template import Template
from mako.lookup import TemplateLookup

parser = argparse.ArgumentParser(
  description="arguments"
)
parser.add_argument(
  "-i", "--info", type=str, default=""
)
parser.add_argument(
  "-r", "--ratio", type=float, default=0.5
)

parser.add_argument(
  "-owner", "--owner", type=str, default="Axelera"
)

parser.add_argument(
  "-email", "--email", type=str, default="Axelera@axelera.ai"
)

class conn_info:
  conn_file_path = "" # path of the hjson containing connection info
  conn_info = {} # connection info
  ip_inst_info = {} # storage of all parameters related to the ip in mapping_info part
  inst_to_ip = {} # mapping between inst name to ip name
  inst_str_match_info = {} # expend sig matching info based on connection info
  inst_const_info = {} # signal assigned with const value

  def __init__(self, conn_file_path):
    self.conn_file_path = pathlib.Path(conn_file_path)
    if self.conn_file_path.exists():
      with self.conn_file_path.open() as file:
        self.conn_info = hjson.load(file)
    else:
      print("conn info source file (%s) does not exist!"%(str(conn_file_path)))
      sys.exit(1)
    self._get_ip_inst_info()
    self._check_info()
    self._get_ip_const_info()
    self._get_ip_conn_info()

  def _check_info(self):
    for ip in self.conn_info["mapping_info"]:
      ip_name = self.ip_inst_info[ip]["ip_name"]
      if ip_name not in self.conn_info["ip_info"]:
        print("ip (%s, %s) defined in mapping section is not defined in ip_info scetion!"%(ip, ip_name))
        sys.exit(1)

  def _get_ip_inst_info(self):
    for ip in self.conn_info["mapping_info"]:
      if ip not in self.ip_inst_info:
        self.ip_inst_info[ip] = {}
        self.ip_inst_info[ip]["param"] = {}
      self.ip_inst_info[ip]["inst"] = self.conn_info["mapping_info"][ip]["inst"]
      # ip inst name
      ip_name = ip
      ip_inst_suffix = ""
      # if the unique suffix is attached to ip inst name
      if "(" in ip and ")" in ip:
        ip_inst_suffix = f'_{ip.split("(")[-1].replace(")", "")}'
        ip_name = ip.split("(")[0]
      if int(self.ip_inst_info[ip]["inst"]) > 1:
        ip_inst_names = [f'u_{ip_name}{ip_inst_suffix}_{index}' for index in range(int(self.ip_inst_info[ip]["inst"]))]
      else:
        ip_inst_names = [f'u_{ip}']
      self.ip_inst_info[ip]["ip_name"] = ip_name ## use ip_name here not ip, for situation e.g. lpddr_p(graph) as a key in hjson file
      self.ip_inst_info[ip]["inst_names"] = ip_inst_names
      for inst_name in ip_inst_names:
        self.inst_to_ip[inst_name] = ip_name
      # store all parameters, not used yet
      for (key, value) in self.conn_info["mapping_info"][ip].items():
          if key.startswith("@"):
            self.ip_inst_info[ip]["param"][key] = value
    if self.conn_info["top"] not in self.inst_to_ip:
      self.inst_to_ip[self.conn_info["top"]] = self.conn_info["top"]

  def _get_ip_const_info(self):
    if self.conn_info["mapping_info"]:
      for ip in self.conn_info["mapping_info"]:
        if "const_info" in self.conn_info["mapping_info"][ip]:
          for const_item in self.conn_info["mapping_info"][ip]["const_info"].items():
            for ip_inst_idx in range(int(self.ip_inst_info[ip]["inst"])):
              ip_inst_name = self.ip_inst_info[ip]["inst_names"][ip_inst_idx]
              if ip_inst_name not in self.inst_const_info:
                self.inst_const_info[ip_inst_name] = {}
              sig_name = const_item[0]
              sig = const_item[1].replace("@inst",str(ip_inst_idx)).replace("[]","")
              match = re.search(r"\(([^)]+)\)", sig)
              if match:
                sig_value = match.group(1)
                try:
                  sig_value = str(eval(sig_value))
                  sig = re.sub(r"\([^)]+\)", sig_value, sig)
                except Exception as e:
                  print(f"Warning: Failed to evaluate '{sig_value}'")
              self.inst_const_info[ip_inst_name][sig_name] = sig

  def _get_ip_conn_info(self):
    if self.conn_info["mapping_info"]:
      for ip in self.conn_info["mapping_info"]:
        for pair_ip in self.conn_info["mapping_info"][ip]["pair_info"]:
          if self.conn_info["mapping_info"][ip]["pair_info"][pair_ip]:
            if pair_ip == self.conn_info["top"]:
              pair_ip_inst_name = [f'{self.conn_info["top"]}']
            else:
              pair_ip_inst_name = self.ip_inst_info[pair_ip]["inst_names"]
            for ip_inst_idx in range(int(self.ip_inst_info[ip]["inst"])):
              for pair_item in self.conn_info["mapping_info"][ip]["pair_info"][pair_ip].items():
                # TODO, assume pair IP inst is 1, more generic solution may needed
                # inst_str_match_info
                ip_inst_name = self.ip_inst_info[ip]["inst_names"][ip_inst_idx]
                if ip_inst_name not in self.inst_str_match_info:
                  self.inst_str_match_info[ip_inst_name] = {}
                sig_pattern = pair_item[0]
                pair_sig_pattern = pair_item[1].replace("@inst",str(ip_inst_idx)).split("[")[0]
                pair_sig_pattern_idx = pair_item[1].replace("@inst",str(ip_inst_idx))
                pair_sig_acc = True if pair_item[1].endswith("]") else False
                acc_content = re.findall(r'\[(.*?)\]', pair_sig_pattern_idx)[0] if pair_sig_acc else None# only one [ ] in the name pattern
                acc_idx = None
                if acc_content not in (None, ""):
                  try:
                    acc_idx = eval(acc_content)
                  except Exception as e:
                    print(f"Error evaluating the expression: {acc_content} for {pair_sig_pattern} of {pair_ip}")
                    sys.exit(1)
                self.inst_str_match_info[ip_inst_name][sig_pattern] = {}
                self.inst_str_match_info[ip_inst_name][sig_pattern]["pair_ip_inst"] = pair_ip_inst_name[0]
                self.inst_str_match_info[ip_inst_name][sig_pattern]["acc"] = pair_sig_acc
                self.inst_str_match_info[ip_inst_name][sig_pattern]["acc_idx"] = acc_idx
                self.inst_str_match_info[ip_inst_name][sig_pattern]["pair_sig_pattern"] = pair_sig_pattern

  def get_ip_info(self):
    return self.conn_info["ip_info"]

  #def get_mapping_ip(self):
  #  return list(self.conn_info["mapping_info"].keys())

  def get_all_ip_insts(self):
    inst_name_list = []
    for ip in self.ip_inst_info:
      inst_name_list += self.ip_inst_info[ip]["inst_names"]
    return inst_name_list

  def get_inst_pair(self, inst_name):
    re = []
    if inst_name in self.inst_str_match_info:
      re = self.inst_str_match_info[inst_name]
    return re

  def get_inst_const(self):
    return self.inst_const_info

  def get_pkg_info(self):
    re = []
    if self.conn_info["pkg_info"]:
      re = self.conn_info["pkg_info"]
    return re

  def get_localparam(self):
    re = None
    if "localparam" in self.conn_info:
      re = self.conn_info["localparam"]
    return re

  def get_ip_name_from_inst(self, inst_name):
    if inst_name not in self.inst_to_ip:
      print("inst name (%s) is not known"%(inst_name))
    return self.inst_to_ip[inst_name]

  def get_top_name(self):
    return self.conn_info["top"]

  def get_top_ports(self):
    return self.conn_info["top_ports"]

  def get_inst_to_ip_dict(self):
    return self.inst_to_ip

  def get_top_file_path(self):
    return self.conn_info["top_path"]
