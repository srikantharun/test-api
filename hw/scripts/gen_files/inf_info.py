#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Class for IP interface related
# Owner: Luyi <yi.lu@axelera.ai>

import os
import sys
import hjson
import subprocess
import pathlib
import math
import numbers

class inf_info:
  ip_inf_info = {}  # interface info of the IP
  ip_imports = []   # all imports of the IP
  top_name = ""
  para_info_obj = None  # parameter info
  protocol_info_obj = None
  report = {} # info to report, detail data struct in __init__
  gitRepo = ""

  def __init__(self, ip_info, para_info_obj, protocol_info_obj):
    self.para_info_obj = para_info_obj
    self.protocol_info_obj = protocol_info_obj
    typedef_info = self.para_info_obj.get_typedef_info()
    for ip in ip_info:
      ip_file_path = pathlib.Path(ip_info[ip])
      print(ip_file_path)
      ip_name_from_path = ip_info[ip].split("/")[-1].replace(".sv", "")
      if ip != ip_name_from_path:
        print("ip name (%s) does not match ip name (%s) abstract from the .sv file"%(ip, ip_name_from_path))
        sys.exit(1)
      if ip_file_path.exists():
        # replace typedef
        new_lines = []
        with ip_file_path.open() as file:
          for line in file:
            for type_name in typedef_info:
              if f"{type_name}" in line:
                line = line.replace(f" {typedef_info[type_name]['pkg']}::{type_name} ", f" {typedef_info[type_name]['value']} ").replace(f" {type_name} ", f" {typedef_info[type_name]['value']} ")
                break
            new_lines.append(line)
        ip_file_path_mo = f"{ip_file_path.resolve()}_mo"
        with open(ip_file_path_mo, "w") as file:
          file.writelines(new_lines)
        #subprocess.check_output("verible_syntax_mo.py -c " + str(ip_file_path.resolve()), shell=True)
        verible_path = pathlib.Path(__file__).parent / "verible_syntax_mo.py"
        subprocess.check_output(f"{verible_path.resolve()} -c {ip_file_path_mo}", shell=True)
        ip_json = str(ip_file_path_mo) + ".hjson"
        with open(ip_json) as file:
          ip_json_cont = hjson.load(file)
          self.ip_inf_info[ip] = ip_json_cont[ip]
        self.ip_imports += self.ip_inf_info[ip]["imports"]
      else:
        print("info source file does not exist!")
        sys.exit(1)
    self.ip_imports = list(set(self.ip_imports))
    self._update_sig_width()

  def _update_sig_width(self):
    for ip in self.ip_inf_info:
      for sig in self.ip_inf_info[ip]["ports"]["misc"]:
        width_info = self.ip_inf_info[ip]["ports"]["misc"][sig]["width"]
        width_resolved, width_update = self.para_info_obj.update_param(width_info)
        self.ip_inf_info[ip]["ports"]["misc"][sig]["width_update"] = width_update
        self.ip_inf_info[ip]["ports"]["misc"][sig]["resolved"] = width_resolved

  def set_top_sig(self, top_name, top_ports):
    self.top_name = top_name
    if top_name not in self.ip_inf_info:
      self.ip_inf_info[top_name] = {}
      self.ip_inf_info[top_name]["ports"] = {}
      self.ip_inf_info[top_name]["ports"]["misc"] = {}
      for sig in top_ports:
        if any(item in top_ports[sig] for item in ["input", "output", "inout"]):
          self.ip_inf_info[top_name]["ports"]["misc"][sig] = {}
          sig_dir = top_ports[sig].split("@")
          dir_type = ""
          if "inout" in top_ports[sig] and "wire" not in top_ports[sig]:
            dir_type = "wire"
          elif "wire" not in top_ports[sig]:
            dir_type = "logic"
          self.ip_inf_info[top_name]["ports"]["misc"][sig]["dir"] = f'{sig_dir[0]} {dir_type}'
          if "@" in top_ports[sig]:
            self.ip_inf_info[top_name]["ports"]["misc"][sig]["width"] = sig_dir[1]
            self.ip_inf_info[top_name]["ports"]["misc"][sig]["width_update"] = sig_dir[1]
          else:
            self.ip_inf_info[top_name]["ports"]["misc"][sig]["width"] = "UNKNOW" # actual value will be from the connection pair
        else: # for protocol
          sig_dict = self.protocol_info_obj.get_protocol_info(top_ports[sig])
          for protocol_sig in sig_dict:
            sig_prefix = "i_" if "input" in sig_dict[protocol_sig] else "o_"
            sig_name = f'{sig_prefix}{sig}_{protocol_sig}'
            self.ip_inf_info[top_name]["ports"]["misc"][sig_name] = {}
            self.ip_inf_info[top_name]["ports"]["misc"][sig_name]["dir"] = sig_dict[protocol_sig]
            self.ip_inf_info[top_name]["ports"]["misc"][sig_name]["width"] = "UNKNOW"

  def set_top_sig_width(self, sig_name, width ):
    self.ip_inf_info[self.top_name]["ports"]["misc"][sig_name]["width"] = width
    self.ip_inf_info[self.top_name]["ports"]["misc"][sig_name]["width_update"] = width

  def get_sig_width(self, ip_name, sig_name):
    if sig_name not in self.ip_inf_info[ip_name]["ports"]["misc"]:
      print("sig name (%s) does not exist!"%sig_name)
      sys.exit(1)
    else:
      try:
        resolved = self.ip_inf_info[ip_name]["ports"]["misc"][sig_name]["resolved"]
      except KeyError:
        print("Warning! -> Data width of %s in %s is not resolved!"%(sig_name, ip_name))
        sys.exit(1)
      width_update = self.ip_inf_info[ip_name]["ports"]["misc"][sig_name]["width_update"]
      packed_dim = self.ip_inf_info[ip_name]["ports"]["misc"][sig_name]["packed_dim"]
      return resolved, width_update, packed_dim

  def get_sig_dir(self, ip_name, sig_name):
    if sig_name not in self.ip_inf_info[ip_name]["ports"]["misc"]:
      print("sig name (%s) does not exist!"%sig_name)
      sys.exit(1)
    else:
      dir = "input"
      if "output" in self.ip_inf_info[ip_name]["ports"]["misc"][sig_name]["dir"]:
        dir = "output"
      elif "inout" in self.ip_inf_info[ip_name]["ports"]["misc"][sig_name]["dir"]:
        dir = "inout"
      return dir

  def get_sig_dir_type(self, ip_name, sig_name):
    if sig_name not in self.ip_inf_info[ip_name]["ports"]["misc"]:
      print("sig name (%s) does not exist!"%sig_name)
      sys.exit(1)
    else:
      dir_type = "logic"
      if " wire" in self.ip_inf_info[ip_name]["ports"]["misc"][sig_name]["dir"]:
        dir_type = "wire"
      return dir_type

  def get_pattern_sig_list(self, ip_name, sig_pattern):
    # In previous version, there is a step to subsitude parameters defined in mapping info. Will add it back when needed
    sig_list = []
    for key in self.ip_inf_info[ip_name]["ports"]["misc"]:
      key_clean = key
      if key.startswith("i_"):
        key_clean = key[2:]
      elif key.startswith("o_"):
        key_clean = key[2:]
      elif key.startswith("io_"):
        key_clean = key[3:]
      if key_clean.startswith(sig_pattern):
        sig_list.append(key)
    return sig_list

  def get_inf_info(self):
    temp_inf = {}
    for idx, ip in enumerate(self.ip_inf_info):
      if ip == self.top_name:
        continue
      temp_inf[ip] = {}
      for sig_idx, sig in enumerate(self.ip_inf_info[ip]["ports"]["misc"]):
        temp_inf[ip][sig] = {}
        temp_inf[ip][sig]["width"] = self.ip_inf_info[ip]["ports"]["misc"][sig]["width_update"]
        temp_inf[ip][sig]["dir"] = self.ip_inf_info[ip]["ports"]["misc"][sig]["dir"]
        temp_inf[ip][sig]["pack_dim"] = self.ip_inf_info[ip]["ports"]["misc"][sig]["packed_dim"]
    return temp_inf

  def get_top_info(self):
    temp_inf = {}
    for idx, sig in enumerate(self.ip_inf_info[self.top_name]["ports"]["misc"]):
      temp_inf[sig] = {}
      try:
        temp_inf[sig]["width"] = self.ip_inf_info[self.top_name]["ports"]["misc"][sig]["width_update"]
      except KeyError:
        print(f"{self.top_name}.{sig} has no width_update key")
      temp_inf[sig]["dir"] = self.ip_inf_info[self.top_name]["ports"]["misc"][sig]["dir"]
    return temp_inf

  def get_imports(self):
    return self.ip_imports
