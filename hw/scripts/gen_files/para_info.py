#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: parameter info
# Owner: Luyi <yi.lu@axelera.ai>

import os
import sys
import re
import hjson
import subprocess
import pathlib
import math
import numbers

class para_info:
  para_file_list = [] # list of parameter files
  para_info = {} # info of module parameters
  para_typedef_info = {} # info of typedef
  para_error = {}
  git_repo = ""

  def __init__(self, para_file_list):
    self.para_file_list = para_file_list
    pkg_path_list = []
    for item in para_file_list:
      if item.endswith(".sv"):
        pkg_path_list.append(item)
      else:
        # when a dir is given
        for file in os.listdir(item):
          if file.endswith("_pkg.sv"):
            pkg_path_list.append(os.path.join(item, file))
    for pkg in pkg_path_list:
      pkg_path = pathlib.Path(pkg)
      pkg_name = pkg_path.stem
      with pkg_path.open() as file:
        lines = file.readlines()
        for line in lines:
          if line.strip().startswith("parameter"):
            param_name = line.split("=")[0].strip().split(" ")[-1]
            param_value = line.split("=")[1].strip().split(";")[0]
            if param_name not in self.para_info:
              self.para_info[param_name] = {}
              self.para_info[param_name]["resolved"] = False
              self.para_info[param_name]["value"] = param_value
              self.para_info[param_name]["file"] = pkg
            else:
              self.para_error[param_name] = {}
              self.para_error[param_name]["f0"] = pkg
          if line.strip().startswith("typedef") and " logic " in line:
            type_name = line.replace(";","").strip().split(" ")[-1]
            type_cont = line.replace(";","").replace(type_name,"").replace("typedef","").strip()
            if type_name not in self.para_typedef_info:
              self.para_typedef_info[type_name] = {}
              self.para_typedef_info[type_name]["value"] = type_cont
              self.para_typedef_info[type_name]["pkg"] = pkg_name
            else:
              print("type name (%s) exist"%(type_name))
              sys.exit(1)

    self._ana_param()

  def _ana_param(self):
    resolved_para = []
    resolved = False
    for param in self.para_info:
      if self.para_info[param]["value"].isdigit():
        self.para_info[param]["resolved"] = True
        resolved_para.append(param)
        resolved = True
    while(resolved):
      resolved = False
      for param in self.para_info:
        if param in resolved_para:
          continue
        temp_value = self.para_info[param]["value"]
        for item in resolved_para:
          temp_value = temp_value.replace(item, self.para_info[item]["value"])
        temp_value = temp_value.replace("$clog2", "math.log2")
        re = {}
        try:
          exec(f'import math; result = {temp_value}', re)
          if isinstance(re["result"], numbers.Real):
            resolved = True
            resolved_para.append(param)
            para_value = math.ceil(re["result"])
            self.para_info[param]["value"] = str(int(para_value))
            self.para_info[param]["resolved"] = True
        except:
          continue

  def _evaluate_arithmetic_in_string(self, input_string):
    # Split the string into parts that are either non-numeric or arithmetic
    parts = re.split(r'(\s*[+\-*/]\s*)', input_string)

    # Initialize variables to hold the current numeric expression and the result
    current_expression = ""
    combined_result = ""

    # Iterate over the parts
    for part in parts:
      if re.match(r'\s*[+\-*/]\s*', part):  # It's an operator
        current_expression += part
      elif re.match(r'\s*\d+\s*', part):  # It's a number
        current_expression += part
      else:  # It's a non-numeric part
        if current_expression:  # Evaluate the current numeric expression
          try:
            result = eval(current_expression)
          except:
            result = 0  # Default to zero if there's an error in evaluation
          if result != 0:
            combined_result += f"+{result}"
          current_expression = ""
        combined_result += part.strip()

    # Evaluate any remaining numeric expression
    if current_expression:
      try:
        result = eval(current_expression)
      except:
        result = 0  # Default to zero if there's an error in evaluation
      if result != 0:
        combined_result += f"+{result}"

    # Remove leading '+' if present
    if combined_result.startswith('+'):
      combined_result = combined_result[1:]

    return combined_result

  def update_param(self, width_info):
    width_resolved = False
    width_update = ""
    # if only digit
    if isinstance(width_info, int):
      width_update = str(width_info)
      width_resolved = True
    elif isinstance(width_info, str):
      if width_info in self.para_info:
        if self.para_info[width_info]["resolved"]:
          width_update = self.para_info[width_info]["value"]
          width_resolved = True
        else:
          width_update = width_info
          width_resolved = False
      else:
        width_update = width_info
        width_resolved = False
        print("Warning! %s is not identified"%(width_info))
    elif isinstance(width_info, list):
      if len(width_info) == 0:
        width_update = "1"
        width_resolved = True
      elif len(width_info) == 1:
        if width_info[0].isdigit():
          width_update =  width_info[0]
          width_resolved = True
        elif width_info[0] in self.para_info:
          if self.para_info[width_info[0]]["resolved"]:
            width_update = self.para_info[width_info[0]]["value"]
            width_resolved = True
          else:
            width_update = width_info[0]
            width_resolved = False
        else:
          width_update = width_info[0]
          width_resolved = False
          print("Warning! %s is not identified"%(width_info))
      elif len(width_info) == 2:
        if all(item.isdigit() for item in width_info):
          width_update = int(width_info[0]) + 1 - int(width_info[1])
          width_resolved = True
        elif isinstance(width_info[0], str) and "pkg" in width_info[0]:
          if width_info[1] in self.para_info:
            if self.para_info[width_info[1]]["resolved"]:
              width_update = self.para_info[width_info[1]]["value"]
              width_resolved = True
            else:
              width_update = f'{width_info[0]}::width_info[1]'
              width_resolved = False
          else:
            width_update = f'{width_info[0]}::width_info[1]'
            width_resolved = False
            print("Warning! %s is not identified"%(width_info))
        elif isinstance(width_info[0], str) and width_info[1].isdigit():
          width_update = width_info
          width_resolved = False
          if width_info[0] in self.para_info:
            if self.para_info[width_info[0]]["resolved"]:
              width_resolved = True
              width_info[0] = self.para_info[width_info[0]]["value"]
              width_update = int(width_info[0]) + 1 - int(width_info[1])
        else:
          width_update = width_info
          width_resolved = False
          print("Warning! %s is not identified"%(width_info))
      elif len(width_info) == 3:

        if all(item.isdigit() for item in width_info):
          width_resolved = True
        else:
          width_resolved = True
          for idx in range(len(width_info)):
            if width_info[idx].isdigit():
              continue
            elif width_info[idx] in self.para_info:
              if self.para_info[width_info[idx]]["resolved"]:
                width_info[idx] = self.para_info[width_info[idx]]["value"]
              else:
                width_info[idx] = width_info[idx]
                width_resolved = False
            else:
              print("Warning! %s is not identified"%(width_info))
              width_info[idx] = width_info[idx]
              width_resolved = False
        if width_resolved:
          width_update = int(width_info[0]) + 1 - int(width_info[1]) - int(width_info[2])
        else:
          width_str = f'{width_info[0]} + 1 - {width_info[1]} - {width_info[2]}'
          width_update = self._evaluate_arithmetic_in_string(width_str) #self._eval_arith_str(width_str)

      #elif len(width_info) == 4:
      #  width_resolved = False
      #  width_update = width_info
      #  if isinstance(width_info[0], str) and "pkg" in width_info[0]:
      #    if width_info[1] in self.para_info:
      #      if self.para_info[width_info[1]]["resolved"]:
      #        if width_info[2].isdigit() and width_info[3].isdigit():
      #          width_resolved = True
      #          width_update = int(self.para_info[width_info[1]]["value"]) + 1 - int(width_info[2]) - int(width_info[3])

      #  if not width_resolved:
      #    print("Warning! %s is not identified"%(width_info))

      else:
        print("Warning! %s is not identified"%(width_info))
        width_update = width_info
        width_resolved = False

    return width_resolved, width_update

  def get_typedef_info(self):
    return self.para_typedef_info
