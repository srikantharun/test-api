#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Class for supported protocols
# Owner: Luyi <yi.lu@axelera.ai>

import os
import sys
import hjson
import subprocess
import pathlib
import math
import numbers

class protocol_info:
  protocol_src = ""  # location of protocol definations

  def __init__(self, protocol_src):
    self.protocol_src = "%s/protocol" % pathlib.Path(__file__).parent.resolve()

  def get_protocol_info(self, bus_type):
    bus_info = {}
    r_info = {}
    file_list = list(pathlib.Path(self.protocol_src).glob(f'{bus_type}.hjson'))
    if not file_list:
      print("The protocol define for %s is not found in %s!"%(bus_type, self.protocol_src))
    else:
      with open(f'{self.protocol_src}/{file_list[0].name}') as file:
        bus_info = hjson.load(file)
    for sig in bus_info:
      r_info[sig] = "input" if "in" in bus_info[sig]["dir"] else "output"
    return r_info

