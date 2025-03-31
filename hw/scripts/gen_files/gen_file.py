#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: sv file gen
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
  "-r", "--sv-rule", type=str, default=""
)
parser.add_argument(
  "-p", "--protocol", type=str, default=""
)

class svGen:
  infoSrc = "" # path of the source file which contains ip info, the hjson file
  infoCont = {} # content of the hjson file above
  protocolSrc = "" # path to dir of all protocol defines
  svRuleSrc = "" # path of file defining naming convention
  svRuleInfo = {}
  clkIn = {} # clk signals
  rstIn = {} # reset signals
  sigIn = {} # input signals, detail struct in init
  sigOut = {} # output signals, detail struct in init
  sigInOut = {} # inout signals, details struct in init
  sigBus = {} # bus protocal signals
  sigPara = {} # parameters
  pkgEn = None # if package is needed
  gitRepo = ""
  tempLookup = ""

  def __init__(self, infoSrc, protocolSrc, svRule):
    self.infoSrc = pathlib.Path(infoSrc)
    self.protocolSrc = pathlib.Path(protocolSrc)
    self.svRuleSrc = pathlib.Path(svRule)
    if self.infoSrc.exists():
      with self.infoSrc.open() as file:
        self.infoCont = hjson.load(file)
    else:
      print("info source file does not exist!")
      sys.exit(1)
    if not self.svRuleSrc:
      print("systemverilog rule cannot be loaded!")
      sys.exit(1)
    with self.svRuleSrc.open() as file:
      self.svRuleInfo = hjson.load(file)
    self.clkIn["sig"] = []
    self.clkIn["info"] = {}
    self.rstIn["sig"] = []
    self.rstIn["info"] = {}
    self.sigIn["sig"] = []
    self.sigIn["info"] = {}
    self.sigOut["sig"] = []
    self.sigOut["info"] = {}
    self.sigInOut["sig"] = []
    self.sigInOut["info"] = {}
    self.sigBus["sig"] = []
    self.sigBus["info"] = {}
    self.sigBus["para"] = {}
    self.pkgEn = True if self.infoCont["param_resolved"] == "False" else False
    self.gitRepo = self._getRepoTop()
    self.tempLookup = TemplateLookup(directories=[f'{self.gitRepo}/hw/scripts/gen_files/templates'])

  def _getRepoTop(self):
    return subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                          check=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip()

  def _namingCheck(self, sig, dir):
    # input
    sigName = sig
    if "input" in dir or dir == "in":
      # TODO, check the case for "_ni"
      sigName = sigName.lstrip(self.svRuleInfo["naming_rule"]["in_meta_pre_info"]).rstrip(self.svRuleInfo["naming_rule"]["in_meta_suf_info"])
      if self.svRuleInfo["naming_rule"]["in_meta"] == "prefix":
        sigName = f'{self.svRuleInfo["naming_rule"]["in_meta_pre_info"]}{sigName}'

      if self.svRuleInfo["naming_rule"]["in_meta"] == "suffix":
        sigName = f'{sigName}{self.svRuleInfo["naming_rule"]["in_meta_suf_info"]}'

    elif "output" in dir or dir == "out":
      sigName = sigName.lstrip(self.svRuleInfo["naming_rule"]["out_meta_pre_info"]).rstrip(self.svRuleInfo["naming_rule"]["out_meta_suf_info"])
      if self.svRuleInfo["naming_rule"]["out_meta"] == "prefix":
        sigName = f'{self.svRuleInfo["naming_rule"]["out_meta_pre_info"]}{sigName}'

      if self.svRuleInfo["naming_rule"]["out_meta"] == "suffix":
        sigName = f'{sigName}{self.svRuleInfo["naming_rule"]["out_meta_suf_info"]}'

    elif "inout" in dir:
      sigName = sigName.lstrip(self.svRuleInfo["naming_rule"]["inout_meta_pre_info"]).rstrip(self.svRuleInfo["naming_rule"]["inout_meta_suf_info"])
      if self.svRuleInfo["naming_rule"]["inout_meta"] == "prefix":
        sigName = f'{self.svRuleInfo["naming_rule"]["inout_meta_pre_info"]}{sigName}'

      if self.svRuleInfo["naming_rule"]["inout_meta"] == "suffix":
        sigName = f'{sigName}{self.svRuleInfo["naming_rule"]["inout_meta_suf_info"]}'

    return sigName

  def getSig(self):
    if self.infoCont:
      moduleName = self.infoCont["name"]
      if self.infoCont["param"]:
        for param in self.infoCont["param"]:
          self.sigPara[param] = f'{self.infoCont["param"][param]}' #f'{moduleName}_{self.infoCont["param"][param]}'.upper()
      if self.infoCont["in_clk"]:
        for sig in self.infoCont["in_clk"]:
          if sig not in self.clkIn["sig"]:
            sigName = self._namingCheck(sig, "input")
            self.clkIn["sig"].append(sigName)
            self.clkIn["info"][sigName] = 1
      if self.infoCont["in_rst"]:
        for sig in self.infoCont["in_rst"]:
          if sig not in self.rstIn["sig"]:
            sigName = self._namingCheck(sig, "input")
            self.rstIn["sig"].append(sigName)
            self.rstIn["info"][sigName] = 1
      if self.infoCont["in_port_b"]:
        for sig in self.infoCont["in_port_b"]:
          if sig not in self.sigIn["sig"]:
            sigName = self._namingCheck(sig, "input")
            self.sigIn["sig"].append(sigName)
            self.sigIn["info"][sigName] = 1
          else:
            print("%s has already been defined"%(sig))
            sys.exit(1)
      if self.infoCont["in_port_v"]:
        for sig in self.infoCont["in_port_v"]:
          if sig not in self.sigIn["sig"]:
            sigName = self._namingCheck(sig, "input")
            self.sigIn["sig"].append(sigName)
            if self.pkgEn:
              self.sigIn["info"][sigName] = self.infoCont["in_port_v"][sig]
              #if str(self.infoCont["in_port_v"][sig]).isdigit():
              #  self.sigIn["info"][sigName] = self.infoCont["in_port_v"][sig]
              #else:
              #  self.sigIn["info"][sigName] = self.infoCont["in_port_v"][sig]
            else:
              if str(self.infoCont["in_port_v"][sig]).isdigit():
                self.sigIn["info"][sigName] = self.infoCont["in_port_v"][sig]
              else:
                self.sigIn["info"][sigName] = self.sigPara[self.infoCont["in_port_v"][sig]]
          else:
            print("%s has already been defined"%(sig))
            sys.exit(1)
      if self.infoCont["out_port_b"]:
        for sig in self.infoCont["out_port_b"]:
          if sig not in self.sigOut["sig"]:
            sigName = self._namingCheck(sig, "output")
            self.sigOut["sig"].append(sigName)
            self.sigOut["info"][sigName] = 1
          else:
            print("%s has already been defined"%(sig))
            sys.exit(1)
      if self.infoCont["out_port_v"]:
        for sig in self.infoCont["out_port_v"]:
          if sig not in self.sigOut["sig"]:
            sigName = self._namingCheck(sig, "output")
            self.sigOut["sig"].append(sigName)
            if not self.pkgEn:
              self.sigOut["info"][sigName] =  self.sigPara[self.infoCont["out_port_v"][sig]]
            else:
              self.sigOut["info"][sigName] = self.infoCont["out_port_v"][sig]
          else:
            print("%s has already been defined"%(sig))
            sys.exit(1)
      if self.infoCont["inout_port_b"]:
        for sig in self.infoCont["inout_port_b"]:
          if sig not in self.sigInOut["sig"]:
            sigName = self._namingCheck(sig, "inout")
            self.sigInOut["sig"].append(sigName)
            self.sigInOut["info"][sigName] = 1
          else:
            print("%s has already been defined"%(sig))
            sys.exit(1)
      if self.infoCont["inout_port_v"]:
        for sig in self.infoCont["inout_port_v"]:
          if sig not in self.sigInOut["sig"]:
            sigName = self._namingCheck(sig, "inout")
            self.sigInOut["sig"].append(sigName)
            if not self.pkgEn:
              self.sigInOut["info"][sigName] = self.sigPara[self.infoCont["inout_port_v"][sig]]
            else:
              self.sigInOut["info"][sigName] = self.infoCont["inout_port_v"][sig]
          else:
            print("%s has already been defined"%(sig))
            sys.exit(1)
      if self.infoCont["bus"]:
        for bus in self.infoCont["bus"]:
          busInst = 1
          if "inst" in self.infoCont["bus"][bus] and "@inst" in bus:
            busInst = self.infoCont["bus"][bus]["inst"]
          for busIdx in range(int(busInst)):
            busInfo = None
            busType = self.infoCont["bus"][bus]["type"]
            busName = bus.replace("@inst", str(busIdx))
            if "@" in busName:
              busName = bus.split("@")[0]
            paramMap = {}
            if self.infoCont["bus"][bus]["param"]["self"]: # still use [bus] here because the data in hjson use that as key
              for param in self.infoCont["bus"][bus]["param"]["self"]:
                #busName = bus
                #if "@" in bus:
                #  busName = bus.split("@")[0]
                paramName = f'{moduleName}_{busName}_{busType}_{param}'.upper()
                if self.infoCont["bus"][bus]["param"]["self"][param].endswith("_t"):
                  paramName = self.infoCont["bus"][bus]["param"]["self"][param]
                self.sigPara[paramName] = self.infoCont["bus"][bus]["param"]["self"][param]
                paramMap[param] = paramName
            if self.infoCont["bus"][bus]["param"]["shared"]:
              for param in self.infoCont["bus"][bus]["param"]["shared"]:
                paramName = f'{self.infoCont["bus"][bus]["param"]["shared"][param]}_{param}'.upper()
                if self.infoCont["bus"][bus]["param"]["shared"][param].endswith("_t"):
                  paramName = self.infoCont["bus"][bus]["param"]["shared"][param]
                paramMap[param] = paramName
            fileList = list(pathlib.Path(self.protocolSrc).glob(f'{busType}.hjson'))
            if not fileList:
              print("The protocol define for %s is not found!"%(busType))
            else:
              with open(f'{self.protocolSrc}/{fileList[0].name}') as file:
                busInfo = hjson.load(file)
            for sig in busInfo:
              sigName = f'{busName}_{busType}_{sig}'
              sigName = self._namingCheck(sigName, busInfo[sig]["dir"])
              if sigName not in self.sigBus["sig"]:
                self.sigBus["sig"].append(sigName)
                self.sigBus["info"][sigName] = {}
                self.sigBus["info"][sigName]["dir"] = busInfo[sig]["dir"]
                if not self.pkgEn:
                  self.sigBus["info"][sigName]["dw"] = str(busInfo[sig]["dw"]) if str(busInfo[sig]["dw"]).isdigit() else str(self.infoCont["bus"][bus]["param"][busInfo[sig]["dw"]])
                else:
                  self.sigBus["info"][sigName]["dw"] = str(busInfo[sig]["dw"]) if str(busInfo[sig]["dw"]).isdigit() else str(paramMap[busInfo[sig]["dw"]])

                if "@" in self.sigBus["info"][sigName]["dw"]:
                  pattern = r"@(\w+)"
                  matches = re.findall(pattern, self.sigBus["info"][sigName]["dw"])
                  for match in matches:
                    if match in paramMap:
                      if not self.pkgEn:
                        self.sigBus["info"][sigName]["dw"] = self.sigBus["info"][sigName]["dw"].replace(match, str(self.infoCont["bus"][bus]["param"][match])).replace("@","")
                      else:
                        self.sigBus["info"][sigName]["dw"].replace(match, str(paramMap[match]))

      for para in self.sigPara:
        if "@" in str(self.sigPara[para]):
          pattern = r"@(\w+)"
          matches = re.findall(pattern, self.sigPara[para])
          for match in matches:
            if match in paramMap:
              if not self.pkgEn:
                self.sigPara[para] = self.sigPara[para].replace(match, str(self.infoCont["bus"][bus]["param"][match])).replace("@","")
              else:
                self.sigPara[para] = self.sigPara[para].replace(match, str(paramMap[match])).replace("@","")

  def topRender(self):
    cfg = {}
    cfg["name"] = self.infoCont["name"]
    cfg["imports"] = self.infoCont["imports"]
    cfg["clkIn"] = self.clkIn
    cfg["rstIn"] = self.rstIn
    cfg["sigIn"] = self.sigIn
    cfg["sigOut"] = self.sigOut
    cfg["sigInOut"] = self.sigInOut
    cfg["sigBus"] = self.sigBus
    cfg["sigPara"] = self.sigPara
    cfg["pkgEn"] = self.pkgEn
    t = Template(f"<%include file='interface.sv.mako'/>",lookup=self.tempLookup)
    renderedOut = t.render(**cfg)
    filePath = self.infoCont["top_path"].replace("{REPO_ROOT}", self.gitRepo)
    with open(filePath, 'wb') as file:
      file.write(renderedOut.encode())

    t = Template(f"<%include file='pkg.sv.mako'/>",lookup=self.tempLookup)
    renderedOut = t.render(**cfg)
    filePath = self.infoCont["pkg_path"].replace("{REPO_ROOT}", self.gitRepo)
    with open(filePath, 'wb') as file:
      file.write(renderedOut.encode())

def main():
  args = parser.parse_args()
  infoFile = args.info
  protocolDir = args.protocol
  svRule = args.sv_rule

  top= svGen(infoFile, protocolDir, svRule)
  top.getSig()
  top.topRender()

if __name__ == "__main__":
  main()
