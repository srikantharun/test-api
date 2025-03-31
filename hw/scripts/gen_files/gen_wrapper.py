#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: wrapper gen
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

class wrapperGen:
  infoSrc = "" # path of the source file which contains ip info, the hjson file
  infoCont = {} # content of the hjson file above
  svRuleSrc = "" # path of file defining naming convention
  svRuleInfo = {}
  protocolSrc = "" # path to dir of all protocol defines
  protocolInfo = {} # info of bus protocols
  ipInfo = {} # info from hjosn file which contains extra info about the ip, e.g. clk & rst, or wanted pipeline
  wrapperInfo = {} # created wrapper info
  namingCheckEn = None
  gitRepo = ""
  tempLookup = ""

  def __init__(self, infoSrc, protocolSrc, svRule):
    self.infoSrc = pathlib.Path(infoSrc)
    self.protocolSrc = pathlib.Path(protocolSrc)
    self.svRuleSrc = pathlib.Path(svRule)
    self.wrapperInfo["sig"] = []
    self.wrapperInfo["info"] = {}
    self.gitRepo = self._getRepoTop()
    self.tempLookup = TemplateLookup(directories=[f'{self.gitRepo}/hw/scripts/gen_files/templates'])
    if self.infoSrc.exists():
      with self.infoSrc.open() as file:
        self.infoCont = hjson.load(file)
    else:
      print("info source file does not exist!")
      sys.exit(1)

  def _getRepoTop(self):
    return subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                          check=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip()

  #def _busCheck(self):
  #  if not self.protocolSrc:
  #    print("Location for bus protocol define does not exist!")
  #    sys.exit(1)
  #  protocolList = list(pathlib.Path(self.protocolSrc).glob(f'*.hjson'))
  #  for bus in self.infoCont["ports"]["bus"]:
  #    busProtocol = self.infoCont["ports"]["bus"][bus]
  #    if f'{busProtocol}.hjson' not in protocolList:
  #      print("protocol define for %s cannot be found"%(busProtocol))
  #      sys.exit(1)
  #    else:
  #      if busProtocol not in self.protocolInfo:
  #        with open(f'{self.protocolSrc}/{busProtocol}.hjson') as file:
  #          self.protocolInfo[busProtocol] = hjson.load(file)
  #      for sig in infoCont["ports"]["misc"]:
  #        sigName = sig.replace(""bus", "").split("_")[0]
  #        if sigName.lower() in self.protocolInfo[busProtocol]

  def _namingCheck(self):
    if not self.svRuleSrc:
      print("systemverilog rule cannot be loaded!")
      sys.exit(1)
    with self.svRuleSrc.open() as file:
      self.svRuleInfo = hjson.load(file)
    for idx in range(len(self.wrapperInfo["sig"])):
      sigName = self.wrapperInfo["sig"][idx]
      # input
      if "input" in self.wrapperInfo["info"][sigName]["dir"]:
        # TODO, check the case for "_ni"
        sigName = sigName.lstrip(self.svRuleInfo["naming_rule"]["in_meta_pre_info"]).rstrip(self.svRuleInfo["naming_rule"]["in_meta_suf_info"])
        if self.svRuleInfo["naming_rule"]["in_meta"] == "prefix":
          sigName = f'{self.svRuleInfo["naming_rule"]["in_meta_pre_info"]}{sigName}'

        if self.svRuleInfo["naming_rule"]["in_meta"] == "suffix":
          sigName = f'{sigName}{self.svRuleInfo["naming_rule"]["in_meta_suf_info"]}'

      elif "output" in self.wrapperInfo["info"][sigName]["dir"]:
        sigName = sigName.lstrip(self.svRuleInfo["naming_rule"]["out_meta_pre_info"]).rstrip(self.svRuleInfo["naming_rule"]["out_meta_suf_info"])
        if self.svRuleInfo["naming_rule"]["out_meta"] == "prefix":
          sigName = f'{self.svRuleInfo["naming_rule"]["out_meta_pre_info"]}{sigName}'

        if self.svRuleInfo["naming_rule"]["out_meta"] == "suffix":
          sigName = f'{sigName}{self.svRuleInfo["naming_rule"]["out_meta_suf_info"]}'

      elif "inout" in self.wrapperInfo["info"][sigName]["dir"]:
        sigName = sigName.lstrip(self.svRuleInfo["naming_rule"]["inout_meta_pre_info"]).rstrip(self.svRuleInfo["naming_rule"]["inout_meta_suf_info"])
        if self.svRuleInfo["naming_rule"]["inout_meta"] == "prefix":
          sigName = f'{self.svRuleInfo["naming_rule"]["inout_meta_pre_info"]}{sigName}'

        if self.svRuleInfo["naming_rule"]["inout_meta"] == "suffix":
          sigName = f'{sigName}{self.svRuleInfo["naming_rule"]["inout_meta_suf_info"]}'
      self.wrapperInfo["info"][self.wrapperInfo["sig"][idx]]["newName"] = sigName

  def getSig(self):
    if self.infoCont:
      filePath = self.infoCont["design_file"].replace("{REPO_ROOT}", self.gitRepo)
      subprocess.check_output("verible_syntax_mo.py -c " + filePath, shell=True)
      ipJson = f'{filePath}.hjson'
      with open(ipJson) as file:
        ipJsonCont = hjson.load(file)
        self.ipInfo = ipJsonCont[self.infoCont["design_name"]]

      #if self.infoCont["ports"]["bus"]
      #  self._busCheck()

      for sig in self.ipInfo["ports"]["misc"]:
        self.wrapperInfo["sig"].append(sig)
        self.wrapperInfo["info"][sig] = {}
        self.wrapperInfo["info"][sig]["dir"] = self.ipInfo["ports"]["misc"][sig]["dir"]
        self.wrapperInfo["info"][sig]["width"] = self.ipInfo["ports"]["misc"][sig]["width"]
        self.wrapperInfo["info"][sig]["newName"] = sig
        if "input" in self.ipInfo["ports"]["misc"][sig]["dir"]:
          self.wrapperInfo["info"][sig]["dir_only"] = "input"
        elif "output" in self.ipInfo["ports"]["misc"][sig]["dir"]:
          self.wrapperInfo["info"][sig]["dir_only"] = "output"
        else:
          self.wrapperInfo["info"][sig]["dir_only"] = "inout"

      #self._namingCheck()

  def topRender(self):
    cfg = {}
    cfg["imports"] = self.ipInfo["imports"]
    cfg["designName"] = self.infoCont["design_name"]
    cfg["wrapperName"] = self.infoCont["wrapper_name"]
    cfg["clkList"] = self.infoCont["ports"]["clk"]
    cfg["rstList"] = self.infoCont["ports"]["rst"]
    cfg["interfaceSig"] = self.wrapperInfo
    if "dft" in self.infoCont:
      cfg["dft"] = self.infoCont["dft"]
    else:
      cfg["dft"] = ""

    t = Template(f"<%include file='wrapper.sv.mako'/>",lookup=self.tempLookup)
    renderedOut = t.render(**cfg)
    filePath = self.infoCont["wrapper_file"].replace("{REPO_ROOT}", self.gitRepo)
    pathlib.Path(filePath).parents[0].mkdir(parents=True, exist_ok=True)
    with open(filePath, 'wb') as file:
      file.write(renderedOut.encode())

def main():
  args = parser.parse_args()
  infoFile = args.info
  protocolDir = args.protocol
  svRule = args.sv_rule

  top= wrapperGen(infoFile, protocolDir, svRule)
  top.getSig()
  top.topRender()

if __name__ == "__main__":
  main()
