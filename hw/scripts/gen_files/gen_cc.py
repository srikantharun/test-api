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

class topGen:
  owner = "" # owner of the generated file
  email = "" # email of the owner for the generated file
  infoSrc = "" # path of the source file which contains ip info, the hjson file
  infoCont = {} # content of the hjson file above
  ipInterfaceInfo = {} # database for ip interface information from verible_syntax
  ipInstInfo = {} # ip instance info
  ipInstMapping = {} # mapping of ip module name to ip inst name
  sigFullConnInfo = {} # info of each signal: if only 1-to-1 or 1-to-many or many-to-1
  sigLinkedInfo = {} # info of each port and its connected internal signal
  interSigInfo = {} # info of all internal signals
  ipImports = [] # all imports from subips
  topInfSig = {} # info of top module io signals
  paramInfo = {} # info of module parameters
  report = {} # info to report, detail data struct in __init__
  gitRepo = ""
  tempLookup = ""

  def __init__(self, infoSrc, owner, email):
    self.owner = owner
    self.email = email
    self.infoSrc = pathlib.Path(infoSrc)
    self.report["sigWidthMis"] = [] # info about signal width mismatch when connecting
    self.report["sigWidthNot"] = [] # info about unresolved signal width
    self.report["accSigMis"] = [] # info about width mismatch for accumulated signal
    self.report["unconn"] = {} # info about input signals not driven
    self.gitRepo = self._getRepoTop()
    self.tempLookup = TemplateLookup(directories=[f'{self.gitRepo}/hw/scripts/gen_files/templates'])
    print(self.infoSrc)
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

  def _getSigList(self, ip, pairIp, pairSig):
    ### vector sig case
    if "[" in pairSig:
      pairSig = pairSig.split("[")[0]
      for para in self.ipInstInfo[ip]["param"]:
        pairSig = pairSig.replace(para, self.ipInstInfo[ip]["param"][para])
    pairSigList = []
    if pairIp == self.infoCont["top"]:
      for key in self.infoCont["top_ports"]:
        if self.infoCont["top_ports"][key] == "axi":
          prot = "axi"
        else:
          prot = "misc"
        keyClean = key
        if key.startswith("i_"):
          keyClean = key.lstrip("i_")
        elif key.startswith("o_"):
          keyClean = key.lstrip("o_")
        elif key.startswith("io_"):
          keyClean = key.lstrip("io_")
        if keyClean.startswith(pairSig):
          pairSigList.append({"sig":key, "top":1, "prot":prot})
    else:
      for key in self.ipInterfaceInfo[pairIp]["ports"]["misc"]:
        keyClean = key
        if key.startswith("i_"):
          keyClean = key.lstrip("i_")
        elif key.startswith("o_"):
          keyClean = key.lstrip("o_")
        elif key.startswith("io_"):
          keyClean = key.lstrip("io_")
        if keyClean.startswith(pairSig):
          pairSigList.append({"sig":key, "top":0, "prot":"misc"})
    return pairSigList

  def _findSigMatch(self, ip, ipSigList, ipPattern, pairIp, pairIpSigList, pairIpPattern, segTrue):
    pairIpIsTop = True if pairIp == self.infoCont["top"] else False
    matchSig = []

    for ipSig in ipSigList:
      ipSigDir = self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["dir"].replace("logic","").replace("wire","").strip()
      sigMatchRatio = 0
      pairSigFound = ""
      for pairIpSig in pairIpSigList:
        if pairIpIsTop:
          if pairIpSig["prot"] == "misc" and self.infoCont["top_ports"][pairIpSig["sig"]] != ipSigDir:
            continue
        else:
          if self.ipInterfaceInfo[pairIp]["ports"]["misc"][pairIpSig["sig"]]["dir"] == ipSigDir:
            continue
        ipSigClean = ipSig
        pairIpSigClean = pairIpSig["sig"]
        if ipSig.startswith("i_"):
          ipSigClean = ipSig.lstrip("i_")
        elif ipSig.startswith("o_"):
          ipSigClean = ipSig.lstrip("o_")
        elif ipSig.startswith("io_"):
          ipSigClean = ipSig.lstrip("io_")
        if pairIpSig["sig"].startswith("i_"):
          pairIpSigClean = pairIpSig["sig"].lstrip("i_")
        elif pairIpSig["sig"].startswith("o_"):
          pairIpSigClean = pairIpSig["sig"].lstrip("o_")
        elif pairIpSig["sig"].startswith("io_"):
          pairIpSigClean = pairIpSig["sig"].lstrip("io_")

        if pairIpSig["prot"] == "misc":
          ipSigClean = ipSigClean.replace(ipPattern, "")
          pairIpSigClean = pairIpSigClean.replace(pairIpPattern, "")
          tempRatio = SequenceMatcher(None, ipSigClean.lower(), pairIpSigClean.lower()).ratio()
          if tempRatio == 1.0: #> sigMatchRatio:
            sigMatchRatio = tempRatio
            pairSigFound = pairIpSig
        else:
          if ipSigClean.startswith(pairIpPattern):
            pairSigFound = {"sig":ipSig}
      if not pairSigFound:
        continue

      matchSig.append((ipSig, pairSigFound["sig"]))
      if pairIp == self.infoCont["top"]:
        self.topInfSig[pairSigFound["sig"]] = {}
        self.topInfSig[pairSigFound["sig"]]["width"] = self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["width"]
        self.topInfSig[pairSigFound["sig"]]["dir"] = self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["dir"]
        # update signal width of "top" in ipInterfaceInfo
        if not pairIpSig["prot"] == "misc":
          self.ipInterfaceInfo[self.infoCont["top"]]["ports"]["misc"][pairSigFound["sig"]]= {}
        self.ipInterfaceInfo[self.infoCont["top"]]["ports"]["misc"][pairSigFound["sig"]]["width"] = self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["width"]
        self.ipInterfaceInfo[self.infoCont["top"]]["ports"]["misc"][pairSigFound["sig"]]["dir"] = self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["dir"]
      #pairIpSigList.remove(pairSigFound)
    return matchSig

  def _anaParam(self):
    resolvedPara = []
    resolved = False
    for param in self.paramInfo:
      if self.paramInfo[param]["value"].isdigit():
        self.paramInfo[param]["resolved"] = True
        resolvedPara.append(param)
        resolved = True
    while(resolved):
      resolved = False
      for param in self.paramInfo:
        if param in resolvedPara:
          continue
        tempValue = self.paramInfo[param]["value"]
        for item in resolvedPara:
          tempValue = tempValue.replace(item, self.paramInfo[item]["value"])
        tempValue = tempValue.replace("$clog2", "math.log2")
        re = {}
        try:
          exec(f'import math; result = {tempValue}', re)
          if isinstance(re["result"], numbers.Real):
            resolved = True
            resolvedPara.append(param)
            self.paramInfo[param]["value"] = str(int(re["result"]))
            self.paramInfo[param]["resolved"] = True
        except:
          continue

  def _updateParam(self):
    for ip in self.ipInterfaceInfo:
      for sig in self.ipInterfaceInfo[ip]["ports"]["misc"]:
        widthInfo = self.ipInterfaceInfo[ip]["ports"]["misc"][sig]["width"]
        widthResolved = False
        widthUpdate = ""
        # if only digit
        if isinstance(widthInfo, int):
          widthUpdate = str(widthInfo)
          widthResolved = True
        elif isinstance(widthInfo, str):
          if widthInfo in self.paramInfo:
            if self.paramInfo[widthInfo]["resolved"]:
              widthUpdate = self.paramInfo[widthInfo]["value"]
              widthResolved = True
            else:
              widthUpdate = ""
              widthResolved = False
          else:
            widthUpdate = ""
            widthResolved = False
            print("Warning! %s is not identified for %s in module %s"%(widthInfo, sig, ip))
        elif isinstance(widthInfo, list):
          if len(widthInfo) == 0:
            widthUpdate = "1"
            widthResolved = True
          elif len(widthInfo) == 1:
            if widthInfo[0].isdigit():
              widthUpdate =  widthInfo[0]
              widthResolved = True
            elif widthInfo[0] in self.paramInfo:
              if self.paramInfo[widthInfo[0]]["resolved"]:
                widthUpdate = self.paramInfo[widthInfo[0]]["value"]
                widthResolved = True
              else:
                widthUpdate = widthInfo[0]
                widthResolved = False
            else:
              widthUpdate = widthInfo[0]
              widthResolved = False
              print("Warning! %s is not identified for %s in module %s"%(widthInfo, sig, ip))
          elif len(widthInfo) == 2:
            if all(item.isdigit() for item in widthInfo):
              widthUpdate = int(widthInfo[0]) + 1 - int(widthInfo[1])
              widthResolved = True
            elif isinstance(widthInfo[0], str) and "pkg" in widthInfo[0]:
              if widthInfo[1] in self.paramInfo:
                if self.paramInfo[widthInfo[1]]["resolved"]:
                  widthUpdate = self.paramInfo[widthInfo[1]]["value"]
                  widthResolved = True
                else:
                  widthUpdate = f'{widthInfo[0]}::widthInfo[1]'
                  widthResolved = False
              else:
                widthUpdate = f'{widthInfo[0]}::widthInfo[1]'
                widthResolved = False
                print("Warning! %s is not identified for %s in module %s"%(widthInfo, sig, ip))
            else:
              widthUpdate = ""
              widthResolved = False
              print("Warning! %s is not identified for %s in module %s"%(widthInfo, sig, ip))
          elif len(widthInfo) == 3:

            if all(item.isdigit() for item in widthInfo):
              #widthUpdate = int(widthInfo[0]) + 1 - int(widthInfo[1]) - int(widthInfo[2])
              widthResolved = True
            else:
              widthResolved = True
              for idx in range(len(widthInfo)):
                if widthInfo[idx].isdigit():
                  continue
                elif widthInfo[idx] in self.paramInfo:
                  if self.paramInfo[widthInfo[idx]]["resolved"]:
                    widthInfo[idx] = self.paramInfo[widthInfo[idx]]["value"]
                  else:
                    widthInfo[idx] = widthInfo[idx]
                    widthResolved = False
                else:
                  print("Warning! %s is not identified for %s in module %s"%(widthInfo, sig, ip))
                  widthInfo[idx] = widthInfo[idx]
                  widthResolved = False
            if widthResolved:
              widthUpdate = int(widthInfo[0]) + 1 - int(widthInfo[1]) - int(widthInfo[2])
            else:
              widthUpdate = f'{widthInfo[0]} + 1 - {widthInfo[1]} - {widthInfo[2]}'

          else:
            print("Warning! %s is not identified for %s in module %s"%(widthInfo, sig, ip))
            widthUpdate = ""
            widthResolved = False

        self.ipInterfaceInfo[ip]["ports"]["misc"][sig]["widthUpdate"] = widthUpdate
        self.ipInterfaceInfo[ip]["ports"]["misc"][sig]["resolved"] = widthResolved

  def _sigWidthCheck(self, ip, ipSig, connIp, connSig):
    if self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["resolved"] and self.ipInterfaceInfo[connIp]["ports"]["misc"][connSig]["resolved"]:
      sigW = self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["widthUpdate"]
      connSigW = self.ipInterfaceInfo[connIp]["ports"]["misc"][connSig]["widthUpdate"]
      if sigW != connSigW:
        info = (ip, ipSig, sigW, connIp, connSig, connSigW)
        self.report["sigWidthMis"].append(info)
    else:
      if (not self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["resolved"]):
        sigInfo = (ip, ipSig, self.ipInterfaceInfo[ip]["ports"]["misc"][ipSig]["width"])
        self.report["sigWidthNot"].append(sigInfo)
      if (not self.ipInterfaceInfo[connIp]["ports"]["misc"][connSig]["resolved"]):
        connSigInfo = (connIp, connSig, self.ipInterfaceInfo[connIp]["ports"]["misc"][connSig]["width"])
        self.report["sigWidthNot"].append(connSigInfo)

  def _accSigWidthAdmin(self, ip, sig):
    connSigResolved = []
    connSigNot = []
    connSigFullResolved = True
    for sigConn in self.sigFullConnInfo[ip][sig]["conn"]:
      connIpName = sigConn.split(".")[0]
      connSigName = sigConn.split(".")[-1]

      if self.ipInterfaceInfo[self.ipInstMapping[connIpName]]["ports"]["misc"][connSigName]["resolved"]:
        connSigResolved.append(self.ipInterfaceInfo[self.ipInstMapping[connIpName]]["ports"]["misc"][connSigName]["widthUpdate"])
      else:
        connSigNot.append(self.ipInterfaceInfo[self.ipInstMapping[connIpName]]["ports"]["misc"][connSigName]["widthUpdate"])
        connSigFullResolved = False
    connWResolved = sum([int(i) for i in connSigResolved])
    connSigNotStr = "+".join(connSigNot)
    if self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["resolved"] and connSigFullResolved:
      if connWResolved > int(self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["widthUpdate"]):
        info = (ip, ipSig, self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["widthUpdate"], connWResolved)
        self.report["accSigMis"].append(info)
      if connWResolved < int(self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["widthUpdate"]):
        self.sigLinkedInfo[ip][sig]["accFix"] = str(int(self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["widthUpdate"]) - connWResolved)
        if "output" in self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["dir"]:
          interSigName = f'{ip}_{sig}_unconn'
          self.interSigInfo[interSigName] = self.sigLinkedInfo[ip][sig]["accFix"]
          self.sigLinkedInfo[ip][sig]["wire"].append(interSigName)
          self.sigLinkedInfo[ip][sig]["accFix"] = False
    if not self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["resolved"] or not connSigFullResolved:
      info = (ip, sig, self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["widthUpdate"], connSigNot)
      self.report["accSigMis"].append(info)
      fixInfo = f'({self.ipInterfaceInfo[self.ipInstMapping[ip]]["ports"]["misc"][sig]["widthUpdate"]} - {str(connWResolved)} - {connSigNotStr if connSigNot else str(0)})'
      self.sigLinkedInfo[ip][sig]["accFix"] = fixInfo

  def _sigCompleteCheck(self):
    for ipInst in self.sigLinkedInfo:
      self.report["unconn"][ipInst] = {}
      for sig in self.ipInterfaceInfo[self.ipInstMapping[ipInst]]["ports"]["misc"]:
        if sig not in self.sigLinkedInfo[ipInst]:
          self.report["unconn"][ipInst][sig] = self.ipInterfaceInfo[self.ipInstMapping[ipInst]]["ports"]["misc"][sig]["dir"]

  def getParamInfo(self):
    if self.infoCont["pkg_info"]:
      pkgPathList = []
      paramError = {}
      for item in self.infoCont["pkg_info"]:
        if item.endswith(".sv"):
          pkgPath = item.replace("{REPO_ROOT}", self.gitRepo)
          pkgPathList.append(pkgPath)
        else:
          pkgDirPath = item.replace("{REPO_ROOT}", self.gitRepo)
          for file in os.listdir(pkgDirPath):
            if file.endswith("_pkg.sv"):
              pkgPathList.append(os.path.join(pkgDirPath, file))
      for pkg in pkgPathList:
        with open(pkg) as file:
          lines = file.readlines()
          for line in lines:
            if line.strip().startswith("parameter"):
              paramName = line.split("=")[0].strip().split(" ")[-1]
              paramValue = line.split("=")[1].strip().split(";")[0]
              if paramName not in self.paramInfo:
                self.paramInfo[paramName] = {}
                self.paramInfo[paramName]["resolved"] = False
                self.paramInfo[paramName]["value"] = paramValue
                self.paramInfo[paramName]["file"] = pkg
              else:
                paramError[paramName] = {}
                paramError[paramName]["f0"] = pkg
                paramError[paramName]["f1"] = self.paramInfo[paramName]["file"]
      self._anaParam()
      self._updateParam()

  def getIpInfo(self):
    if self.infoCont["ip_info"]:
      for ip in self.infoCont["ip_info"]:
        ipPath = self.infoCont["ip_info"][ip].replace("{REPO_ROOT}", self.gitRepo)
        ipName = ipPath.split("/")[-1].replace(".sv", "").replace(".v","").replace("_dft_updated", "")
        subprocess.check_output("verible_syntax_mo.py -c " + ipPath, shell=True)
        ipJson = ipPath + ".hjson"
        with open(ipJson) as file:
          ipJsonCont = hjson.load(file)
          self.ipInterfaceInfo[ip] = ipJsonCont[ipName]
        self.ipImports += self.ipInterfaceInfo[ip]["imports"]
      self.ipImports = list(set(self.ipImports))
      # filling info about top
      if self.infoCont["top"] not in self.ipInterfaceInfo:
        self.ipInterfaceInfo[self.infoCont["top"]] = {}
        self.ipInterfaceInfo[self.infoCont["top"]]["ports"] = {}
        self.ipInterfaceInfo[self.infoCont["top"]]["ports"]["misc"] = {}
        for sig in self.infoCont["top_ports"]:
          self.ipInterfaceInfo[self.infoCont["top"]]["ports"]["misc"][sig] = {}
          self.ipInterfaceInfo[self.infoCont["top"]]["ports"]["misc"][sig]["dir"] = self.infoCont["top_ports"][sig]
          self.ipInterfaceInfo[self.infoCont["top"]]["ports"]["misc"][sig]["width"] = "UNKNOW" # actual value will be from the connection pair
    else:
      print("ip info is empty!")
      sys.exit(1)

  def getIpInstInfo(self):
    if self.infoCont["mapping_info"]:
      for ip in self.infoCont["mapping_info"]:
        ipInstNum = self.infoCont["mapping_info"][ip]["inst"]
        if ip not in self.ipInstInfo:
          self.ipInstInfo[ip] = {}
          self.ipInstInfo[ip]["param"] = {}
        self.ipInstInfo[ip]["inst"] = ipInstNum
        ### make generic solution for parameter e.g. base
        if "base" in self.infoCont["mapping_info"][ip]:
          self.ipInstInfo[ip]["base"] = self.infoCont["mapping_info"][ip]["base"]
        for (key, value) in self.infoCont["mapping_info"][ip].items():
          if key.startswith("@"):
            self.ipInstInfo[ip]["param"][key] = value

  def getIpConnInfo(self):
    if self.infoCont["mapping_info"]:
      # for conn info
      for ip in self.infoCont["mapping_info"]:
        ipInstSuffix = ""
        ipName = ip
        if "(" in ip and ")" in ip:
          ipInstSuffix = f'_{ip.split("(")[-1].replace(")", "")}'
          ipName = ip.split("(")[0]
        if int(self.ipInstInfo[ip]["inst"]) > 1:
          ipInstName = [f'u_{ipName}{ipInstSuffix}_{index}' for index in range(int(self.ipInstInfo[ip]["inst"]))]
        else:
          ipInstName = [f'u_{ip}']
        ### check per pair IP
        for pairIp in self.infoCont["mapping_info"][ip]["pair_info"]:
          if self.infoCont["mapping_info"][ip]["pair_info"][pairIp]:
            if pairIp == self.infoCont["top"]:
              pairIpInstName = [f'{self.infoCont["top"]}']
            else:
              if int(self.ipInstInfo[pairIp]["inst"]) > 1:
                pairIpInstName = [f'u_{pairIp}_{index}' for index in range(int(self.ipInstInfo[pairIp]["inst"]))]
              else:
                pairIpInstName = [f'u_{pairIp}']
            if pairIpInstName[0] not in self.ipInstMapping:
              self.ipInstMapping[pairIpInstName[0]] = pairIp
            ### check each pair signal set defined
            for ipInstIdx in range(int(self.ipInstInfo[ip]["inst"])):
              if ipInstName[ipInstIdx] not in self.ipInstMapping:
                self.ipInstMapping[ipInstName[ipInstIdx]] = ipName # use ipName here not ip, for situation e.g. lpddr_p(graph) as a key in hjson file
              for pairItem in self.infoCont["mapping_info"][ip]["pair_info"][pairIp].items():
                # temp, assume pair IP inst is 1, more generic solution may needed
                ipSigList = []
                for key in self.ipInterfaceInfo[ipName]["ports"]["misc"]:
                  keyClean = key
                  if key.startswith("i_"):
                    keyClean = key.lstrip("i_")
                  elif key.startswith("o_"):
                    keyClean = key.lstrip("o_")
                  elif key.startswith("io_"):
                    keyClean = key.lstrip("io_")
                  if keyClean.startswith(pairItem[0]):
                    ipSigList.append(key)
                pairSigPattern = pairItem[1].replace("@inst",str(ipInstIdx)).replace("[]","") # this pattern is used to find group of signals with the same sub-string
                pairIpSigAcc = True if pairItem[1].endswith("[]") else False
                pairIpSigList = self._getSigList(ip, pairIp, pairSigPattern)
                segTrue = True if "[" in pairItem[1] else False
                matchSig = self._findSigMatch(ipName, ipSigList, pairItem[0], pairIp, pairIpSigList, pairSigPattern, segTrue) # use ipName here, cause it will search in self.ipInterfaceInfo
                segInfo = [] #TODO, check if the base info + seg concept still needed since the accumulation signals is handled in different way [self.ipInstInfo[ip]["base"], ipInstIdx] if segTrue else []
                for matchItem in matchSig:
                  #self.connInfo[(ipInstName[ipInstIdx], pairIpInstName[0])][matchItem[0]] = (matchItem[1], segInfo)
                  ipSigFullName = f'{ipInstName[ipInstIdx]}.{matchItem[0]}'
                  pairIpSigFullName = f'{pairIpInstName[0]}.{matchItem[1]}'
                  if ipInstName[ipInstIdx] not in self.sigFullConnInfo:
                    self.sigFullConnInfo[ipInstName[ipInstIdx]] = {}
                  if matchItem[0] not in self.sigFullConnInfo[ipInstName[ipInstIdx]]:
                    self.sigFullConnInfo[ipInstName[ipInstIdx]][matchItem[0]] = {}
                    self.sigFullConnInfo[ipInstName[ipInstIdx]][matchItem[0]]["dir"] = self.ipInterfaceInfo[ipName]["ports"]["misc"][matchItem[0]]["dir"]
                    self.sigFullConnInfo[ipInstName[ipInstIdx]][matchItem[0]]["acc"] = False
                    self.sigFullConnInfo[ipInstName[ipInstIdx]][matchItem[0]]["conn"] = {}
                  self.sigFullConnInfo[ipInstName[ipInstIdx]][matchItem[0]]["conn"][pairIpSigFullName] = {}
                  self.sigFullConnInfo[ipInstName[ipInstIdx]][matchItem[0]]["conn"][pairIpSigFullName]["dir"] = self.ipInterfaceInfo[pairIp]["ports"]["misc"][matchItem[1]]["dir"]
                  self.sigFullConnInfo[ipInstName[ipInstIdx]][matchItem[0]]["conn"][pairIpSigFullName]["seg"] = segInfo

                  if pairIpInstName[0] not in self.sigFullConnInfo:
                    self.sigFullConnInfo[pairIpInstName[0]] = {}
                  if matchItem[1] not in self.sigFullConnInfo[pairIpInstName[0]]:
                    self.sigFullConnInfo[pairIpInstName[0]][matchItem[1]] = {}
                    self.sigFullConnInfo[pairIpInstName[0]][matchItem[1]]["dir"] = self.ipInterfaceInfo[pairIp]["ports"]["misc"][matchItem[1]]["dir"]
                    self.sigFullConnInfo[pairIpInstName[0]][matchItem[1]]["acc"] = pairIpSigAcc
                    self.sigFullConnInfo[pairIpInstName[0]][matchItem[1]]["conn"] = {}
                  if ipSigFullName not in self.sigFullConnInfo[pairIpInstName[0]][matchItem[1]]["conn"]:
                    self.sigFullConnInfo[pairIpInstName[0]][matchItem[1]]["conn"][ipSigFullName] = {}
                    self.sigFullConnInfo[pairIpInstName[0]][matchItem[1]]["conn"][ipSigFullName]["dir"] = self.ipInterfaceInfo[ipName]["ports"]["misc"][matchItem[0]]["dir"]

    else:
      print("mapping info is empty!")
      sys.exit(1)

  def processConnInfo(self):
    ## use output signal of each ip to define the interconnect signal, and link to input of IP
    if self.sigFullConnInfo:
      for ipInst in self.sigFullConnInfo:
        ipIsTop = True if ipInst == f'{self.infoCont["top"]}' else False
        if ipInst not in self.sigLinkedInfo:
          self.sigLinkedInfo[ipInst] = {}
        interSigName = ""
        for sig in self.sigFullConnInfo[ipInst]:
          if sig not in self.sigLinkedInfo[ipInst]:
            self.sigLinkedInfo[ipInst][sig] = {}
            self.sigLinkedInfo[ipInst][sig]["wire"] = []
          if not ipIsTop:
            if "input" in self.sigFullConnInfo[ipInst][sig]["dir"]:
              continue
          else:
            if "output" in self.sigFullConnInfo[ipInst][sig]["dir"]:
              continue
          #if ipIsTop and "output" in self.sigFullConnInfo[ipInst][sig]["dir"]:
          #  continue
          connIp = [key.split(".")[0] for key in self.sigFullConnInfo[ipInst][sig]["conn"]]
          oneIp = True if ([connIp[0]]*len(connIp) == connIp) else False
          for sigConn in self.sigFullConnInfo[ipInst][sig]["conn"]:
            connIpName = sigConn.split(".")[0]
            connSigName = sigConn.split(".")[-1]
            connIpIsTop = True if connIpName == f'{self.infoCont["top"]}' else False
            if connIpName not in self.sigLinkedInfo:
              self.sigLinkedInfo[connIpName] = {}
            if connSigName not in self.sigLinkedInfo[connIpName]:
              self.sigLinkedInfo[connIpName][connSigName] = {}
              self.sigLinkedInfo[connIpName][connSigName]["wire"] = []
            if ipIsTop:
              interSigName = sig
            else:
              if connIpIsTop:
                interSigName = sig
              else:
                if oneIp:
                  interSigName = f"{ipInst}_to_{connIpName}__{sig}"
                  #self._sigWidthCheck(ipInst, sig, connIpName, connSigName)
                else:
                  if not self.sigFullConnInfo[ipInst][sig]["acc"]:
                    interSigName = f"{ipInst}_to_multi__{sig}"
                    #self._sigWidthCheck(ipInst, sig, connIpName, connSigName)
                  else:
                    interSigName = f"{ipInst}_to_{connIpName}__{sig}"

            if interSigName not in self.sigLinkedInfo[connIpName][connSigName]["wire"]:
              self.sigLinkedInfo[connIpName][connSigName]["wire"].append(interSigName)
            if interSigName not in self.sigLinkedInfo[ipInst][sig]["wire"]:
              self.sigLinkedInfo[ipInst][sig]["wire"].append(interSigName)

            if not ipIsTop and not connIpIsTop:
              if interSigName not in self.interSigInfo:
                ## TODO, need to handle situation that tar and dest are both split
                if self.sigFullConnInfo[ipInst][sig]["acc"]:
                  self.interSigInfo[interSigName] = self.ipInterfaceInfo[self.ipInstMapping[connIpName]]["ports"]["misc"][connSigName]["widthUpdate"]
                else:
                  self.interSigInfo[interSigName] = self.ipInterfaceInfo[self.ipInstMapping[ipInst]]["ports"]["misc"][sig]["widthUpdate"]
          if self.sigFullConnInfo[ipInst][sig]["acc"]:
            self._accSigWidthAdmin(ipInst, sig)

      self._sigCompleteCheck()

      if f'{self.infoCont["top"]}' in self.sigLinkedInfo:
        del self.sigLinkedInfo[f'{self.infoCont["top"]}']

  def topRender(self):
    cfg = {}
    cfg["owner"] = self.owner
    cfg["email"] = self.email
    cfg["moduleName"] = self.infoCont["top"]
    cfg["internalSig"] = self.interSigInfo
    cfg["sigLinkedInfo"] = self.sigLinkedInfo
    cfg["ipInstMapping"] = self.ipInstMapping
    cfg["ipInterfaceInfo"] = self.ipInterfaceInfo
    cfg["imports"] = self.ipImports
    cfg["topInf"] = self.topInfSig
    t = Template(f"<%include file='module.sv.mako'/>",lookup=self.tempLookup)
    renderedOut = t.render(**cfg)
    # write to file
    filePath = self.infoCont["top_path"].replace("{REPO_ROOT}", self.gitRepo)
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
  infoFile = args.info
  ratio = args.ratio
  owner = args.owner
  email = args.email

  top = topGen(infoFile, owner, email)
  top.getIpInfo()
  top.getIpInstInfo()
  top.getIpConnInfo()
  top.getParamInfo()
  top.processConnInfo()
  top.topRender()
  #top.printDatabase()

if __name__ == "__main__":
  main()
