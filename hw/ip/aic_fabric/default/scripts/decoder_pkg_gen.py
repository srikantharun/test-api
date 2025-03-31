#!/user/bin/python3.6
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: script collect slave addr info
# Owner: Luyi <yi.lu@axelera.ai>

import sys
import os
import argparse
import hjson
import shutil
from ast import literal_eval
from mako.template import Template
from mako.lookup import TemplateLookup
import re

CWD = os.getcwd()
RROOT = os.environ.get("REPO_ROOT")
AW = 12 #int(41/4)

genFileName = "aic_fabric_pkg.sv"
genFilePath = f'{RROOT}/hw/ip/aic_fabric/default/rtl/pkg/{genFileName}'

TEMP_LOOKUP = TemplateLookup(directories=[f'{RROOT}/hw/ip/aic_fabric/default/scripts'])

parser = argparse.ArgumentParser(description="Run test defined in test_list")
parser.add_argument(
    "-f",
    "--addr-pkg",
    type=str,
    default= f'{RROOT}/hw/impl/europa/asic/rtl/pkg/aipu_addr_map_pkg.sv,{RROOT}/hw/impl/europa/asic/rtl/pkg/aic_addr_map_pkg.sv',
    help="address package, comma seperate multiples",
)

parser.add_argument(
    "-c",
    "--axi-config",
    type=str,
    default="fabric_slave.hjson",
    help="address package",
)

parser.add_argument(
    "-o",
    "--output",
    type=str,
    default="../rtl/slave_pkg.sv",
    help="generated ",
)

def is_hex(s):
  pattern = r"^(0x|'h|'H)?[0-9a-fA-F]+$"
  return bool(re.match(pattern, s))

def dataAn(data=[]):
  tempDict = {} # store resolved value
  reDict = {}
  paraName = []
  paraUn = {} # parameter is not hex value
  newResolve = False
  for line in data:
    line = line.strip()
    if line.startswith("parameter"):
      lineInfo_pre = line.split("=")[0].strip().split(" ")
      lineInfo_post = line.split("=")[1].strip()
      lineName = lineInfo_pre[-1]
      lineValue = lineInfo_post.replace(";","")
      hex = is_hex(lineValue)
      if hex:
        lineValue = lineValue.replace("'h","")
        lineValue = ('0'*AW+lineValue)[-AW:]
        lineValue = "0x"+lineValue.lower() #hex(literal_eval("0x"+lineValue))
        tempDict[lineName] = {"val":lineValue, "hex":hex}
        paraName.append(lineName)
        newResolve = True
      else:
        paraUn[lineName] = {"val":lineValue, "hex":hex}

  while(newResolve):
    newResolve = False
    resolvedPara = {}
    newRL = []
    for para in paraUn:
      paraValue = paraUn[para]["val"]
      for resolvedPara in tempDict:
        paraValue = paraValue.replace(resolvedPara, tempDict[resolvedPara]["val"])
        if is_hex(paraValue):
          newResolve = True
          newRL.append(para)
          paraUn[para] = {"val":paraValue, "hex":is_hex(paraValue)}
          break
        else:
          continue
    if newRL:
      for newPara in newRL:
        newParaValue = paraUn.pop(newPara)
        tempDict[newPara] = newParaValue
        paraName.append(newPara)

  while(paraName):
    name = paraName.pop(0)
    addrSt = None
    addrEnd = None
    if name.endswith("_ST_ADDR"):
      addrSt = tempDict[name]["val"] if tempDict[name]["hex"] else name
      namePair = name.replace("_ST_ADDR", "_END_ADDR")
      if namePair not in paraName:
        tempDict.pop(name)
        continue
      paraName.remove(namePair)
      addrEnd = tempDict[namePair]["val"] if tempDict[namePair]["hex"] else namePair
    elif name.endswith("_END_ADDR"):
      addrEnd = tempDict[name]["val"] if tempDict[name]["hex"] else name
      namePair = name.replace("_END_ADDR", "_ST_ADDR")
      if namePair not in paraName:
        tempDict.pop(name)
        continue
      paraName.remove(namePair)
      addrSt = tempDict[namePair]["val"] if tempDict[namePair]["hex"] else namePair
    if addrSt and addrEnd:
      if tempDict[name]["hex"]:
        addrSt = literal_eval(addrSt.lower())
        addrEnd = literal_eval(addrEnd.lower())
      name = name.replace("_ST_ADDR","").replace("_END_ADDR","")
      reDict[name] = (addrSt, addrEnd)
  return reDict, tempDict

def collectInfo():

  args = parser.parse_args()
  addrPkg_list = args.addr_pkg.split(",")
  genFile = args.output
  axiConf = args.axi_config

  axiInfo = None
  if axiConf:
    with open(axiConf, "r") as file:
      axiInfo = hjson.load(file)
  else:
    print("axi configuration file cannot be found!")
    sys.exit(1)

  addrDict = None
  matchInfo = {}
  addrData = []
  for addrPkg in addrPkg_list:
    with open(addrPkg, "r") as file:
      file_lines = file.readlines()
      addrData += file_lines

  addrDict, nameDict = dataAn(addrData)
  nameKey = list(nameDict.keys())
  valList = list(nameDict.values())
  for bus in axiInfo:
    matchInfo[bus] = {}
    # in hjson, the debug slave 0 is counted, however, the addr decoder only count non-debug slaves. So "-1" here
    matchInfo[bus]["slave_num"] = int(axiInfo[bus]["slave_num"])-1
    matchInfo[bus]["master_num"] = axiInfo[bus]["master_num"]
    matchInfo[bus]["inDefault"] = None
    matchInfo[bus]["outDefault"] = None
    matchInfo[bus]["postMap"] = {}
    matchInfo[bus]["fakeDumySlave"] = []
    for slave in axiInfo[bus]["map"]:
      cont = axiInfo[bus]["map"][slave]
      if type(cont) == str:
        if cont == "addr_in_core_default":
          matchInfo[bus]["inDefault"] = slave
        elif cont == "addr_out_core_default":
          matchInfo[bus]["outDefault"] = slave
        elif cont == "None":
          continue
        else:
          matchInfo[bus]["postMap"][slave] = [v for k,v in addrDict.items() if k == cont]
      elif type(cont) == list:
        if "addr_in_core_default" in cont:
          matchInfo[bus]["inDefault"] = slave
          cont.remove("addr_in_core_default")
        if "addr_out_core_default" in cont:
          matchInfo[bus]["outDefault"] = slave
          cont.remove("addr_out_core_default")
        if cont:
          matchInfo[bus]["postMap"][slave] = []
          for ip in cont:
            matchInfo[bus]["postMap"][slave] += [v for k,v in addrDict.items() if k == ip]
    regionNum = 0

    for slave in matchInfo[bus]["postMap"]:
      if not matchInfo[bus]["postMap"][slave]:
        matchInfo[bus]["fakeDumySlave"].append(slave)
        continue
      matchInfo[bus]["postMap"][slave] = sorted(matchInfo[bus]["postMap"][slave], key = lambda ele: (0, ele)
                        if type(ele[0]) is int else (1, ele))
      tempList = []
      tempName = []
      newRange = True
      curRange = None
      for idx in range(len(matchInfo[bus]["postMap"][slave])):
        if newRange:
          curRange = matchInfo[bus]["postMap"][slave][idx]
        if type(curRange[0]) is str:
            tempList.append((curRange[0], curRange[1]))
            tempName.append((curRange[0], curRange[1]))
            newRange = True
        elif (idx + 1) < len(matchInfo[bus]["postMap"][slave]) and type(matchInfo[bus]["postMap"][slave][idx+1][0]) is int:
          if (curRange[1] + 1) == matchInfo[bus]["postMap"][slave][idx+1][0]:
            curRange = (curRange[0], matchInfo[bus]["postMap"][slave][idx+1][1])
            newRange = False
          elif (curRange[1] + 1) < matchInfo[bus]["postMap"][slave][idx+1][0]:
            tempRange = (hex(curRange[0]), hex(curRange[1]))
            tempVal = {"val":"0x"+('0'*AW+hex(curRange[0])[2:])[-AW:], "hex":True}
            nameIdx = valList.index(tempVal) # find the first match, if multi instances, only the first one's idx is selected
            nameVal0 = nameKey[nameIdx]
            tempVal = {"val":"0x"+('0'*AW+hex(curRange[1])[2:])[-AW:], "hex":True}
            nameIdx = valList.index(tempVal)
            nameVal1 = nameKey[nameIdx]
            tempList.append(tempRange)
            tempName.append((nameVal0, nameVal1))
            newRange = True
        else:
          tempRange = (hex(curRange[0]), hex(curRange[1]))
          tempVal = {"val":"0x"+('0'*AW+hex(curRange[0])[2:])[-AW:], "hex":True}
          nameIdx = valList.index(tempVal)
          nameVal0 = nameKey[nameIdx]
          tempVal = {"val":"0x"+('0'*AW+hex(curRange[1])[2:])[-AW:], "hex":True}
          nameIdx = valList.index(tempVal)
          nameVal1 = nameKey[nameIdx]
          tempName.append((nameVal0, nameVal1))
          tempList.append(tempRange)
          newRange = True
      matchInfo[bus]["postMap"][slave] = {}
      matchInfo[bus]["postMap"][slave]["addr"] = tempList
      matchInfo[bus]["postMap"][slave]["name"] = tempName
      regionNum += len(tempList)
    matchInfo[bus]["regionNum"] = regionNum
    if matchInfo[bus]["fakeDumySlave"]:
      for slave in matchInfo[bus]["fakeDumySlave"]:
        matchInfo[bus]["postMap"].pop(slave)

  matchInfoReorg = {}
  matchInfoReorg["BUS"] = matchInfo

  return matchInfoReorg

def fileGen(info={}):
  if info:
    t = Template(f"<%include file='decoder_pkg.sv.tpl'/>",lookup=TEMP_LOOKUP)
    renderOut = t.render(**info)
    with open(genFilePath, 'wb') as file:
      file.write(renderOut.encode())
  else:
    print("no info collected!")
    sys.exit(1)

if __name__ == "__main__":
  info = collectInfo()
  fileGen(info)

