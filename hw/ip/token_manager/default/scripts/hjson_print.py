
import math


def str_conv(str):
  return str.upper().replace("-","_")

def header(ip="aic",idw=7):
  # lines.append out hjson:
  # header:
  lines=[]
  lines.append('// Copyright lowRISC contributors.\n\
// Licensed under the Apache License, Version 2.0, see LICENSE for details.\n\
// SPDX-License-Identifier: Apache-2.0\n\
{ name: "token_manager_'+ip.lower()+'_csr",\n\
  clocking: [{clock: "clk_i", reset: "rst_n_i"}],\n\
  bus_interfaces: [\n\
    { protocol: "tlul", direction: "device" }\n\
  ],\n\
\n\
  param_list : [\n\
    {name:"AXI_AW", type:"int", default:"40"},  # Matches aic_common_pkg::\n\
    {name:"AXI_IDW", type:"int", default:"'+str(idw)+'"},\n\
    {name:"AXI_LENW", type:"int", default:"8"}, # Matches axi_pkg::AXI_LEN_WIDTH\n\
  ],\n\
  axi_intf: True\n\
  regwidth: "64",\n\
  addrcap: "0x10000",\n\
  registers: [\n')
  return lines

def footer():
  lines=[]
  lines.append('\
  ]\n\
}\n')
  return lines

def swep(ctype, clist, reg_align=8, reg_w=8, pref=""):
  lines=[]
  nr_regs=math.ceil((len(clist)*reg_align)/64)
  for ridx in range(nr_regs):
    lines.append(f'    {{ name: "{pref}SWEP_{str_conv(ctype)}_{ridx}",\n')
    if(ctype=="prod"):
      lines.append(f'      desc: \'\'\'\n\
       SW Endpoint to produce tokens:\n\
       Write incremental value (0-{pow(2,reg_w)-1}) to produce a number of tokens. This will increment the internal counter with that value.\n\
       Read will return the current value of the internal counter. This values represents the number of tokens waiting to be consumed by the corresponding token-link partner.\n\
      \'\'\',\n')
      lines.append(f'      swaccess: "rw",\n')
      lines.append(f'      hwqe: True\n')
    else:
      lines.append(f'      desc: \'\'\'\n\
       SW Endpoint to consume tokens.\n\
       Read the amount of consumed tokens, read will clear the field.\n\
       Write won\'t do anything.\n\
      \'\'\',\n')
      lines.append(f'      swaccess: "rc",\n')
      lines.append(f'      hwre: True\n')
      lines.append(f'      hwqe: True\n')
    lines.append(f'      hwaccess: "hrw",\n')
    lines.append(f'      hwext: True\n')
    lines.append(f'      fields: [\n')
    for fidx, f in enumerate(clist):
      if(ridx * 64 <= fidx * reg_align and (ridx+1)*64 > fidx * reg_align):
        if 'Unnamed' not in f:
          lines.append(f'        {{\n')
          lines.append(f'          bits: "{fidx*reg_align + reg_w - (ridx*64) - 1}:{fidx*reg_align - (ridx*64)}"\n')
          lines.append(f'          name: "{str_conv(f)}"\n')
          if(ctype=="prod"):
            lines.append(f'          desc: "Write incremental value to this field to update the producer counter for {str_conv(f)}"\n')
          else:
            lines.append(f'          desc: "Read from this field to read the current consumer value of {str_conv(f)}. This will clear the counter."\n')
          lines.append(f'          resval: 0x0\n')
          lines.append(f'        }}\n')
    lines.append(f'      ]\n')
    lines.append(f'    }},\n')
  return lines

def gen_cnt(connections, clist, reg_align=8, reg_w=8, ctype="prod", pref=""):
  lines=[]
  fields=0
  otype="cons" if ctype=="prod" else "prod"
  producer_consumer = "producer" if ctype=="prod" else "consumer"
  for pr in clist:
    res=list(filter(lambda d: d[ctype] in pr, connections))
    fields+=len(res)
    if len(res) > 0:
      nr_regs=math.ceil((len(res)*reg_align)/64)
      for ridx in range(nr_regs):
        pf=f"_{ridx}" if nr_regs>1 else ""
        lines.append(f'    {{ name: "{pref}{str_conv(ctype)}_CNT_{str_conv(pr)}{pf}",\n')
        lines.append(f'      desc: \'\'\'\n\
          Current status of {producer_consumer} counters of {str_conv(pr)}. \n\
          \'\'\',\n')
        lines.append(f'      swaccess: "ro",\n')
        lines.append(f'      hwaccess: "hwo",\n')
        lines.append(f'      hwext: True\n')
        lines.append(f'      fields: [\n')

        for fidx, d in enumerate(res):
          if(ridx * 64 <= fidx * reg_align and (ridx+1)*64 > fidx * reg_align):
            lines.append(f'        {{\n')
            lines.append(f'          bits: "{fidx*reg_align + reg_w - (ridx*64) - 1}:{fidx*reg_align - (ridx*64)}"\n')
            lines.append(f'          name: "{str_conv(d[ctype])}_TOK_{str_conv(ctype)}_{str_conv(d[otype])}_CNT"\n')
            lines.append(f'          desc: "Current count for {str_conv(d[ctype])}_TOK_{str_conv(ctype)}_{str_conv(d[otype])}"\n')
            lines.append(f'          resval: 0x0\n')
            lines.append(f'        }}\n')
        lines.append(f'      ]\n')
        lines.append(f'    }},\n')
  return (lines, fields)

def irq_gen_status(connections, clist, ctype="prod", pref=""):
  lines=[]
  otype="cons" if ctype=="prod" else "prod"
  producer_consumer = "producer" if ctype=="prod" else "consumer"
  # get amount of needed fields:
  fields=0
  for pr in clist:
    res=list(filter(lambda d: d[ctype] in pr, connections))
    fields+=(len(res))

  idx=0
  postfix=''
  for pr in clist:
    res=list(filter(lambda d: d[ctype] in pr, connections))
    for i, d in enumerate(res):
      ridx=math.floor(idx/64)
      if idx%64==0:
        if fields>64:
          postfix=f'_{ridx}'
          # close previous register if not first one
          if math.floor(idx/64) > 0:
            lines.append(f'      ]\n')
            lines.append(f'    }},\n')
        lines.append(f'    {{ name: "{pref}IRQ_GEN_SAT_{str_conv(ctype)}_STATUS{postfix}",\n')
        lines.append(f'      desc: \'\'\'\n\
          Status of the interupt of the token manager for the generic {producer_consumer} counter.\n\
          The bits are sticky and cleared when writing a 1 to that bit.\n\
          Note: bit will be set again when the irq condition (saturation) is still there.\n\
          \'\'\',\n')
        lines.append(f'      swaccess: "rw1c",\n')
        lines.append(f'      hwaccess: "hrw",\n')
        lines.append(f'      fields: [\n')

      lines.append(f'        {{\n')
      lines.append(f'          bits: "{idx-ridx*64}"\n')
      lines.append(f'          name: "{str_conv(d[ctype])}_TOK_{str_conv(ctype)}_{str_conv(d[otype])}"\n')
      lines.append(f'          desc: "{str_conv(d[ctype])}_TOK_{str_conv(ctype)}_{str_conv(d[otype])} saturated and raised the IRQ."\n')
      lines.append(f'          resval: 0x0\n')
      lines.append(f'        }}\n')
      idx+=1
  lines.append(f'      ]\n')
  lines.append(f'    }},\n')
  return (lines, fields)

def irq_gen_en(connections, clist, ctype="prod", pref=""):
  lines=[]
  otype="cons" if ctype=="prod" else "prod"
  producer_consumer = "producer" if ctype=="prod" else "consumer"
  # get amount of needed fields:
  fields=0
  for pr in clist:
    res=list(filter(lambda d: d[ctype] in pr, connections))
    fields+=(len(res))

  idx=0
  postfix=''
  for pr in clist:
    res=list(filter(lambda d: d[ctype] in pr, connections))
    for i, d in enumerate(res):
      ridx=math.floor(idx/64)
      if idx%64==0:
        if fields>64:
          postfix=f'_{ridx}'
          # close previous register if not first one
          if math.floor(idx/64) > 0:
            lines.append(f'      ]\n')
            lines.append(f'    }},\n')
        lines.append(f'    {{ name: "{pref}IRQ_GEN_SAT_{str_conv(ctype)}_EN{postfix}",\n')
        lines.append(f'      desc: \'\'\'\n\
          Status of the interupt of the token manager for the generic {producer_consumer} counter.\n\
          The bits are sticky and cleared when writing a 1 to that bit.\n\
          Note: bit will be set again when the irq condition (saturation) is still there.\n\
          \'\'\',\n')
        lines.append(f'      swaccess: "rw",\n')
        lines.append(f'      hwaccess: "hro",\n')
        lines.append(f'      fields: [\n')

      lines.append(f'        {{\n')
      lines.append(f'          bits: "{idx-ridx*64}"\n')
      lines.append(f'          name: "IRQ_{str_conv(d[ctype])}_TOK_{str_conv(ctype)}_{str_conv(d[otype])}_EN"\n')
      lines.append(f'          desc: "Enable the IRQ for {str_conv(d[ctype])}_TOK_{str_conv(ctype)}_{str_conv(d[otype])} saturation."\n')
      lines.append(f'          resval: 0x0\n')
      lines.append(f'        }}\n')
      idx+=1
  lines.append(f'      ]\n')
  lines.append(f'    }},\n')
  return (lines, fields)

def irq_swep_status(clist, typen="SAT", desc="saturation", mess="saturated", opt="cons prod", pref=""):
  lines=[]
  lines.append(f'    {{ name: "{pref}IRQ_SWEP_{typen}_STATUS",\n')
  lines.append(f'      desc: \'\'\'\n\
    Status of the interupt of the token manager for the software endpoints that {mess}.\n\
    The bits are sticky and cleared when writing a 1 to that bit.\n\
    Note: bit will be set again when the irq condition ({desc}) is still there.\n\
    \'\'\',\n')
  lines.append(f'      swaccess: "rw1c",\n')
  lines.append(f'      hwaccess: "hrw",\n')
  lines.append(f'      fields: [\n')
  if "cons" in opt:
    for idx, d in enumerate(clist):
      lines.append(f'        {{\n')
      lines.append(f'          bits: "{idx}"\n')
      lines.append(f'          name: "SWEP_CONS_{str_conv(d)}"\n')
      lines.append(f'          desc: "Consume counter on software endpoint {str_conv(d)} {mess}."\n')
      lines.append(f'          resval: 0x0\n')
      lines.append(f'        }}\n')
  if "prod" in opt:
    for idx, d in enumerate(clist):
      lines.append(f'        {{\n')
      lines.append(f'          bits: "{idx}"\n')
      lines.append(f'          name: "SWEP_PROD_{str_conv(d)}"\n')
      lines.append(f'          desc: "Producer counter on software endpoint {str_conv(d)} {mess}"\n')
      lines.append(f'          resval: 0x0\n')
      lines.append(f'        }}\n')
  lines.append(f'      ]\n')
  lines.append(f'    }},\n')
  return lines

def irq_swep_en(clist, typen="SAT", desc="saturation", mess="saturated", opt="cons prod", pref=""):
  lines=[]
  lines.append(f'    {{ name: "{pref}IRQ_SWEP_{typen}_EN",\n')
  lines.append(f'      desc: \'\'\'\n\
    Enable the corresponding interrupt for the software endpoints that {mess}.\n\
    \'\'\',\n')
  lines.append(f'      swaccess: "rw",\n')
  lines.append(f'      hwaccess: "hro",\n')
  lines.append(f'      fields: [\n')
  if "cons" in opt:
    for idx, d in enumerate(clist):
      lines.append(f'        {{\n')
      lines.append(f'          bits: "{idx}"\n')
      lines.append(f'          name: "IRQ_SWEP_CONS_{str_conv(d)}_EN"\n')
      lines.append(f'          desc: "Enable IRQ consume counter on software endpoint {str_conv(d)} {mess}."\n')
      lines.append(f'          resval: 0x0\n')
      lines.append(f'        }}\n')
  if "prod" in opt:
    for idx, d in enumerate(clist):
      lines.append(f'        {{\n')
      lines.append(f'          bits: "{idx}"\n')
      lines.append(f'          name: "IRQ_SWEP_PROD_{str_conv(d)}_EN"\n')
      lines.append(f'          desc: "Enable IRQ producer counter on software endpoint {str_conv(d)} {mess}"\n')
      lines.append(f'          resval: 0x0\n')
      lines.append(f'        }}\n')
  lines.append(f'      ]\n')
  lines.append(f'    }},\n')
  return lines

def irq_top_map (clist, pref=""):
  lines=[]
  lines.append(f'    {{ name: "{pref}IRQ_MAPPING_ERROR_STATUS",\n')
  lines.append(f'      desc: \'\'\'\n\
    If set there was a VUID_TO_UID mapping error during the token to OCPL mapping.\n\
    This happens when the used entry is set to 0\n\
    \'\'\',\n')
  lines.append(f'      swaccess: "rw1c",\n')
  lines.append(f'      hwaccess: "hrw",\n')
  lines.append(f'      fields: [\n')

  for idx, d in enumerate(clist):
    lines.append(f'        {{\n')
    lines.append(f'          bits: "{idx}"\n')
    lines.append(f'          name: "MAP_ERROR_{str_conv(d)}"\n')
    lines.append(f'          desc: "VUID_TO_UID mapping error during the token to OCPL mapping for {str_conv(d)}."\n')
    lines.append(f'          resval: 0x0\n')
    lines.append(f'        }}\n')
  lines.append(f'      ]\n')
  lines.append(f'    }},\n')
  return lines
