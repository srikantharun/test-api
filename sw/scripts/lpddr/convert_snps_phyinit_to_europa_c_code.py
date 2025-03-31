import argparse
import re
import sys
import os
import copy
from ipyxact.ipyxact import Component
from dataclasses import dataclass, field
from typing import Dict, List

LPDDR_PHY_DEFAULT_MULTIPLIER = 1
LPDDR_PHY_ICCM_BANKS = 2
LPDDR_PHY_DCCM_BANKS = 1
DEFAULT_TOP_FUNC_NAME = 'lpddr_phy_init_custom'
DEFAULT_XML_FILE = os.environ["DDR_PHY_RTL_PATH"] + "/export/dwc_lpddr5xphy_top.xml"

# OVERRIDES
DM_EN_DCCM_OVERRIDES = [
  { 'offset': 0x38, 'value':  0x4f08 },
  { 'offset': 0x44, 'value':  0x4f08 },
  { 'offset': 0x6a, 'value':   0x84d },
  { 'offset': 0x76, 'value':   0x84d },
]

@dataclass
class ipxactXmlUtil:
  filename: str
  component: Component = None

  @staticmethod
  def search_addr_block_for_reg_addr(block, reg_addr: int):
    for reg in sorted(block.register, key=lambda a: a.addressOffset):
      if reg_addr == (block.baseAddress + reg.addressOffset):
        return reg
    return None

  def search_mem_maps_for_addr_block(self, reg_addr: int):
    for m in self.component.memoryMaps.memoryMap:
      for block in m.addressBlock:
        if block.baseAddress <= reg_addr <= (block.baseAddress + block.range - 1):
          return block
    return None

  def get_mem_block_range(self, block_name: str) -> int:
    for m in self.component.memoryMaps.memoryMap:
      for block in m.addressBlock:
        if block_name == block.name:
          return block.range
    return None

  def search_for_reg(self, reg_addr: int):
    the_block = self.search_mem_maps_for_addr_block(reg_addr=reg_addr)
    if the_block:
      the_reg = ipxactXmlUtil.search_addr_block_for_reg(block=the_block, reg_addr=reg_addr)
    else:
      the_reg = None

    return the_block, the_reg

  def __post_init__(self):
    self._load_component_from_file()

  def _load_component_from_file(self):
    with open(self.filename) as f:
      self.component = Component()
      self.component.load(f)


def parse_args():
  parser = argparse.ArgumentParser(description='Convert Synopsys PHY Init FW pseudo-code to triton FW C code')
  parser.add_argument('txt_file', help='Input Synopsys PHY Init FW pseudo-code file (dwc_ddrphy_phyinit_out_lpddr4x*.txt)')
  parser.add_argument('-x', '--xml', help='LPDDR PHY IP X-ACT xml file', default=DEFAULT_XML_FILE)
  parser.add_argument('--debug', action='store_true', help='When enabled, it prints out conversion debugging info', default=False)
  parser.add_argument('-i', '--iccm_preload', action='store_true', help='ICCM accesses will be stored in memory preload file', default=None)
  parser.add_argument('-d', '--dccm_preload', action='store_true', help='DCCM accesses will be stored in memory preload file', default=None)
  parser.add_argument('-o', '--out_dir', help='Directory to store generated files', required=True)
  parser.add_argument('-p', '--prefix', action='store', type=str, help='Prefix for generated files & name of the resulting C function', default=DEFAULT_TOP_FUNC_NAME)
  parser.add_argument('-s', '--speed_grade', help='Any of 800, 1600', required=True)
  parser.add_argument('-sk', '--skip_train', help='when enabled, waitFWDone function is changed, firmware progresses after device initialization', action='store_true', default=False)
  parser.add_argument('--dm_en', action='store_true', help='When enabled, it overrides DCCM-related accesses to enable Data Mask', default=False)
  parser.add_argument('--overwrite', action='store_true', help='When enabled, it will overwrite existing files', default=False)
  parser.add_argument('--gen_io_ret', action='store_true', help='When enabled, it will generate IO retention save process ', default=False)
  parser.add_argument('--diagnostic', action='store_true', help='When enabled, it will diagnostic tests ', default=False)
  parser.add_argument('--gen_texhex', action='store_true', help='When enabled, it will generate texhex files', default=False)
  return parser.parse_args()

# Regex for detecting the APB 16-bit Write function; example format:
#   dwc_ddrphy_apb_wr(32'h30022,32'h2);
REGEX_APB_WR32 = \
  "^dwc_ddrphy_apb_wr" + "\(" + \
  "32'h" + "([0123456789abcdef]+)" + "," + \
  "32'h" + "([0123456789abcdef]+)" + "\);"

# Regex for detecting the APB 16-bit Read function; example format:
#   dwc_ddrphy_apb_rd(32'h90206);
REGEX_APB_RD16 = \
  "^dwc_ddrphy_apb_rd" + "\(" + \
  "32'h" + "([0123456789abcdef]+)" + "\);"

# Regex for detecting any function without params; example formats:
#   dwc_ddrphy_phyinit_userCustom_overrideUserInput();
#   dwc_ddrphy_phyinit_userCustom_A_bringupPower ( );
#   dwc_ddrphy_phyinit_userCustom_B_startClockResetPhy( ) ;
REGEX_ANY_FUNC_WITHOUT_PARAMS = \
  "^([a-zA-Z0-9_]+)" + "\s*" + \
  "\(" + "\s*" + "\)" + \
  "\s*" + ";"

# Regex for detecting any function with an int param; example formats:
#  dwc_ddrphy_phyinit_userCustom_H_readMsgBlock(0);
#  dwc_ddrphy_phyinit_userCustom_E_setDfiClk(0);
REGEX_ANY_FUNC_WITH_ONE_INT_PARAM = \
  "^([a-zA-Z0-9_]+)" + "\s*" + \
  "\(" + "\s*" + "([0-9]+)" + "\s*" + "\)" + \
  "\s*" + ";"

# Regex for detecting any function with only one phyctx param:
#  dwc_ddrphy_phyinit_userCustom_overrideUserInput (phyctx);
#  dwc_ddrphy_phyinit_userCustom_A_bringupPower (phyctx);
REGEX_ANY_FUNC_WITH_ONE_CHAR_PARAM = \
  "^([a-zA-Z0-9_]+)" + "\s*" + \
  "\(" + "\s*" + "([a-z]+)" + "\s*" + "\)" + \
  "\s*" + ";"

# Regex for detecting any function with one phyctx and one int params:
#  dwc_ddrphy_phyinit_userCustom_E_setDfiClk (phyctx, 0);
#  dwc_ddrphy_phyinit_userCustom_H_readMsgBlock (phyctx, 0);
REGEX_ANY_FUNC_WITH_ONE_CHAR_ONE_INT_PARAM = \
  "^([a-zA-Z0-9_]+)" + "\s*" + \
  "\(" + "\s*" + "([a-z]+)" + "\s*" + "," + "\s*" + "([0-9]+)" + "\s*" + "\)" + \
  "\s*" + ";"

# removes comments/blanks if required
def filter_phyinit_line(line: str, preserve_comments: bool=False, preserve_blanks: bool=False) -> str:
  line = line.strip()
  # if "Start of dwc_ddrphy_phyinit_userCustom_customPreTrain" in line:
  #   return "dwc_ddrphy_phyinit_userCustom_customPreTrain();"
  # Return line marking when the ICCM should be load for using methods lpddr_iccm_init and lpddr_iccm_init_2D
  if "[dwc_ddrphy_phyinit_WriteOutMem] STARTING. offset 0x50000" in line:
    return "load_iccm_init"
  # Return read statements that are commented and remove "// "
  if line[:20] == '// dwc_ddrphy_apb_rd':
    return line[3:]
  # filter blanks
  if len(line.strip()) == 0 and not preserve_blanks:
    return None
  # filter comments
  if line[:2] == '//' and not preserve_comments:
    return None
  # If it is FBW, the DfiMode does not need to be altered since the default value (0x5) is the desired
  # one to use the DFI as Lockstep
  if 'fbw' in args.prefix and "dwc_ddrphy_apb_wr(32'h20018," in line:
    return None

  return line

# returns a dictionary with the function & its params {'func': function_name, 'param': parameters}
#
def get_structured_access_from_phyinit_line(line: str):
  ret_func = None
  ret_param = None
  ret_value = None
  # search for APB Write function (the only one with params afaik)
  match = re.search(REGEX_APB_WR32, line)
  if match:
    # LPDDR PHY addresses need a Left Shift of 1 to convert to triton address
    address = int(match.group(1).strip(), 16)
    data = int(match.group(2).strip(), 16)# search for any function without params
    ret_func = 'set_reg_u32'
    ret_param = {'addr': address, 'data': data}
  # search for APB Read function
  match = re.search(REGEX_APB_RD16, line)
  if match:
    # LPDDR PHY addresses need a Left Shift of 1 to convert to triton address
    address = int(match.group(1).strip(), 16)
    ret_func = 'get_reg_u16'
    ret_param = {'addr': address}
  match = re.search(REGEX_ANY_FUNC_WITHOUT_PARAMS, line)
  if match:
    ret_func = match.group(1)
    ret_param = None
  # search for any function with an int param
  match = re.search(REGEX_ANY_FUNC_WITH_ONE_INT_PARAM, line)
  if match:
    ret_func = match.group(1)
    ret_param = match.group(2)
  match = re.search(REGEX_ANY_FUNC_WITH_ONE_CHAR_PARAM, line)
  if match:
    ret_func = match.group(1)
    ret_param = match.group(2)
  match = re.search(REGEX_ANY_FUNC_WITH_ONE_CHAR_ONE_INT_PARAM, line)
  if match:
    ret_func = match.group(1)
    ret_param = match.group(2)
    ret_value = match.group(3)
  return {'func': ret_func, 'param': ret_param, 'value': ret_value}

# returns a dict with APB register write details
#   {'block': block_name, 'reg': register_name, 'offset': address_offset (if any), 'data': register write value)
def get_apb16_access_reg_details(address: int, data:int, ipxact_util: ipxactXmlUtil, multiplier: int=1):
  block = ipxact_util.search_mem_maps_for_addr_block(reg_addr=address)
  if block:
    reg = ipxact_util.search_addr_block_for_reg_addr(block=block, reg_addr=address)
    if reg is None:
      addr_offset = (address - block.baseAddress) * multiplier
      reg_name = None
    else:
      addr_offset = None
      reg_name = reg.name if not uniquify else f'{block.name}_{reg.name}'
    return {'block': block.name, 'reg': reg_name, 'offset': addr_offset, 'data': data}
  else:
    return None # ret_warn = f'found APB Write statement but could not find block with address {hex(address)} (address multiplied: {hex(address * multiplier)})'

# converts known statements (calls to functions) from SNPS pseudo-code to triton FW C code
def convert_phyinit_line_NEW(line: str, ipxact_util: ipxactXmlUtil, uniquify: bool=False, multiplier: int=1, dccm_overrides: List[Dict]=[], iccm_overrides: List[Dict]=[]):
  ret_cstr = None
  ret_ccm = None
  ret_warn = None

  funcparams = get_structured_access_from_phyinit_line(line)
  if funcparams and funcparams['func'] == 'set_reg_u32':
    addr = funcparams['param']['addr']
    data = funcparams['param']['data']
    # retrieve reg access details structure
    apb16_details = get_apb16_access_reg_details(address=addr, data=data, ipxact_util=ipxact_util, multiplier=multiplier)
    if apb16_details is None:
      ret_warn = f'found APB Write statement but could not find block with address {hex(addr)} (address multiplied: {hex(addr * multiplier)})'
    else:
      # Apply DCCM overrides, if any
      if apb16_details['block'] == 'DCCM' and len(dccm_overrides) > 0:
        for override in dccm_overrides:
          if override['offset'] == apb16_details['offset']:
            apb16_details['data'] = override['value']
      # Apply ICCM overrides, if any
      if apb16_details['block'] == 'ICCM' and len(iccm_overrides) > 0:
        for override in iccm_overrides:
          if override['offset'] == apb16_details['offset']:
            apb16_details['data'] = override['value']
      # Return structured CCM
      if apb16_details['block'] == 'DCCM' or apb16_details['block'] == 'ICCM':
        ret_ccm = {'name': apb16_details['block'], 'addr': apb16_details['offset'], 'data': data}
      # create C code
      if apb16_details['block'] == "ICCM" or apb16_details['block'] == "DCCM" or apb16_details['block'] == "ACSM" or apb16_details['block'] == "PIE":
        reg_field = f'{apb16_details["block"]}_BaseAddress + {hex(apb16_details["offset"])}'
      else:
        reg_field = f'{apb16_details["reg"]}_AddressOffset'
      data_field = apb16_details['data']
      ret_cstr = f'lpddrPhyWriteReg32({reg_field}, (uint32_t)0x{data_field:08x});'
  elif funcparams and funcparams['func'] == 'get_reg_u16':
    addr = funcparams['param']['addr']
    data = 0
    # retrieve reg access details structure
    apb16_details = get_apb16_access_reg_details(address=addr, data=data, ipxact_util=ipxact_util, multiplier=multiplier)
    if apb16_details is None:
      ret_warn = f'found APB Read statement but could not find block with address {hex(addr)} (address multiplied: {hex(addr * multiplier)})'
    else:
      # Apply DCCM overrides, if any
      if apb16_details['block'] == 'DCCM' and len(dccm_overrides) > 0:
        for override in dccm_overrides:
          if override['offset'] == apb16_details['offset']:
            apb16_details['data'] = override['value']
      # Apply ICCM overrides, if any
      if apb16_details['block'] == 'ICCM' and len(iccm_overrides) > 0:
        for override in iccm_overrides:
          if override['offset'] == apb16_details['offset']:
            apb16_details['data'] = override['value']
      # Return structured CCM
      if apb16_details['block'] == 'DCCM' or apb16_details['block'] == 'ICCM':
        ret_ccm = {'name': apb16_details['block'], 'addr': apb16_details['offset'], 'data': data}
      # create C code
      if apb16_details['block'] == "ICCM" or apb16_details['block'] == "DCCM":
        reg_field = f'{apb16_details["block"]}_BaseAddress + {hex(apb16_details["offset"])}'
      else:
        reg_field = apb16_details['reg']
      # Generating print statement that will print the register values after training
      ret_cstr = f'printf("{reg_field} = 0x%04x\\n", get_reg_u16({reg_field}));'
  elif funcparams and funcparams['param'] and funcparams['value']:
    # custom function with parameter and value
    ret_cstr = f'{funcparams["func"]}({funcparams["param"]},{funcparams["value"]});'
  elif funcparams and funcparams['param']:
    # custom function with parameter
    ret_cstr = f'{funcparams["func"]}({funcparams["param"]});'
  elif funcparams:
    # custom function without parameter
    ret_cstr = f'{funcparams["func"]}();'
  else:
    # warning
    ret_warn = 'unknown statement'

  return ret_cstr, ret_ccm, ret_warn

# returns a list with the contents of each bank (list of lists)
def build_ccm_mem_arrays(ccm_contents: List, mem_words: int, banks: int, multiplier: int) -> List[List]:
  words_per_bank = mem_words // banks

  # step 1: store in ccm_words = {addr0: data0, add1: data1, ..., addrN: dataN}
  ccm_words = {}
  for c in ccm_contents:
    ccm_words[c['addr']] = c['data']
  # step 2: build an array with each bank's contents
  ccm_arrays = [ [] ]
  i = int(0)
  ibank = 0
  while (i < mem_words):
    if (i // words_per_bank) > ibank:
      # crossed the bank limit
      ibank += 1
      ccm_arrays.append([])
    addr = i * multiplier
    this_word = ccm_words[addr] if addr in ccm_words else 0
    ccm_arrays[ibank].append(this_word)
    i += 1
  return ccm_arrays

# writes the I/DCCM arrays generated by build_ccm_mem_arrays to <flprefix>.bank<i> files
def write_ccm_files(ccm_arrays: List[List], flprefix: str):
  for ibank, ccm_arr in enumerate(ccm_arrays):
    with open(f'{flprefix}.bank{ibank}', "w") as flout:
      # .texthex format needs 2 16-bit words per line, high word first, low word then
      for i, word in enumerate(ccm_arr):
        if i % 2 == 0:
          word_lo = f'{word:04x}'
        else:
          word_hi = f'{word:04x}'
          flout.write(word_hi + word_lo + '\n')

def get_c_code_head(args, func_name: str):
  ret = []
  ret.append(f'/**')
  ret.append('')
  ret.append(f'Automatically generated by {sys.argv[0]} using the parameters:')
  ret.append(f'')
  for v in vars(args):
    ret.append(f'  {v}: {vars(args)[v]}')
  ret.append(f'')
  ret.append(f'  full command-line args: {str(sys.argv)}')
  ret.append(f'')
  ret.append(f'**/')
  ret.append('')
  # ret.append('#ifdef SYS_CTRL\n')
  # ret.append('#include <drv/lpddr/ddr_phy_memorymap.h>')
  ret.append('#include "drv_lpddr.h"')
  if args.gen_io_ret:
    ret.append('#include <stdio.h>')
  if args.diagnostic:
    ret.append('#include <drv/lpddr/drv_lpddr_diagnostic.h>')
  ret.append('')
  ret.append(f'void {func_name}()' + ' {')
  return ret

def get_c_code_tail() -> str:
  # return '}' + '\n' + '#endif // SYS_CTRL' + '\n'
  return '}' + '\n'

def update_cstr(cstr, args):

    if 'setDfiClk' in cstr:
        str = args.speed_grade
        if str=='800':
            cstr = cstr.replace('0','5')
        elif str=='1600':
            cstr = cstr.replace('0','4')
        elif str=='2400':
            cstr = cstr.replace('0','3')
        elif str=='3200':
            cstr = cstr.replace('0','2')
        elif str=='4267':
            cstr = cstr.replace('0','0')

    if 'overrideUserInput' in cstr:
        cstr = '//' + cstr

    if 'bringupPower' in cstr:
        cstr = '//' + cstr

    if 'startClockResetPhy' in cstr:
        cstr = '//' + cstr

    if 'customPostTrain' in cstr:
        cstr = '//' + cstr

    if 'enterMissionMode' in cstr:
        cstr = '//' + cstr

    if 'readMsgBlock' in cstr:
      if args.diagnostic and 'readMsgBlock(0)' in cstr:
        cstr = "#ifdef SILICON_TEST\n" + cstr
        if '2D' not in args.prefix:
            cstr = cstr + "\n  #ifdef DIAGNOSTIC_TEST_4\n"
            cstr = cstr + "    diagnostic_test_4();"
            cstr = cstr + "\n  #elif DIAGNOSTIC_TEST_5\n"
            cstr = cstr + "    diagnostic_test_5();"
            cstr = cstr + "\n  #elif DIAGNOSTIC_TEST_6\n"
            cstr = cstr + "    diagnostic_test_6();"
            cstr = cstr + "\n  #endif"
        cstr = cstr + "\n#endif"
      elif args.diagnostic and 'readMsgBlock(1)' in cstr:
        cstr = "#ifdef SILICON_TEST\n" + cstr
        cstr = cstr + "\n  #ifdef DIAGNOSTIC_TEST_4\n"
        cstr = cstr + "    diagnostic_test_4();"
        cstr = cstr + "\n  #elif DIAGNOSTIC_TEST_5\n"
        cstr = cstr + "    diagnostic_test_5();"
        cstr = cstr + "\n  #elif DIAGNOSTIC_TEST_6\n"
        cstr = cstr + "    diagnostic_test_6();"
        cstr = cstr + "\n  #endif"
        cstr = cstr + "\n#endif"
      else:
        cstr = "#ifdef SILICON_TEST\n" + cstr + "\n#endif"

    if 'waitFwDone' in cstr:
      if args.skip_train:
        cstr = cstr.replace('()','(1)')
      else:
        cstr = cstr.replace('()','(0)')

    return cstr

if __name__ == '__main__':
  args = parse_args()
  multiplier = LPDDR_PHY_DEFAULT_MULTIPLIER
  uniquify = True

  ipxact_util = ipxactXmlUtil(filename=args.xml)
  ICCM_WORD_RANGE = ipxact_util.get_mem_block_range("ICCM")
  DCCM_WORD_RANGE = ipxact_util.get_mem_block_range("DCCM")
  FUNC_NAME = args.prefix if args.prefix else DEFAULT_TOP_FUNC_NAME

  iccm_contents = []
  dccm_contents = []
  prev_iccm_addr = None

  if not os.path.exists(args.out_dir):
    os.mkdir(args.out_dir)
  elif os.path.isdir(args.out_dir):
    # dir exists
    pass
  else:
    # exists but it's a file
    sys.exit("provided out_dir arg is a file")

  if args.dm_en:
    dccm_overrides = copy.deepcopy(DM_EN_DCCM_OVERRIDES)
  else:
    dccm_overrides = []
  iccm_overrides = [] # no ICCM overrides required as of now

  if args.gen_io_ret:
    # This file is only generated when the IO retention generation is enabled
    # Contains  series of prints of all the necessary registers (section 12.2 of PHY Training Firmware Application Note)
    flname_c_customPostTrain = os.path.join(args.out_dir, 'dwc_ddrphy_phyinit_userCustom_customPostTrain.c')
  else:
    flname_c_code = os.path.join(args.out_dir, FUNC_NAME + '.c')
    flname_prefix_iccm = os.path.join(args.out_dir, FUNC_NAME + '.ICCM.texthex')
    flname_prefix_dccm = os.path.join(args.out_dir, FUNC_NAME + '.DCCM.texthex')

  # make sure we don't accidentally overwrite any file
  if not args.overwrite:
    check_files = [flname_c_code]
    if args.iccm_preload:
      for ibank in range(LPDDR_PHY_ICCM_BANKS):
        check_files.append(f'{flname_prefix_iccm}.bank{ibank}')

    if args.dccm_preload:
      for ibank in range(LPDDR_PHY_DCCM_BANKS):
        check_files.append(f'{flname_prefix_dccm}.bank{ibank}')

    for filename in check_files:
      if os.path.exists(filename):
        sys.exit(f"File already exists -- aborting -- file: {filename}")

  file_inp = open(args.txt_file, 'r')

  if args.gen_io_ret:
    file_c_customPostTrain = open(flname_c_customPostTrain, 'w')
  else:
    file_c_code = open(flname_c_code, 'w')

  iccm_load_replaced = 0
  reached_customPostTrain = 0
  iccm_load_init = 0

  # 1. C code header
  if args.gen_io_ret:
    for line in get_c_code_head(args=args, func_name='dwc_ddrphy_phyinit_userCustom_customPostTrain'):
      file_c_customPostTrain.write(line + '\n')
  else:
    for line in get_c_code_head(args=args, func_name=FUNC_NAME):
      file_c_code.write(line + '\n')

  # 2. iterate input file
  for i, line in enumerate(file_inp):
    if args.debug: print(f'// {i:4d} {line}') # DBG
    line = filter_phyinit_line(line, preserve_comments=False, preserve_blanks=False)
    if line is not None:
      cstr, ccm, warnstr = convert_phyinit_line_NEW(line=line, ipxact_util=ipxact_util, uniquify=uniquify, \
        dccm_overrides=dccm_overrides, iccm_overrides=iccm_overrides, multiplier=multiplier)
      cstr = update_cstr(cstr, args)

      if args.gen_io_ret:
        if line == 'dwc_ddrphy_phyinit_userCustom_customPostTrain ();':
          # For IO retention, just need to analyse the accesses after customPostTrain
          reached_customPostTrain = 1
        if line == 'dwc_ddrphy_phyinit_userCustom_J_enterMissionMode ();':
          reached_customPostTrain = 0

      # I/DCCM content detect & store
      if ccm is not None and ccm['name'] == 'ICCM':
        iccm_contents.append({'addr': ccm['addr'], 'data': ccm['data']})
      elif ccm is not None and ccm['name'] == 'DCCM':
        dccm_contents.append({'addr': ccm['addr'], 'data': ccm['data']})
      # line printout
      if warnstr is not None:
        warnprint = f'// WARNING @ l. {i}: {warnstr} -- warning generated by {sys.argv[0]} on this line: {line}'
        if not args.gen_io_ret:
          file_c_code.write(warnprint + '\n')
        if args.debug: print(warnprint)
      elif ccm is not None and ((ccm['name'] == 'ICCM' and args.iccm_preload) or (ccm['name'] == 'DCCM' and args.dccm_preload)):
        # don't print, its ICCM/DCCM part with ICCM/DCCM preload enabled
        if args.debug: print(f'// {i:4d} {cstr}' + f'[{ccm["name"]}]' if ccm is not None else '') # DBG
        # if iccm_load_replaced==0:
        #   if not args.gen_io_ret:
        #     file_c_code.write(f'#ifdef SILICON_TEST\n')
        #     file_c_code.write(f'    lpddr_iccm_init();\n')
        #     file_c_code.write(f'#endif\n')
        #   iccm_load_replaced=1
      else:
        if reached_customPostTrain == 1 and line != 'dwc_ddrphy_phyinit_userCustom_customPostTrain ();':
          if args.gen_io_ret:
            file_c_customPostTrain.write(f'  {cstr}\n')
        else:
          if not args.gen_io_ret:
            if line == 'dwc_ddrphy_phyinit_userCustom_customPostTrain ();':
              file_c_code.write(f'#ifdef SILICON_TEST\n')
              file_c_code.write(f'  #ifdef CUSTOM_POST_TRAIN\n')
              if not args.skip_train:
                file_c_code.write(f'    dwc_ddrphy_phyinit_userCustom_customPostTrain();\n')
              else:
                file_c_code.write(f'    lpddr_load_trained_phy_register_values();\n')
              file_c_code.write(f'  #endif\n')
              file_c_code.write(f'#endif\n')
            else:
              # Code to add lpddr_iccm_init and lpddr_iccm_init_2D methods to output C method
              if line == 'load_iccm_init':
                if iccm_load_init == 0:
                  file_c_code.write(f'#ifdef SILICON_TEST\n')
                  file_c_code.write(f'  lpddr_iccm_init();\n')
                  file_c_code.write(f'#endif\n')
                  iccm_load_init = 1
                elif iccm_load_init == 1:
                  file_c_code.write(f'#ifdef SILICON_TEST\n')
                  file_c_code.write(f'    lpddr_iccm_init_2D();\n')
                  file_c_code.write(f'#endif\n')
                  iccm_load_init = 2
              # Code so that DCCM is set for SimulationOnly mode when not on SILICON
              # Based on section 10.3 of PHY Training Firmware Application Note (Version 1.46)
              # MsgMisc register field with Byte offset 0x01, CSR Addr 0x54000
              elif re.search("dwc_ddrphy_apb_wr\(32'h54000",line):
                file_c_code.write(f'#ifdef SILICON_TEST\n')
                file_c_code.write(f'  {cstr}\n')
                file_c_code.write(f'#else\n')
                file_c_code.write(f'  lpddrPhyWriteReg32(DCCM_BaseAddress + 0x0, (uint32_t)0x0600);\n')
                file_c_code.write(f'#endif\n')
              else:
                file_c_code.write(f'{cstr}\n')
  # 3. write tail
  if args.gen_io_ret:
    file_c_customPostTrain.write(get_c_code_tail())
    file_c_customPostTrain.close()
  else:
    file_c_code.write(get_c_code_tail())
    file_c_code.close()

  file_inp.close()

  # Calling optimize_lpddr_generated_code to reduce size of DCCM accesses in generated C-file
  # if not args.gen_io_ret: os.system("python3 ddr/optimize_lpddr_generated_code.py -f " + flname_c_code)

  if args.gen_texhex:
    if args.iccm_preload is not None and len(iccm_contents) > 0 and not args.gen_io_ret:
      # ICCM file
      ccm_arrays = build_ccm_mem_arrays(ccm_contents=iccm_contents, mem_words=ICCM_WORD_RANGE, banks=LPDDR_PHY_ICCM_BANKS, multiplier=multiplier)
      write_ccm_files(ccm_arrays=ccm_arrays, flprefix=flname_prefix_iccm)
    if args.dccm_preload is not None and len(dccm_contents) > 0 and not args.gen_io_ret:
      # DCCM file
      ccm_arrays = build_ccm_mem_arrays(ccm_contents=dccm_contents, mem_words=DCCM_WORD_RANGE, banks=LPDDR_PHY_DCCM_BANKS, multiplier=multiplier)
      write_ccm_files(ccm_arrays=ccm_arrays, flprefix=flname_prefix_dccm)
