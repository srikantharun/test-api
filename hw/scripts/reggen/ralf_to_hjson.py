#!/usr/bin/env python3

import argparse
from collections import OrderedDict
import hjson

def parse_args():
    parser = argparse.ArgumentParser(
            description='convert a simple ralf file to hjson in the lowrisc-regtool format (very custom for now)')
    parser.add_argument('file', help='RALF file to parse')
    parser.add_argument('-o','--output', help='output hjson file')
    parser.add_argument('-a','--base-addr', default=0, help='set base address of first system')

    return parser.parse_args()

def get_system_definition(args):

    with open(args.file) as f:
        lines = f.readlines()

    system = OrderedDict({})
    system['clocking'] = [{'clock': "clk_i", 'reset': "rst_n_i"}]
    system['bus_interfaces'] = [{ 'protocol': "tlul", 'direction': "device" }]
    blocks = {}
    system_found = False
    first_block = True

    for line in lines:
        if line.startswith('system '):
            system_name = line.split(' ')[1]
            system['name'] = system_name.lower()
            system_found = True
        if system_found:
            if line.startswith('  bytes'):
                system['regwidth'] = int(line.split(' ')[-1].replace(';\n',''))*8
                system['regalign'] = system['regwidth']
            if line.startswith('  block'):
                curr_block_addr = int(line.split("@'h")[-1].replace(';\n',''),16)
                if first_block:
                    diff_addr = curr_block_addr - args.base_addr
                    block_addr = hex(args.base_addr).split('0x')[-1]
                    first_block = False
                else: 
                    block_addr = hex(curr_block_addr-diff_addr).split('0x')[-1]
                blocks[line.split('block ')[1].split(' ')[0]] = block_addr
    
    return system, blocks

def get_block_definition(name, offset):

    with open(args.file) as f:
        lines = f.readlines()

    registers = []
    track = {
        'block_started' : False,
        'block_ended' : False,
        'register_started' : False,
        'register_ended' : False,
        'field_started' : False,
        'field_ended' : False,
    }
    first_reg = True

    for line in lines:
        if name in line:
            track['block_started'] = True
        if track['block_started']:
            if line.startswith('}'):
                track['block_ended'] = True
            if track['block_ended']: 
                break
            if 'register' in line:
                current_reg = line.split('register ')[1].split(' ')[0]
                current_addr = line.split("@'h")[1].split(' ')[0]
                reg_dict = OrderedDict({'name':current_reg, 'fields':[], 'desc':'none'})
                if first_reg:
                    registers.append({'skipto':f'0x{offset}'})
                else:
                    registers.append({'skipto':f'{hex(int(offset,16)+int(current_addr,16))}'})
                first_reg = False

            if line.startswith('  }'):
                registers.append(reg_dict)

            if 'field' in line:
                fieldname = line.split('field ')[1].split(' ')[0]
                lowerbit = int(line.split(" @")[-1].split(' ')[0])
                field_dict = {'bits':0,'name':fieldname,'desc':'none','resval':0,'hwaccess':'hro'}
            if 'bits' in line:
                upperbit = int(line.split('bits ')[-1].replace(';\n',''))+lowerbit
                field_dict['bits'] = f'{upperbit-1}:{lowerbit}'
            if 'access' in line:
                access = line.split('access ')[-1].replace(';\n','')
                field_dict['swaccess'] = access
            if 'reset' in line:
                resval = line.split('reset ')[-1].split(f"{upperbit-lowerbit}'h")[-1].replace(';\n','')
                field_dict['resval'] = f'0x{resval}'
            if 'volatile' in line:
                field_dict['hwaccess'] = 'hrw'
            if 'attributes' in  line:
                splitline = line.split('attributes ')[-1]
                splitline = splitline.replace('{ ','').replace(' }','')
                attributes = splitline.split(',')
                tags = 'exc'
                for attribute in attributes:
                    if 'NO_REG_BIT_BASH_TEST' in attribute:
                        tags += ':CsrBitBashTest'
                    if 'NO_REG_TESTS' in attribute:
                        tags += ':CsrAllTests'
                reg_dict['tags'] = [tags]
            if line.startswith('    }'):
                reg_dict['fields'].append(field_dict)

    return registers


if __name__ == '__main__':
    args = parse_args()

    system, blocks = get_system_definition(args)
    reg_list = []
    for block,offset in blocks.items():
        reg_list.append(get_block_definition(block, offset))

    flat_reg_list = [x for xs in reg_list for x in xs]

    system['registers'] = flat_reg_list
    
    with open(f"{args.output}", "w") as outfile:
        hjson.dump(system, outfile)
        outfile.write("\n")

