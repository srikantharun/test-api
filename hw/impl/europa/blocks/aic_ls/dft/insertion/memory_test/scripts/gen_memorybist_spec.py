#!/usr/bin/env python3

import sys
import os
import argparse
import logging
import hjson

REPO_ROOT = os.environ['REPO_ROOT']

logger = logging.getLogger(__name__)

# Initialize parser
parser = argparse.ArgumentParser(description="Generate MemoryBist specification for LS main memory array.")

parser.add_argument(
  '--verbosity',
  default='info',
  help='Verbosity of the script.',
  type=str,
  choices=['critical', 'error', 'warning', 'info', 'debug', 'notset']
)

parser.add_argument(
  '-f',
  default=os.path.join(REPO_ROOT, 'hw/impl/europa/blocks/aic_ls/dft/insertion/memory_test/data/memory_grouping.hjson'),
  help='Memory grouping hjson file',
  type=str,
)

args = parser.parse_args()

def get_macro_string(mbank):
   bank = mbank%4
   minibank = mbank//4
   return f'u_aic_ls/u_l1/u_l1_mem/g_sbank[{bank}].u_sub_bank/g_mini_bank[{minibank}].u_mini_bank/g_macro[0].u_macro/gen_inst.i_sramspehd'

def print_spec(memory_grouping):
    first_controller = True
    first_controller_str = ''
    first_memory = True
    first_memory_str = ''
    mif_num = 1

    print('MemoryBist {') # open MemoryBist
    print('  ijtag_host_interface : Sib(mbist);')
    for controller in memory_grouping['controllers']:
        logging.debug(f'Controller: {controller}')
        if first_controller:
            first_controller_str = controller
            first_controller = False
        print(f'  Controller({controller}) {{') # open Controller
        print(f'    clock_domain_label: i_clk;')
        print(f'    Step {{') # open Step
        for memory in memory_grouping['controllers'][controller]:
            logging.debug(f'Memory: {memory}')
            print(f"      {'MemoryInterface(' if mif_num == 1 else 'ReusedMemoryInterface('}m{mif_num}) {{")
            print(f"        instance_name : {get_macro_string(memory)};")
            if not first_memory:
                print(f"        reused_interface_id : {first_controller_str}:{first_memory_str};")
            print(f'      }}')
            if first_memory:
                first_memory_str = f'm{mif_num}'
                first_memory = False
            mif_num += 1
        print('    }') # close Step
        print('  }') # close Controller
    print('}') # close MemoryBist

def main():
  logging.basicConfig(
    level=args.verbosity.upper(),
    format="[%(levelname)s]: %(message)s",
    handlers=[
      logging.StreamHandler(stream=sys.stdout)
    ]
  )

  # Read memory grouping hjson file
  with open(args.f, 'r') as f:
    memory_grouping = hjson.load(f)

  logging.debug(f'Memory grouping: {memory_grouping}')

  # Generate MemoryBist specification
  print_spec(memory_grouping)

if __name__ == '__main__':
  main()
