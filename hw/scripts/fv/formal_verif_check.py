#!/usr/bin/env python3

import argparse
import sys
import re


re_dict = {
   'Proven'       : re.compile(r'#\s+proven')
  ,'Inconclusive' : re.compile(r'#\s+inconclusive')
  ,'Falsified'    : re.compile(r'#\s+falsified')
  ,'Error'        : re.compile(r'\[Error\]')
}

def get_log(rpt):
  """
  Parameters
  ----------
  """
  try:
    with open(rpt, 'r') as f:
      return f.readlines()
  except:
    print('Fatal: Log not found!')
    sys.exit(-1)
  

if __name__ == '__main__':

  # Getting arguments
  parser = argparse.ArgumentParser(description='Processing Formal Verif results.')
  parser.add_argument('-r', '--report', dest='rpt', default=None, required=True,
                      help='Formal Verification report')
  parser.add_argument('-w', '--waive-error', dest='waive_errors', default=False, action='store_true',
                      help='Formal Verification report')

  args = parser.parse_args()

  inconclusive = False
  proven = False
  for line in get_log(args.rpt):
    for key, rx in re_dict.items():
      match_re = rx.search(line)
      if match_re:
        if key == 'Falsified':
          print('Error: Falsified assertion found!')
          sys.exit(-1)
        elif key == 'Inconclusive':
          inconclusive = True
        elif key == 'Proven':
          proven = True
        elif key == 'Error':
          if args.waive_errors:
            print('Warning: Some connections do not match to RTL!')
            sys.exit(0)
          else:
            print('Error: Error found! Check the Log')
            print(line)
            sys.exit(-1)
  
  if proven:
    if inconclusive:
      print('Warning: Inconclusive assertion found!')
      sys.exit(1)
    else:
      print('Info: All assertions proven!')
      sys.exit(0)
  else:
    print('Error: Zero assertions proven!')
    sys.exit(-1)
