#!/usr/bin/env python3

import argparse
import sys
import re
import hjson

re_dict_cc = {
  'Match'       : re.compile(r'(?P<score>\d+.\d+)\s+(?P<tgl>\d+.\d+)\s(?P<module>\w+)')
}
re_dict_fpv = {
  'Match'       : re.compile(r'(?P<score>\d+.\d+)\s+(?P<line>\d+.\d+)\s+(?P<cond>\d+.\d+)\s+(?P<tgl>\d+.\d+)\s+(?P<module>\w+)')
}

re_dict_app = {
  'cc': re_dict_cc,
  'fpv': re_dict_fpv
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
  
def get_hjson(path):
  try:
    with open(path, 'r') as file:
      return hjson.load(file)
  except IOError as err:
    print(f"Error found opening {path}: {err}")
    sys.exit(-1)

def check_module(module, module_list):
  for elem in module_list:
    if elem in module:
      return True
  else:
    return False

def check_score(data):
  for key, value in data.items():
    if key != 'module':
      if value != '100.00':
        return False
  return True

if __name__ == '__main__':

  # Getting arguments
  parser = argparse.ArgumentParser(description='Processing URG results.')
  parser.add_argument('-r', '--report', dest='rpt', default=None, required=True,
                      help='URG txt dashboard report')
  parser.add_argument('-a', '--app', dest='app', default='fpv', required=True,
                      help='Formal Verif App')
  parser.add_argument('-s', '--sign-off', dest='sign_off', default=None, required=True,
                      help='List of module to sign off')
  parser.add_argument('-w', '--waive-errors', dest='waive_errors', default=False, action='store_true',
                      help='Waive coverage failure')

  args = parser.parse_args()

  sign_off = get_hjson(args.sign_off)

  re_dict = re_dict_app[args.app]

  proven = False
  for line in get_log(args.rpt):
    for key, rx in re_dict.items():
      match_re = rx.search(line)
      if match_re:
        if key == 'Match':
          data = match_re.groupdict()
          if data['module'] not in sign_off:
            continue
          if check_score(data):
            print(f"[{data['module']}] Passed: 100% coverage!")
            proven = True
          else:
            if args.waive_errors:
              print(f"[{data['module']}] Score: {data['score']}% coverage!")
              sys.exit(0)
            else:
              print(f"[{data['module']}] Failed: {data['score']}% coverage!")
              sys.exit(1)
        else:
          print('Error: Error found! Check the Log')
          sys.exit(-1)

  if proven:
    sys.exit(0)
  else:
    print('No match found!')
    sys.exit(-1)
