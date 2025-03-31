import re
import tool.signoff_codes

def define_error_message_search (milestone):
  error_list = [re.compile(r"\*\* Error:.*")]
  return error_list


def define_warning_message_search (milestone):
  warning_list = [re.compile(r"\*\* Warning:.*")]
  return warning_list

def errors_allowed (milestone):
  return False

def warnings_allowed (milestone):
  return milestone in ["skeleton", "prebronze", "bronze"]

def find_rtl_codes ():
  tool_codes = {}
  for c in tool.signoff_codes.codes:
    tool_codes[c] = []
    try:
      tool_codes[c].extend(tool.signoff_codes.codes[c]['questa'])
    except KeyError:
      pass
  return tool_codes
